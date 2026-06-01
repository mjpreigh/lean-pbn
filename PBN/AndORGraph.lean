-- Build and traverse AND-OR graphs
import Lean
import Std.Data.HashMap

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta

set_option autoImplicit false
set_option tactic.hygienic false

inductive Node
  | OR (expr: String) (children : List String) (parents : List String) (fvar : Option FVarId)
  | AND (expr : String) (children : List String) (parent : String) (fvar : FVarId) (name: String)

structure Edge where
  parent : String
  child : String

structure ANDORGraph where
  root : String
  -- two maps because same expr can go with an and + an or node
  andNodeMap : HashMap String Node
  orNodeMap : HashMap String Node

def getNodeExprString (node : Node) : MetaM String := do
  match node with
  | Node.AND e _ _ _ _ => return e
  | Node.OR e _ _ _ => return e

def getNodeChildren (graph : ANDORGraph) (node_str : String) (is_and_node : Bool) : MetaM (List String) := do
  let mut node := graph.andNodeMap[node_str]?
  if !is_and_node then
    node := graph.orNodeMap[node_str]?
  match node with
  | none => throwError "Node not in graph (1)."
  | some n =>
    match n with
    | Node.OR _ c _ _ => return c
    | Node.AND _ c _ _ _ => return c

def getNodeParents (graph : ANDORGraph) (node_str : String) (is_and_node : Bool) : MetaM (List String) := do
  let mut node := graph.andNodeMap[node_str]?
  if !is_and_node then
    node := graph.orNodeMap[node_str]?
  match node with
  | none => throwError "Node not in graph (2)."
  | some n =>
    match n with
    | Node.OR _ _ p _ => return p
    | Node.AND _ _ p _ _ => return [p]

def getNodeFvarid (graph : ANDORGraph) (node_str : String) (is_and_node : Bool) : MetaM FVarId := do
  let mut node := graph.andNodeMap[node_str]?
  if !is_and_node then
    node := graph.orNodeMap[node_str]?
  match node with
  | none => throwError "Node not in graph (3)."
  | some n =>
    match n with
    | Node.OR _ _ _ f =>
      match f with
      | none => throwError "Fvarid does not exist."
      | some fv => return fv
    | Node.AND _ _ _ f _ => return f

def insertEdge (graph : ANDORGraph) : MetaM ANDORGraph := do
  -- make sure both ends of the edge actually refers to nodes in graph
  let new_graph : ANDORGraph := {root := graph.root, andNodeMap := graph.andNodeMap, orNodeMap := graph.orNodeMap}
  return new_graph

def insertNode (graph : ANDORGraph) (node : Node) : MetaM ANDORGraph := do
  let mut andNodeMap := graph.andNodeMap
  let mut orNodeMap := graph.orNodeMap
  match node with
  | Node.AND e _ _ _ _  =>
    andNodeMap := andNodeMap.insert e node
  | Node.OR e _ _ _ => orNodeMap := orNodeMap.insert e node
  let new_graph : ANDORGraph := {root := graph.root, andNodeMap := andNodeMap, orNodeMap := orNodeMap}
  return new_graph

def exprToString (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

-- pretty print type of MVar with given MVarId
def mvaridToString (m : MVarId) : MetaM String := do
  return (← exprToString (← m.getType))

-- all rules a hypothesis could possibly represent
partial def getAllRules (e : Expr) (args_so_far : List String) (rules_so_far : HashMap String (List String)) : MetaM (HashMap String (List String)) := do
  let exp ← whnf e
  match exp with
  | Expr.forallE _ first body _ =>
    let new_args :=  args_so_far ++ [(← exprToString first)]
    let new_result ← exprToString body
    let new_rules := rules_so_far.insert new_result new_args
    return (← getAllRules body new_args new_rules)
  | _ => return rules_so_far

-- map each hypothesis to all new things it could produce and a list of args needed to produce that thing
-- do this before building the AND-OR graph to save time repeatedly iterating over hypotheses and their parts
def preprocessArgs : TacticM ((HashMap String ((FVarId × String) × HashMap String (List String))) × (HashMap String FVarId)) := do
  let mut args_map := {}
  let mut fvar_map := {}
  let lctx ← getLCtx
  for ldecl in lctx do
    unless ldecl.isImplementationDetail do
      fvar_map := fvar_map.insert (← exprToString ldecl.toExpr) ldecl.fvarId
      if !(← isProp ldecl.toExpr) then
        let lexpr := ldecl.type
        let mut first_possible_results : HashMap String (List String) := {}
        first_possible_results := first_possible_results.insert (← exprToString lexpr) []
        let possible_results ← getAllRules lexpr [] first_possible_results
        args_map := args_map.insert (← exprToString lexpr) ((ldecl.fvarId, toString ldecl.userName), possible_results)
  return (args_map, fvar_map)

def addParentAndToOr (graph : ANDORGraph) (node_or : String) (parent_and : String) : MetaM ANDORGraph := do
  -- replace the node in graph nodemap with a new one where parent is in the parents list
  let old_node := graph.orNodeMap[node_or]?
  match old_node with
  | some n =>
    match n with
    | Node.AND _ _ _ _ _ =>
      throwError "AND node can only have one parent."
      --let new_node := Node.AND e c (parent_and :: p) f n
      -- overwrite old node
      --return (← insertNode graph new_node)
    | Node.OR e c p f =>
      let new_node := Node.OR e c (parent_and :: p) f
      -- overwrite old node
      return (← insertNode graph new_node)
  | none => throwError "Node not in graph (4)."

partial def constructGraphHelper (working_graph : ANDORGraph) (curr_goal : String) (curr_goal_fvarid : Option FVarId) (all_possible_rules : HashMap String ((FVarId × String) × (HashMap String (List String)))) (local_fvars : HashMap String FVarId) : MetaM ANDORGraph := do
  -- curr_goal is not added yet: figure out its children (and nodes)
  -- add children of its and-node children along the way
  let mut graph := working_graph
  let mut curr_goal_children := []
  -- avoid infinite recursion if there is a cycle
  let curr_goal_node_placeholder := Node.OR curr_goal [] [] none
  graph ← insertNode graph curr_goal_node_placeholder
  -- if a hypothesis can produce the type of curr_goal, add as a rule, add edge, and visit arguments
  for (hyp, expr_rules) in all_possible_rules do
    let hyp_fvar := expr_rules.1.1
    let hyp_name := expr_rules.1.2
    let rules := expr_rules.2

    if rules.contains curr_goal then
      let args := rules[curr_goal]!
      curr_goal_children := hyp :: curr_goal_children
      -- add a rule node for this hypothesis
      let new_and := Node.AND hyp args curr_goal hyp_fvar hyp_name
      graph ← insertNode graph new_and
      -- if they don't already exist, add a node for each argument and get subgraph
      for child in args do
        if !graph.orNodeMap.contains child then
          -- add new node by calling constructGraphHelper
          -- if there is already a local decl that matches this, use that fvarid
          --let child_fvarid := local_fvars[child]?
          graph ← constructGraphHelper graph child none all_possible_rules local_fvars
        -- add hyp as a parent to the child
        graph ← addParentAndToOr graph child hyp
  -- add curr_goal to graph
  let curr_goal_node := Node.OR curr_goal curr_goal_children [] curr_goal_fvarid
  graph ← insertNode graph curr_goal_node
  return graph

def constructGraph (goal : MVarId) : TacticM ANDORGraph := do
  let root ← mvaridToString goal
  let ret ← goal.withContext do
    let preprocess ← preprocessArgs
    let all_possible_rules := preprocess.1
    let local_fvars := preprocess.2
    let empty_graph : ANDORGraph := { root := root, orNodeMap := {}, andNodeMap := {}}
    return (← constructGraphHelper empty_graph root (some (← goal.getType).fvarId!) all_possible_rules local_fvars)
  return ret

partial def printAndOrGraph (graph : ANDORGraph) (curr_node_str : String) (seen_and_nodes : List String) (seen_or_nodes : List String) (curr_or : Bool) : MetaM Unit := do
  let mut curr_node := graph.orNodeMap[curr_node_str]?
  if !curr_or then
    curr_node := graph.andNodeMap[curr_node_str]?
  match curr_node with
  | some n =>
    match n with
    | Node.AND e c p _ n =>
      logInfo m!"AND {n} : {e}, children : {c}, parent : {p}"
      for child in c do
        if !seen_or_nodes.contains child then
          printAndOrGraph graph child seen_and_nodes (child :: seen_or_nodes) true
    | Node.OR e c p _ =>
      logInfo m!"OR {e}, children : {c}, parents : {p}"
      for child in c do
        if !seen_and_nodes.contains child then
          printAndOrGraph graph child (child :: seen_and_nodes) seen_or_nodes false
  | none => throwError "Node does not exist. (a)"

elab "printAndOrGraph" : tactic => do
  -- root is main goal of the context
  let graph ← constructGraph (← getMainGoal)
  printAndOrGraph graph graph.root [] [graph.root] true

-- or node is proven if it has a child and node with no children
def isOrProven (graph : ANDORGraph) (or_str : String) : MetaM (List FVarId) := do
  let or_children ← getNodeChildren graph or_str false
  let mut fvar : List FVarId := []
  for rule in or_children do
    -- if any rule has no children, return true
    if (← getNodeChildren graph rule true).length == 0 then
      fvar := [(← getNodeFvarid graph rule true)]
      break
  return fvar

-- if all the OR children of this AND are proven, add to map and visit all of its AND grandparents
-- also add rule with no args as child of its parent if it is satisfied
-- keep track of the mvarids that these new rules should have
partial def findNewAppsTraverse (graph : ANDORGraph) (curr_and_node : String) (curr_mvarid : MVarId) : TacticM (MVarId × ANDORGraph) := do
  let mut all_args_proven := false
  let args ← getNodeChildren graph curr_and_node true
  -- refer to the AND nodes that provide these ORs
  let mut arg_exprs : List Expr := []
  for arg in args do
    let fv ← isOrProven graph arg
    if fv.length == 1 then
      arg_exprs := arg_exprs ++ [(mkFVar fv[0]!)]
      all_args_proven := true
    else
      all_args_proven := false
      break
  if !all_args_proven then
    return (curr_mvarid, graph)
  let curr_fv ← getNodeFvarid graph curr_and_node true
  let rule_parent := (← getNodeParents graph curr_and_node true)[0]!
  if (← isOrProven graph rule_parent).length > 0 then
    return (curr_mvarid, graph)
  let proof := mkAppN (mkFVar curr_fv) (arg_exprs.toArray)
  let type ← inferType proof
  let name ← mkFreshUserName `h
  let mut new_mvarid ← curr_mvarid.assert name type proof
  let (_, new_mvarid') ← new_mvarid.intro name
  let mut new_graph ← constructGraph new_mvarid'
  new_mvarid := new_mvarid'
  -- visit every grandparent rule to see if more stuff is provable
  let grandparent_rules ← getNodeParents new_graph rule_parent false
  for rule in grandparent_rules do
    (new_mvarid, new_graph) ← findNewAppsTraverse new_graph rule new_mvarid
  return (new_mvarid, new_graph)

-- what rule applications can we satifsy now given an additional hypothesis?
def findNewApps (graph : ANDORGraph) (new_hyp : Expr) (curr_mvarid : MVarId) : TacticM MVarId := do
  -- if there is an or node with same type as new_hyp, make that or the parent
  let type_string ← exprToString new_hyp
  let or_parent := graph.orNodeMap[type_string]?
  match or_parent with
  | none =>
    -- don't go futher, this is not relevant in the graph
    return curr_mvarid
  | some parent_node =>
    let grandparent_rules ← getNodeParents graph (← getNodeExprString parent_node) false
    let mut new_mvarid := curr_mvarid
    let mut new_graph := graph
    -- traverse new graph up from new_and_node and see if any rule applications have all arguments satisfied
    for rule in grandparent_rules do
      (new_mvarid, new_graph) ← findNewAppsTraverse new_graph rule new_mvarid
    return new_mvarid

partial def reachableFrom (graph : ANDORGraph) (node_string : String) (and : Bool) (and_reached_so_far : List String) (or_reached_so_far : List String) (up : Bool) : MetaM ((List String) × (List String)) := do
  let mut node := graph.andNodeMap[node_string]?
  if !and then
    node := graph.orNodeMap[node_string]?
  let mut ands := and_reached_so_far
  let mut ors := or_reached_so_far
  match node with
  | none => return ([], [])--throwError "Node does not exist. (b)"
  | some n =>
    match n with
    | Node.AND e c p _ _ =>
      -- add this to and reached so far
      ands := ands ++ [e]
      if up then
        -- traverse up
        if !ors.contains p then
          (ands, ors) ← reachableFrom graph p false ands ors up
        for child in c do
          if !ors.contains child then
            ors := ors ++ [child]
      else
        -- traverse down
        for child in c do
          if !ors.contains child then
            (ands, ors) ← reachableFrom graph child false ands ors up
    | Node.OR e c p _ =>
      -- add this to ors reached so far
      ors := ors ++ [e]
      if up then
        -- traverse up
        for parent in p do
          if !ands.contains parent then
            (ands, ors) ← reachableFrom graph parent true ands ors up
      else
        -- traverse down
        for child in c do
          if !ands.contains child then
            (ands, ors) ← reachableFrom graph child true ands ors up
  return (ands, ors)

-- start from the new hypothesis
def deleteNotReachableFrom (graph : ANDORGraph) (node_expr : Expr) (curr_mvar : MVarId) : TacticM MVarId := do
  let mut (reachable_ands, reachable_ors) ← reachableFrom graph (← exprToString node_expr) true [] [] true
  let (reachable_ands2, reachable_ors2) ← reachableFrom graph (← exprToString node_expr) true [] [] false
  reachable_ands := reachable_ands ++ reachable_ands2
  reachable_ors := reachable_ors ++ reachable_ors2
  -- now figure out what is NOT reachable
  let mut not_reachable_ands : List String := []
  for (a, _) in graph.andNodeMap do
    if !reachable_ands.contains a then
      not_reachable_ands := a :: not_reachable_ands
  let mut not_reachable_ors : List String := []
  for (o, _) in graph.orNodeMap do
    if !reachable_ors.contains o then
      not_reachable_ors := o :: not_reachable_ors
  -- delete all not reachable ands from context
  let mut new_mvar := curr_mvar
  let mut new_graph := graph
  for a in not_reachable_ands do
    new_graph ← constructGraph new_mvar
    let fvar ← getNodeFvarid new_graph a true
    new_mvar ← new_mvar.tryClear fvar
  -- delete props that match not reachable ors from context. How to recognize this?
  return new_mvar
