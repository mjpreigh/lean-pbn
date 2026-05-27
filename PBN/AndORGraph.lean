-- Build and traverse AND-OR graphs
import Lean
import Std.Data.HashMap

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta

inductive Node
  | OR (expr: String) (children : List String) (parents : List String) (fvar : Option FVarId)
  | AND (expr : String) (children : List String) (parents : List String) (fvar : FVarId) (name: String)

structure Edge where
  parent : String
  child : String

structure ANDORGraph where
  root : String
  edges : List Edge
  nodeMap : HashMap String Node

def insertEdge (graph : ANDORGraph) (edge : Edge) : MetaM ANDORGraph := do
  -- make sure both ends of the edge actually refers to nodes in graph
  --\if !(graph.nodeMap.contains edge.parent) || !(graph.nodeMap.contains edge.child) then
    --throwError "Both ends of edge must be in graph."
  let mut edges := graph.edges
  edges := edge :: edges
  let new_graph : ANDORGraph := {root := graph.root, edges := edges, nodeMap := graph.nodeMap}
  return new_graph

def insertNode (graph : ANDORGraph) (node : Node) : MetaM ANDORGraph := do
  let mut nodeMap := graph.nodeMap
  nodeMap ← match node with
  | Node.AND e _ _ _ _  => pure (nodeMap.insert e node)
  | Node.OR e _ _ _ => pure (nodeMap.insert e node)
  let new_graph : ANDORGraph := {root := graph.root, edges := graph.edges, nodeMap := nodeMap}
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
    let new_args := (← exprToString first) :: args_so_far
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
        let possible_results ← getAllRules lexpr [] {}
        args_map := args_map.insert (← exprToString lexpr) ((ldecl.fvarId, toString ldecl.userName), possible_results)
  return (args_map, fvar_map)

def addParent (graph : ANDORGraph) (node : String) (parent : String) : MetaM ANDORGraph := do
  -- replace the node in graph nodemap with a new one where parent is in the parents list
  let old_node := graph.nodeMap[node]?
  match old_node with
  | some n =>
    match n with
    | Node.AND e c p f n =>
      let new_node := Node.AND e c (parent :: p) f n
      -- overwrite old node
      return (← insertNode graph new_node)
    | Node.OR e c p f =>
      let new_node := Node.OR e c (parent :: p) f
      -- overwrite old node
      return (← insertNode graph new_node)
  | none => throwError "Node not in graph."

partial def constructGraphHelper (working_graph : ANDORGraph) (curr_goal : String) (curr_goal_fvarid : Option FVarId) (all_possible_rules : HashMap String ((FVarId × String) × (HashMap String (List String)))) (local_fvars : HashMap String FVarId) : MetaM ANDORGraph := do
  -- curr_goal is not added yet: figure out its children (and nodes), then add it and any edges including it
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
      let new_and := Node.AND hyp args [curr_goal] hyp_fvar hyp_name
      graph ← insertNode graph new_and
      -- add an edge from curr_goal to the rule
      let edge_to_rule : Edge := {parent := curr_goal, child := hyp}
      graph ← insertEdge graph edge_to_rule
      -- if they don't already exist, add a node for each argument and get subgraph
      -- add an edge to each argument
      for child in args do
        if !graph.nodeMap.contains child then
          -- add new node by calling constructGraphHelper
          -- if there is already a local decl that matches this, use that fvarid
          let child_fvarid := local_fvars[child]?
          graph ← constructGraphHelper graph child none all_possible_rules local_fvars

        -- add hyp as a parent to the child
        graph ← addParent graph child hyp
        -- add edge from hyp to child
        let edge_to_child : Edge := {parent := hyp, child := child}
        graph ← insertEdge graph edge_to_child

  -- add curr_goal to graph
  let curr_goal_node := Node.OR curr_goal curr_goal_children [] curr_goal_fvarid
  graph ← insertNode graph curr_goal_node

  return graph

def constructGraph : TacticM ANDORGraph := do
  -- root is main goal of the context
  let goal ← getMainGoal
  let root ← mvaridToString goal
  let preprocess ← preprocessArgs
  let all_possible_rules := preprocess.1
  let local_fvars := preprocess.2
  let mut nodeMap := {}
  let empty_graph : ANDORGraph := { root := root, edges := [], nodeMap}
  return (← constructGraphHelper empty_graph root (some (← goal.getType).fvarId!) all_possible_rules local_fvars)

partial def printAndOrGraph (graph : ANDORGraph) (curr_node_str : String) (seen_nodes : List String) : MetaM Unit := do
  let curr_node := graph.nodeMap[curr_node_str]?
  match curr_node with
  | some n =>
    match n with
    | Node.AND e c p f n =>
      logInfo m!"AND {n} : {e}, children : {c}, parents : {p}"
      for child in c do
        if !seen_nodes.contains child then
          printAndOrGraph graph child (child :: seen_nodes)
    | Node.OR e c p f =>
      logInfo m!"OR {e}, children : {c}, parents : {p}"
      for child in c do
        if !seen_nodes.contains child then
          printAndOrGraph graph child (child :: seen_nodes)
  | none => throwError "Node does not exist."

elab "printAndOrGraph" : tactic => do
  let graph ← constructGraph
  printAndOrGraph graph graph.root [graph.root]
