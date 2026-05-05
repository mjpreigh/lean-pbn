import Lean
import Std.Data.HashMap

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta

set_option autoImplicit false
set_option tactic.hygienic false

inductive Node
  | OR (expr: String) (children : List String) (parents : List String)
  | AND (name: String) (children : List String) (parents : List String) (expression : Expr)

structure Edge where
  parent : String
  child : String

structure ANDORGraph where
  root : String
  edges : List Edge
  nodeMap : HashMap String Node
  andMap : HashMap String String -- map rule exp to name

inductive AndORNodeType
  | ROOT
  | OR

inductive AndOrStructure (V : Type)
  | leaf (v : V)
  | root (v : Expr) (children : List (AndOrStructure V))
  | or   (v : Expr) (children : List (AndOrStructure V))
  | and  (v : V) (children : List (AndOrStructure V))

def toGraph (tree: AndOrStructure LocalDecl) (graph_in : ANDORGraph) (parent_in : List String) : TacticM ANDORGraph := do
  let mut edges := graph_in.edges
  let mut nodeMap := graph_in.nodeMap
  let mut root := graph_in.root
  let mut parent := parent_in
  let mut andMap := graph_in.andMap

  --logInfo m!"top and map: "
  --for (a, b) in andMap do
    --logInfo m!"{a}, {b}"

  match tree with
  | AndOrStructure.root v children => do

    --let mut string_rep ← m!"{v}".toString
    let fmt ← PrettyPrinter.ppExpr v
    let string_rep := fmt.pretty

    let mut node_children : List String := []

    -- add edges to children
    for child in children do

      match child with
      | AndOrStructure.and v c =>
        let child_string := s!"{v.userName}"
        let edge : Edge := { parent := string_rep, child := child_string}
        node_children := child_string :: node_children
        edges := edge :: edges
        let graph_arg : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap}
        let new_graph ← toGraph child graph_arg [string_rep]
        edges := new_graph.edges
        nodeMap := new_graph.nodeMap
        andMap := new_graph.andMap

      | AndOrStructure.leaf v =>
        let child_string := s!"{v.userName}"
        let edge : Edge := { parent := string_rep, child := child_string }
        edges := edge :: edges
        node_children := child_string :: node_children
        let graph_arg : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap}
        let new_graph ← toGraph child graph_arg [string_rep]
        edges := new_graph.edges
        nodeMap := new_graph.nodeMap
        andMap := new_graph.andMap

      | _ => continue

    -- replace node but with more parents if already exists
    let node_maybe := nodeMap.get? string_rep

    match node_maybe with
    | Node.OR e c p => parent := p ++ parent
    | Node.AND e c p x=> parent := p ++ parent
    | _ => parent := parent

    let node := Node.OR string_rep node_children parent
    nodeMap := nodeMap.insert string_rep node
    let ret_graph : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := string_rep, andMap := andMap}
    return ret_graph

  | AndOrStructure.or v children => do
    --let string_rep := s!"{v}"
    let fmt ← PrettyPrinter.ppExpr v
    let string_rep := fmt.pretty
    let mut node_children : List String := []

    -- add edges to children
    for child in children do
      match child with
      | AndOrStructure.and v c =>
        let child_string := s!"{v.userName}"
        let edge : Edge := { parent := string_rep, child := child_string }
        edges := edge :: edges
        node_children := child_string :: node_children
        let graph_arg : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap}
        let new_graph ← toGraph child graph_arg [string_rep]
        edges := new_graph.edges
        nodeMap := new_graph.nodeMap
        andMap := new_graph.andMap

      | AndOrStructure.leaf v =>
        let child_string := s!"{v.userName}"
        let edge : Edge := { parent := string_rep, child := child_string }
        edges := edge :: edges
        node_children := child_string :: node_children
        let graph_arg : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap}
        let new_graph ← toGraph child graph_arg [string_rep]
        edges := new_graph.edges
        nodeMap := new_graph.nodeMap
        andMap := new_graph.andMap

      | _ => continue

    -- replace node but with more parents if already exists
    let node_maybe := nodeMap.get? string_rep

    match node_maybe with
    | Node.OR e c p => parent := p ++ parent
    | Node.AND e c p x => parent := p ++ parent
    | _ => parent := parent

    -- make node
    let node := Node.OR string_rep node_children parent
    nodeMap := nodeMap.insert string_rep node
    let ret_graph : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap }
    return ret_graph

  | AndOrStructure.and v children => do
    -- make node
    let ld ← inferType v.toExpr
    let string_rep := s!"{v.userName}"

    let ldfmt ← PrettyPrinter.ppExpr ld
    let ldString := ldfmt.pretty

    andMap := andMap.insert ldString string_rep

    --logInfo m!"andMap: {m!"{ld}"}, {string_rep}"

    let mut node_children : List String := []
    -- add edges to children
    for child in children do
      match child with
      | AndOrStructure.or v _ =>
        --let child_string := s!"{v}"
        let fmtchild ← PrettyPrinter.ppExpr v
        let child_string := fmtchild.pretty
        let edge : Edge := { parent := string_rep, child := child_string }
        edges := edge :: edges
        node_children := child_string :: node_children
        let graph_arg : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap}
        let new_graph ← toGraph child graph_arg [string_rep]
        edges := new_graph.edges
        nodeMap := new_graph.nodeMap
        andMap := new_graph.andMap

      | _ => continue

    -- replace node but with more parents if already exists
    let node_maybe := nodeMap.get? string_rep

    match node_maybe with
    | Node.OR e c p => parent := p ++ parent
    | Node.AND e c p x => parent := p ++ parent
    | _ => parent := parent


    let node := Node.AND string_rep node_children parent ld
    nodeMap := nodeMap.insert string_rep node
    let ret_graph : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap }
    return ret_graph

  | AndOrStructure.leaf v => do
    -- make node
    let ld ← inferType v.toExpr
    let string_rep := s!"{v.userName}"

    let ldfmt ← PrettyPrinter.ppExpr ld
    let ldString := ldfmt.pretty

    andMap := andMap.insert ldString string_rep
    --logInfo m!"andMap: {m!"{ld}"}, {string_rep}"

    -- replace node but with more parents if already exists
    let node_maybe := nodeMap.get? string_rep

    match node_maybe with
    | Node.OR e c p => parent := p ++ parent
    | Node.AND e c p x => parent := p ++ parent
    | _ => parent := parent


    let node := Node.AND string_rep [] parent ld
    nodeMap := nodeMap.insert string_rep node

    let ret_graph : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap }
    return ret_graph

partial def traverse_graph (graph : ANDORGraph) (node_string : String) (seen_in : List String) : TacticM Unit := do
  if node_string ∈ seen_in then
    return

  let seen := node_string :: seen_in

  let nodeMap := graph.nodeMap

  let node : Option Node := nodeMap.get? node_string

  match node with
  | Node.OR rep children p =>
    logInfo m!"OR: {rep}, children: {children}, parents : {p}"
    for child in children do
      traverse_graph graph child seen
  | Node.AND rep children p x =>
    logInfo m!"AND: {rep}, children: {children}, parents : {p}"
    for child in children do
      traverse_graph graph child seen
  | _ => return


def PrintSubtree (graph: AndOrStructure LocalDecl): TacticM Unit := do
  match graph with
  | AndOrStructure.root v children => do
    logInfo m!"root expr: {v}"
    for child in children do
      PrintSubtree child
  | AndOrStructure.or v children => do
    logInfo m!"Or: {v}"
    for child in children do
      PrintSubtree child
  | AndOrStructure.and v children => do
    let name := v.userName
    let type ← inferType v.toExpr
    logInfo m!"And: {name} : {type}"
    for child in children do
      PrintSubtree child
  | AndOrStructure.leaf v => do
    let name := v.userName
    let type ← inferType v.toExpr
    logInfo m!"Leaf: {name} : {type}"

def getArgs (e : Expr) (andMap : HashMap String String) : MetaM (List String) := do
  let mut exp := e
  let mut args := []
  while true do
    exp ← whnf exp
    match exp with
    | Expr.forallE _ first body _ =>
        let fmt ← PrettyPrinter.ppExpr first
        let string_rep := fmt.pretty
        let possibleRule := andMap.contains string_rep
        if possibleRule then
          let a := andMap.get! string_rep
          args := [a] ++ args
        else
          args := [string_rep] ++ args
        exp := body
    | _ => break
  return args

def getArgsRaw (e : Expr) : MetaM (List String) := do
  let mut exp := e
  let mut args := []
  while true do
    exp ← whnf exp
    match exp with
    | Expr.forallE _ first body _ =>
        let fmt ← PrettyPrinter.ppExpr first
        let string_rep := fmt.pretty
        args := [string_rep] ++ args
        exp := body
    | _ => break
  return args

def dropLeftMost (e : Expr) : MetaM Expr := do
  let e ← whnf e
  match e with
  | Expr.forallE _ _ body _ => return body
  | _ => return e

  def getFirstArg (e : Expr) : MetaM (List Expr) := do
  match e with
  | Expr.forallE _ first _ _ => return [first]
  | _ => return []

-- for some goal, find rules that could provide it
partial def buildAndOrTree (lctx : LocalContext) (goal: Expr) (nodeType: AndORNodeType) (seen_in : List String) : MetaM (AndOrStructure LocalDecl):= do

  let fmt ← PrettyPrinter.ppExpr goal
  let string_rep := fmt.pretty

  if string_rep ∈ seen_in then
    return AndOrStructure.or goal []

  let mut seen := string_rep :: seen_in

  let mut rules: List (AndOrStructure LocalDecl) := []
  for ldecl in lctx do
    let mut args: List Expr := []
  -- iterate over hypotheses
    unless ldecl.isImplementationDetail do
      let mut last : Option Expr := none
      let mut curr := ← inferType ldecl.toExpr

      -- peel back layer by layer
       -- if layer is the same as goal, add as rule to get goal
        --while !curr == mkSort 0 && (last.isNone || !(← isDefEq last.get! curr)) do
      if (← isDefEq curr goal) then
          rules := rules ++ [AndOrStructure.leaf ldecl ]
          continue
      while true do
        if curr == mkSort 0 then
          break

        let mut iterate : Bool ←
          (match last with
          | some l => do
              let eq ← isDefEq l curr
              pure (¬ eq)
          | none => pure true)

        if !iterate then
          break

        if (← isDefEq curr goal) then
          let mut arg_nodes := []
          for arg in args do

            -- each arg will be an or subtree
            let a ← buildAndOrTree lctx arg AndORNodeType.OR seen
            arg_nodes := a :: arg_nodes
          rules := rules ++ [AndOrStructure.and ldecl arg_nodes]

        -- else strip a layer
        last := some curr
        let arg ← getFirstArg curr
        args := arg ++ args
        curr ← dropLeftMost curr
  match nodeType with
  | AndORNodeType.ROOT =>
      let graph : AndOrStructure LocalDecl :=  AndOrStructure.root goal rules
      return graph
  | AndORNodeType.OR =>
      let graph : AndOrStructure LocalDecl :=  AndOrStructure.or goal rules
      return graph

def getNodeExpr (node : AndOrStructure LocalDecl) : MetaM Expr := do
  match node with
  | AndOrStructure.root v children => return v
  | AndOrStructure.or v children => return v
  | AndOrStructure.and v children => return v.toExpr
  | AndOrStructure.leaf v => return v.toExpr

def navTopDown (node : AndOrStructure LocalDecl) : TacticM Unit := do
  match node with
  | AndOrStructure.root v children =>
    -- present "apply" for each rule
    for rule in children do
      let r ← getNodeExpr rule
      logInfo m!"apply {r}"
  | AndOrStructure.or v children => return
  | AndOrStructure.and v children => return
  | AndOrStructure.leaf v => return

  def navAllPossibilities (node : AndOrStructure LocalDecl) : TacticM Unit := do
  match node with

  | AndOrStructure.root v children =>
    -- present "apply" for each rule
    for rule in children do
      let r ← getNodeExpr rule
      logInfo m!"apply {r}"
    for rule in children do
      navAllPossibilities rule

  | AndOrStructure.or v children =>
    for rule in children do
      navAllPossibilities rule

  | AndOrStructure.and v children =>
    let mut args := m!""
    if children.length > 0 then
      for or in children do
        let o ← getNodeExpr or
        args := args ++ m!" {o}"
      logInfo m!"have _ := {v.userName}{args}"

    for or in children do
      navAllPossibilities or

  | AndOrStructure.leaf v => return

def printAndOr : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    let mainTarget ← getMainTarget
    let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []

    let emptyGraph : ANDORGraph := { edges := [], nodeMap := {}, root := "", andMap := {}}
    let graph ← toGraph tree emptyGraph []

    traverse_graph graph graph.root []

elab "printANDOR" : tactic => do
   printAndOr

-- for now get offered all possible applications
def Navigate : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    let mainTarget ← getMainTarget
    let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []
    navTopDown tree
    --navAllPossibilities tree

elab "navigate" : tactic => do
  Navigate

def remove_goals (false_set : List String) (graph_in : ANDORGraph) : TacticM ANDORGraph := do
  let mut edges := []
  let mut nodeMap := graph_in.nodeMap
  let root := graph_in.root
  let mut andMap := graph_in.andMap

  for f in false_set do
    -- get the goal node
    let node := nodeMap.get? f
    match node with
    | Node.OR s c p =>
      -- remove the goal node
      nodeMap := nodeMap.erase f
      -- remove any edges including the goal node
      -- remove any parents of the goal node
      for parent in p do

        -- remove all other children
        let rule := nodeMap.get? parent
        match rule with
        | Node.AND s c p x =>
          for child in c do
            nodeMap := nodeMap.erase child
        | _ => continue
        -- remove as a child of goals?
        -- remove from andMap
        nodeMap := nodeMap.erase parent
        -- remove from nodeMap
        andMap := andMap.erase parent

      -- remove the goal node as a parent of any children
    | _ => continue


  let graph_out : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap}
  return graph_out


def NavBottomUp : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    let mainTarget ← getMainTarget
    let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []
    let emptyGraph : ANDORGraph := { edges := [], nodeMap := {}, root := "", andMap := {}}
    let graph ← toGraph tree emptyGraph []

    -- rule map : rule (string version) -> are all args axiomotized?
    let mut ruleMap : HashMap String Bool := {}
    let mut argMap : HashMap String Bool := {}
    -- for all nodes
    for (str, node) in graph.nodeMap do
      match node with
      | Node.AND s c p x =>
        -- if it is a leaf
        if List.length c == 0 then

          -- if it is AND, record which goal is true and which rule that goal is a child of
          for goal in p do
            argMap := argMap.insert goal true
            let goalnode := graph.nodeMap.get? goal
            match goalnode with
            | Node.OR s2 c2 p2 =>
              for rule in p2 do
                -- if rule in rule map, do nothing
                -- if rule not in rule map, add rule -> true
                if !ruleMap.contains rule then
                  ruleMap := ruleMap.insert rule true
            | _ => let x := 1

      | Node.OR s c p =>
        -- if it is a leaf
        if List.length c == 0 then
          -- if it is an OR, record which goal is not true and which rule it is a child of
          argMap := argMap.insert s false
          for rule in p do
            -- add rule -> false to rule map no matter what
            ruleMap := ruleMap.insert rule false

    -- for rule in rule map, if true, offer to "have". If false offer "provide" for all non-axiomotized arguments
    for (rule, b) in ruleMap do
      let ruleNode := graph.nodeMap.get? rule
      match ruleNode with
      | Node.AND s c p x =>
        --logInfo m!"getargs and map: "
       -- for (a, b) in graph.andMap do
         -- logInfo m!"{a}, {b}"

        match b with
        | true =>
          let mut args ← getArgs x graph.andMap
          args := List.reverse args
          let argString := String.intercalate " " args
          logInfo m!"have _ := {s} {argString}"
        | false =>
          let mut args ← getArgsRaw x
          for arg in args do
          let arg_status := argMap.get? arg
          match arg_status with
          | true => continue
          | false => logInfo m!"provide {arg}"
          | _ => continue--logInfo m!"provide {arg}"
      | _ => continue

elab "navbottomup" : tactic => do
  NavBottomUp

def navHave : TacticM Unit := do
  sorry

elab "navHave" : tactic => do
  navHave



theorem a_proof_of_negation (a : Prop) :
    a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

theorem a_proof_of_negation2 (a : Prop) :
    a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    sorry
    --navigate

  theorem test (a b c d m : Prop) (f : a → b) (h : c → d) (i : b → d) (j: m → d) (k : a → b → c) (M : b → a) (bb : b):
    (b → c) :=
  by
    --navigate
    --printANDOR
    sorry

  def test2 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (m : Prop) (f : Int → String) (f2 : Int → String)  (g : a → Int) (h : c → d) (i : b → d) (j: m → d) (k : a → b → c) (bb : b):
    (a → String) :=
  by
    intro ha
    apply f
    --have x := i ?bbbb
    sorry
    --navigate

  theorem testingg (c d e : Prop) (g : d → e → c) (hd : d) (he : e) :
    c :=
  by
    have x := g hd he
    --navigate
    sorry

  theorem testinggg (a b c d e : Prop) (g : a → b → d → e → c) (hd : d) (he : e) :
    e → c :=
  by
    --navigate
    sorry

  theorem testingggg (a b c : Prop) (ab : a → b) (bc : b → c):
    a → c :=
  by
    intro ha
    --have x := ab ha
    --navigate
    sorry

def testinggggg (a b c d f : Prop) (hb : b) (hc : c) (bca : b → c → a) (cda : c → d → a):
    a :=
  by
    navigate

    --have ha := bca hb hc
    printANDOR
    navbottomup
    --have x := bca hb
    sorry

  theorem testd (a b c d m : Prop) (f : a → b) (k : a → b → c) :
    c :=
  by
    --navigate
    --printANDOR
    --navbottomup
    sorry

theorem testt (a b c d e x y z : Prop) (f : b → c → a) (g : c → d → a) (h : e → x → z → b) (i : z → y → b)
-- (he : e) (hx : x) (hy : y) (hz : z)
:
    a :=
  by
    --navigate
    have hx: x := sorry
    have h' he hz := h he hx hz



    have he: e := sorry
    have h' := h he

    all_goals have hb: b := ?b
    all_goals have hx: x := sorry
    all_goals have hz: z := sorry
    case b => grind

      -- apply h <;> trivial




    printANDOR
    navbottomup
    sorry

theorem testtt (a b c d e x y z : Prop) (f : b → c → a) (g : c → d → a) (h : e → x → z → b) (i : z → y → b) (he : e):
    a :=
  by

    navigate
    printANDOR
    navbottomup
    sorry


-- "super have"
  -- new goal
  -- residual context/residual graph
  -- throughout all contexts

-- next- essential things, order
