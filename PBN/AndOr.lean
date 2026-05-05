-- infrastructure to build and manipulate AND-OR structures (trees and graphs)

import Lean
import Std.Data.HashMap

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta

set_option autoImplicit false
set_option tactic.hygienic false

inductive Node
  | OR (expr: String) (children : List String) (parents : List String)
  | AND (name: String) (children : List String) (parents : List String) (expression : Expr) (fvar : FVarId)

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

  match tree with
  | AndOrStructure.root v children => do

    --let mut string_rep ← m!"{v}".toString
    let fmt ← PrettyPrinter.ppExpr v
    let string_rep := fmt.pretty

    let mut node_children : List String := []

    -- add edges to children
    for child in children do

      match child with
      | AndOrStructure.and v _ =>
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
    | Node.OR _ _ p => parent := p ++ parent
    | Node.AND _ _ p _ _ => parent := p ++ parent
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
      | AndOrStructure.and v _ =>
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
    | Node.OR _ _ p => parent := p ++ parent
    | Node.AND _ _ p _ _ => parent := p ++ parent
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
    let fvar := v.fvarId

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
    | Node.OR _ _ p => parent := p ++ parent
    | Node.AND _ _ p _ _ => parent := p ++ parent
    | _ => parent := parent


    let node := Node.AND string_rep node_children parent ld fvar
    nodeMap := nodeMap.insert string_rep node
    let ret_graph : ANDORGraph := { edges := edges, nodeMap := nodeMap, root := root, andMap := andMap }
    return ret_graph

  | AndOrStructure.leaf v => do
    -- make node
    let ld ← inferType v.toExpr
    let string_rep := s!"{v.userName}"
    let fvar := v.fvarId

    let ldfmt ← PrettyPrinter.ppExpr ld
    let ldString := ldfmt.pretty

    andMap := andMap.insert ldString string_rep
    --logInfo m!"andMap: {m!"{ld}"}, {string_rep}"

    -- replace node but with more parents if already exists
    let node_maybe := nodeMap.get? string_rep

    match node_maybe with
    | Node.OR _ _ p => parent := p ++ parent
    | Node.AND _ _ p _ _ => parent := p ++ parent
    | _ => parent := parent


    let node := Node.AND string_rep [] parent ld fvar
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
  | Node.AND rep children p _ _ =>
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
  | AndOrStructure.root v _ => return v
  | AndOrStructure.or v _ => return v
  | AndOrStructure.and v _ => return v.toExpr
  | AndOrStructure.leaf v => return v.toExpr

def remove_goals (false_set : List String) (graph_in : ANDORGraph) : TacticM ANDORGraph := do
  let mut edges := []
  let mut nodeMap := graph_in.nodeMap
  let root := graph_in.root
  let mut andMap := graph_in.andMap

  for f in false_set do
    -- get the goal node
    let node := nodeMap.get? f
    match node with
    | Node.OR _ _ p =>
      -- remove the goal node
      nodeMap := nodeMap.erase f
      -- remove any edges including the goal node
      -- remove any parents of the goal node
      for parent in p do

        -- remove all other children
        let rule := nodeMap.get? parent
        match rule with
        | Node.AND _ c _ _ _ =>
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

-- returns list of hypotheses to delete below the given top_node
partial def pruneDescendants (graph : ANDORGraph) (top_node : String) (ax : String) (seen_in : List String) : MetaM (List FVarId) := do
  logInfo m!"ax : {ax}"
  let nodeMap := graph.nodeMap
  let node := nodeMap.get? top_node
  let mut seen := seen_in
  let mut delete : List FVarId := []

  match node with

  | Node.OR e c _ =>
    seen := e :: seen
    -- visit children
    for child in c do
      let delete_intermediate ← pruneDescendants graph child ax seen
      delete := delete ++ delete_intermediate
    return delete

  | Node.AND n c p _ f =>
    seen := n :: seen

    -- unless node has a parent that is not in seen (or it is ax), add to delete
    let mut to_delete := true
    for parent in p do
      if !seen.contains parent then
        to_delete := false
        break
    if to_delete && !(n == ax) then
      delete := f :: delete

    -- visit children
    for child in c do
      let delete_intermediate ← pruneDescendants graph child ax seen
      delete := delete ++ delete_intermediate
    return delete

  | none => return []

-- returns list of hypotheses to delete based on what having top_node makes provable
def pruneProven (graph : ANDORGraph) (top_node : String) (ax : String) (seen_in : List String) : MetaM (List FVarId) := do
  return []

partial def pruneDescendantsAndProven (graph : ANDORGraph) (top_node : String) (ax : String) (seen_in : List String) : MetaM (List FVarId) := do
  let l1 ← pruneDescendants graph top_node ax seen_in
  let l2 ← pruneProven graph top_node ax seen_in
  let ret := l1 ++ l2
  return ret
