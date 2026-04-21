import Lean

open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta

set_option autoImplicit false
set_option tactic.hygienic false

inductive AndORNodeType
  | ROOT
  | OR

inductive AndOrStructure (V : Type)
  | leaf (v : V)
  | root (v : Expr) (children : List (AndOrStructure V))
  | or   (v : Expr) (children : List (AndOrStructure V))
  | and  (v : V) (children : List (AndOrStructure V))

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

def dropOne (e : Expr) : MetaM Expr := do
  let e ← whnf e
  match e with
  | Expr.forallE _ _ body _ => return body
  | _ => return e

def getArgs (e : Expr) : MetaM (List Expr) := do
  let mut exp := e
  let mut args := []
  while true do
    exp ← whnf exp
    match e with
    | Expr.forallE _ first body _ =>
        args := [first] ++ args
        exp := body
    | _ => break
  return args

  def getFirstArg (e : Expr) : MetaM (List Expr) := do
  match e with
  | Expr.forallE _ first _ _ => return [first]
  | _ => return []

-- for some goal, find rules that could provide it
partial def buildAndOr (lctx : LocalContext) (goal: Expr) (nodeType: AndORNodeType) : TacticM (AndOrStructure LocalDecl):= do

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
            let a ← buildAndOr lctx arg AndORNodeType.OR
            arg_nodes := a :: arg_nodes
          rules := rules ++ [AndOrStructure.and ldecl arg_nodes]

        -- else strip a layer
        last := some curr
        let arg ← getFirstArg curr
        args := arg ++ args
        curr ← dropOne curr
  match nodeType with
  | AndORNodeType.ROOT =>
      let graph : AndOrStructure LocalDecl :=  AndOrStructure.root goal rules
      return graph
  | AndORNodeType.OR =>
      let graph : AndOrStructure LocalDecl :=  AndOrStructure.or goal rules
      return graph

def treeToGraph (tree : AndOrStructure LocalDecl) : TacticM (AndOrStructure LocalDecl) := do
  sorry

-- prune branches of the tree that end in an unproven goal
def prune (tree : AndOrStructure LocalDecl) : TacticM (AndOrStructure LocalDecl) := do
  sorry

def getNodeExpr (node : AndOrStructure LocalDecl) : MetaM Expr := do
  match node with
  | AndOrStructure.root v children => return v
  | AndOrStructure.or v children => return v
  | AndOrStructure.and v children => return v.toExpr
  | AndOrStructure.leaf v => return v.toExpr

def navSubtree (node : AndOrStructure LocalDecl) : TacticM Unit := do
  match node with
  | AndOrStructure.root v children =>
    -- present "apply" for each rule
    for rule in children do
      let r ← getNodeExpr rule
      logInfo m!"apply {r}"
    for rule in children do
      navSubtree rule
  | AndOrStructure.or v children => return
  | AndOrStructure.and v children => return
  | AndOrStructure.leaf v => return

-- for now get offered all possible applications
def Navigate : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    let mainTarget ← getMainTarget
    let tree ← buildAndOr lctx mainTarget AndORNodeType.ROOT
    navSubtree tree

    -- PrintSubtree tree

  elab "navigate" : tactic => do
    Navigate

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
    navigate
    sorry

    theorem test (a : Prop) (b : Prop) (c : Prop) (d : Prop) (m : Prop) (f : a → b) (g : b → c) (h : c → d) (i : b → d) (j: m → d) (k : a → b → c) (bb : b):
    (a → d) :=
  by
    intro ha
    navigate
