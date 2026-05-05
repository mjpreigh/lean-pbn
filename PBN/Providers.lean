-- tactics over AND-OR trees and graphs

import Lean
import Std.Data.HashMap
import PBN.AndOr

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta


set_option autoImplicit false
set_option tactic.hygienic false

def navTopDown (node : AndOrStructure LocalDecl) : TacticM Unit := do
  match node with
  | AndOrStructure.root _ children =>
    -- present "apply" for each rule
    for rule in children do
      let r ← getNodeExpr rule
      logInfo m!"apply {r}"
  | AndOrStructure.or _ _ => return
  | AndOrStructure.and _ _ => return
  | AndOrStructure.leaf _ => return

  def navAllPossibilities (node : AndOrStructure LocalDecl) : TacticM Unit := do
  match node with

  | AndOrStructure.root _ children =>
    -- present "apply" for each rule
    for rule in children do
      let r ← getNodeExpr rule
      logInfo m!"apply {r}"
    for rule in children do
      navAllPossibilities rule

  | AndOrStructure.or _ children =>
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

  | AndOrStructure.leaf _ => return

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
    for (_, node) in graph.nodeMap do
      match node with
      | Node.AND _ c p _ _ =>
        -- if it is a leaf
        if List.length c == 0 then

          -- if it is AND, record which goal is true and which rule that goal is a child of
          for goal in p do
            argMap := argMap.insert goal true
            let goalnode := graph.nodeMap.get? goal
            match goalnode with
            | Node.OR _ _ p2 =>
              for rule in p2 do
                -- if rule in rule map, do nothing
                -- if rule not in rule map, add rule -> true
                if !ruleMap.contains rule then
                  ruleMap := ruleMap.insert rule true
            | _ => continue

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
      | Node.AND s _ _ x _ =>
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

def navHave (toHave : Expr) (h : Ident) (mvar : Expr) : TacticM (List MVarId) := do
  let g ← getMainGoal
  let lctx ← getLCtx
  let name := lctx.getUnusedName `h
  let mut g ← g.assert name toHave mvar
  let (_, g') ← g.intro h.getId
  return [g']

-- "super have"
-- new goal
-- residual context/residual graph
-- throughout all contexts
elab "navhavehalf" h:ident t:term : tactic => do
  let e ← elabTerm t none
  let mut mvar ← mkFreshExprMVar (e)
  let goals ← getGoals
  let mut new_goals : List MVarId := []
  for goal in goals do
    let get_goal ← goal.withContext do
      navHave e h mvar
    new_goals := new_goals ++ get_goal
  new_goals := new_goals ++ [mvar.mvarId!]
  replaceMainGoal new_goals

macro "pruneTestMacro" h:ident : tactic => do
  `(tactic|(clear $h))

elab "pruneTest" h:ident t:term : tactic => do
  let e ← elabTerm t none
  let fmt ← ppExpr e
  let mut goal ← getMainGoal
  let mainTarget ← goal.getType
  let lctx ← getLCtx
  let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []
  let emptyGraph : ANDORGraph := { edges := [], nodeMap := {}, root := "", andMap := {}}
  let graph ← toGraph tree emptyGraph []
  let hyp_delete : List FVarId ← pruneDescendants graph fmt.pretty h.getId.toString []
  let del := hyp_delete[0]!
  let goal2 ← goal.tryClear del

  replaceMainGoal [goal2]


elab "navprune" h:ident t:term : tactic => do
  let e ← elabTerm t none
  let mut new_goals2 : List MVarId := []
  let mut goals ← getGoals

  let mut hyp_delete : List FVarId := []
  for goal in goals do
    let hyp_delete1 ← goal.withContext do
      let lctx ← getLCtx
      let mainTarget ← goal.getType
      let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []
      let emptyGraph : ANDORGraph := { edges := [], nodeMap := {}, root := "", andMap := {}}
      let graph ← toGraph tree emptyGraph []
      let fmt ← ppExpr e
      pruneDescendants graph fmt.pretty h.getId.toString []
    hyp_delete := hyp_delete ++ hyp_delete1

  for goal in goals do
    let mvar ← goal.withContext do
      let mut m := goal
      for hyp in hyp_delete do
        m ← m.tryClear hyp
      pure m

    new_goals2 := [mvar] ++ new_goals2
  replaceMainGoal new_goals2


elab "navhave" h:ident t:term : tactic => do
  let e ← elabTerm t none
  let mut mvar ← mkFreshExprMVar (e)
  let goals ← getGoals
  let mut new_goals : List MVarId := []
  for goal in goals do
    let get_goal ← goal.withContext do
      navHave e h mvar
    new_goals := new_goals ++ get_goal
  new_goals := new_goals ++ [mvar.mvarId!]
  replaceMainGoal new_goals


  let mut new_goals2 : List MVarId := []
  let mut goals ← getGoals

  let mut hyp_delete : List FVarId := []
  for goal in goals do
    let hyp_delete1 ← goal.withContext do
      let lctx ← getLCtx
      let mainTarget ← goal.getType
      let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []
      let emptyGraph : ANDORGraph := { edges := [], nodeMap := {}, root := "", andMap := {}}
      let graph ← toGraph tree emptyGraph []
      let fmt ← ppExpr e
      pruneDescendants graph fmt.pretty h.getId.toString []
    hyp_delete := hyp_delete ++ hyp_delete1

  for goal in goals do
    if goal == mvar.mvarId! then
      continue
    let mvar2 ← goal.withContext do
      let mut m := goal
      for hyp in hyp_delete do
        m ← m.tryClear hyp
      pure m

    new_goals2 := [mvar2] ++ new_goals2
  replaceMainGoal new_goals2






  -- for each context
    -- build and-or graph
    -- prune the stuff that is only a descendant of t- get back a list of hypotheses to delete from the context

    -- w = t
    -- while having w satisfies some rule(s),
      -- prune stuff below the rule and any alternate rules to prove the new goal(s)
      -- w = new goal(s)
    -- get back another list of hypotheses to delete from context


-- next- essential things, order
