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
            | Node.OR _ _ p2 _ =>
              for rule in p2 do
                -- if rule in rule map, do nothing
                -- if rule not in rule map, add rule -> true
                if !ruleMap.contains rule then
                  ruleMap := ruleMap.insert rule true
            | _ => continue

      | Node.OR s c p _ =>
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

def navHave (toHave : Expr) (h : Ident) (mvar : Expr) : TacticM MVarId := do
  let g ← getMainGoal
  let lctx ← getLCtx
  let name := lctx.getUnusedName `h
  let mut g ← g.assert name toHave mvar
  let (_, g') ← g.intro h.getId
  return g'

--syntax "navhave " ident term (" with " "(" ident,* ")")? : tactic

elab "navhave" h:ident ":" t:term "-n"? n:ident* "end": tactic => do


  let e ← elabTerm t none
  let main ← getMainGoal
  let mvar ← main.withContext do
    mkFreshExprMVar (e)
  let goals ← getGoals
  let mut new_goals : List MVarId := []
  for goal in goals do
    let get_goal ← goal.withContext do
      let new_mvar ← navHave e h mvar

      let pruned_mvar ← new_mvar.withContext do
        let lctx ← getLCtx
        let mainTarget ← goal.getType
        let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []
        let emptyGraph : ANDORGraph := { edges := [], nodeMap := {}, root := "", andMap := {}}
        let graph ← toGraph tree emptyGraph []
        let mut pretty_new_hyp ← Lean.Meta.ppExpr e

        let mut pruneProvenn ← pruneProven graph pretty_new_hyp.pretty
        let derivation_path := pruneProvenn.2


        let mut m := new_mvar

        -- are new hyptheses available now? P
        let addd := pruneProvenn.1.2
        let mut new_names := n.map (·.getId)
        while new_names.toList.length < addd.length do
          let temp ← mkFreshUserName `h
          new_names := new_names.push temp
        let mut name_idx := 0
        let mut new_h := h.getId
        new_names := new_names.reverse
        for add in addd do

          let add_exp := add.map mkFVar
          let proof := mkAppN add_exp.head! add_exp.tail.toArray
          let type ← inferType proof
          pretty_new_hyp ← Lean.Meta.ppExpr type
          let name ← mkFreshUserName `h
          let m' ← m.assert name type proof

          let name2_option := new_names[name_idx]?
          let mut name2 ← mkFreshUserName `h
          match name2_option with
          | (some existing_name) =>
            name_idx := name_idx + 1
            name2 := existing_name
            new_h := existing_name
          | none =>
            name2 := name2
            new_h := name2
          let (_, m'') ← m'.intro name2
          m := m''

        --
        let new_pruned_mvar ← m.withContext do
          let mut n := m
          let lctx ← getLCtx
          let mainTarget ← goal.getType
          let tree ← buildAndOrTree lctx mainTarget AndORNodeType.ROOT []
          let emptyGraph : ANDORGraph := { edges := [], nodeMap := {}, root := "", andMap := {}}
          let graph ← toGraph tree emptyGraph []

          let prune1 ← pruneDescendants graph pretty_new_hyp.pretty new_h.toString [] pretty_new_hyp.pretty
          let prune := prune1.1
          let prunestr := prune1.2
          --let mut pruneProven2 ← pruneProven graph pretty_new_hyp.pretty
          --prune := prune ++ pruneProven2.1


          for hyp in prune do
            n ← n.tryClear hyp

          logInfo m!"{derivation_path} is derivation path"
          logInfo m!"{prunestr} were pruned"
          for hyp in prunestr do
            logInfo m!"is {hyp} on derivation path?"
            if !derivation_path.contains hyp then
              logInfo m!"{hyp} not on derivation path"

          pure n
        pure [new_pruned_mvar]
      pure pruned_mvar


    new_goals := new_goals ++ get_goal
  new_goals := new_goals ++ [mvar.mvarId!]
  replaceMainGoal new_goals

  -- solve main goal if goal type has been reached
  let main ← getMainGoal
  let maint := (←main.getDecl).type
  main.withContext do
    let lctx ← getLCtx
    for ldecl in lctx do
      unless ldecl.isImplementationDetail do
        let t ← inferType ldecl.toExpr
        if t == maint then
          let uname := mkIdent (ldecl.userName)
          evalTactic (← `(tactic| exact $uname))

elab "navhavent"  t:term : tactic => do
  -- remove any rules that use this term, in all contexts
  return









  -- for each context
    -- build and-or graph
    -- prune the stuff that is only a descendant of t- get back a list of hypotheses to delete from the context

    -- w = t
    -- while having w satisfies some rule(s),
      -- prune stuff below the rule and any alternate rules to prove the new goal(s)
      -- w = new goal(s)
    -- get back another list of hypotheses to delete from context


-- next- essential things, order

--With navhave you always have to provide the node in *some way*
-- tell the story of some example in both ao-nav and this tool
-- intermediate steps, not just proofs done by tactics
-- "play" a strategy
-- re-play what ao-nav did
-- implement some strategy
-- strategies are modular
-- how does pruning relate to strong soundness and completeness in report

-- context names
-- finish the newly proved part of navhave
-- false labels -> but actually means unprovable
-- some sort of navigation strategies (random, all, essential etc)


-- if main goal gets proven, exact that
-- if a something gets proven as an effect of a navhave, also prune other stuff below it


-- if extra hypotheses get created at a navhave in a particular context, should other contexts get access to those hypotheses?

-- any time a new hypothesis is created from pruneproven, also delete any goals that are only descendants of it that are not on the derivation path
