-- freshGoal.mvarId!.setUserName `custom_goal
import Lean
import Std.Data.HashMap
import PBN.AndORGraph

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta

set_option autoImplicit false
set_option tactic.hygienic false
set_option linter.unusedVariables false

def deriveMoreHypotheses (new_hyp : Expr) (goal : MVarId) : TacticM MVarId := do
  let and_or_graph ← constructGraph goal
  -- add new hypothesis to the graph and figure out if this gives anything else
  -- make actual applications to add new hypotheses to the context
  let new_goal ← findNewApps and_or_graph new_hyp goal
  return new_goal

-- add hypothesis to all contexts and create new context where its type is the goal
def addHypothesis (hyp_name : Ident) (new_hyp_type : Expr): TacticM (List MVarId) := do
  let main_goal ← getMainGoal
  -- makes sure new context gets everything in main
  let new_goal ← main_goal.withContext do
    mkFreshExprMVar new_hyp_type
  let goals ← getGoals
  let mut new_goals := []
  -- make sure every existing context gets the new hypothesis
  for local_goal in goals do
    let new_goal ← local_goal.withContext do
      let lctx ← getLCtx
      let name := lctx.getUnusedName `h
      let mut new_local_goal := local_goal
      new_local_goal ← new_local_goal.assert name new_hyp_type new_goal
      let (_, new_local_goal') ← new_local_goal.intro hyp_name.getId
      let new_local_goal'' ← deriveMoreHypotheses new_hyp_type new_local_goal'
      pure (new_local_goal'')
    new_goals := new_goals ++ [new_goal]
  new_goals := new_goals ++ [new_goal.mvarId!]
  return new_goals

  def pruneNotReachable (goals : List MVarId) (e : Expr) : TacticM (List MVarId) := do
    let main := goals[0]!
    let mut new_goals := []
    for local_goal in goals do
      let mut new_local_goal := local_goal
      if local_goal == main then
        new_local_goal ← local_goal.withContext do
          let and_or_graph ← constructGraph local_goal
          let new_goal ← deleteNotReachableFrom and_or_graph e local_goal
          pure (new_goal)
      new_goals := new_goals ++ [new_local_goal]
    return new_goals

  def pruneHavent (goals : List MVarId) (e : Expr) : TacticM (List MVarId) := do
    let mut new_goals := []
    for local_goal in goals do
      let mut new_local_goal ← local_goal.withContext do
          let and_or_graph ← constructGraph local_goal
          let new_goal ← deleteUnusableRulesAndIrrelevantArgs and_or_graph e local_goal
          pure (new_goal)
      new_goals := new_goals ++ [new_local_goal]

    return new_goals

-- have a hypothesis named h of type t in this context and add a new goal for t
-- optionally name anything that is derived along the way
elab "navhave" h:ident ":" t:term "-n"? n:ident* "end": tactic => do
  -- create new hypothesis
  -- create new goal
  -- hypothesis should appear in all existing contexts
  -- in each context, apply newly satisfied rules to get new hypotheses
  let new_hyp_type ← Term.elabType t
  let new_goals ← addHypothesis h new_hyp_type
  replaceMainGoal new_goals

elab "navhavent" t:term : tactic => do
  -- delete any hypotheses that can only be used in a proof that also uses t
  -- pruning all contexts
  let bad_hyp_type ← Term.elabType t
  let new_goals ← pruneHavent (← getGoals) bad_hyp_type
  setGoals new_goals

elab "navhave!" h:ident ":" t:term "-n"? n:ident* "end": tactic => do
  -- navhave but delete any hypotheses that cannot be used in a proof that also uses t
  -- only pruning main context
  let new_hyp_type ← Term.elabType t
  let mut new_goals ← addHypothesis h new_hyp_type
  -- so delete any hypotheses or props that are not reachable from t
  new_goals ← pruneNotReachable new_goals new_hyp_type
  replaceMainGoal new_goals
