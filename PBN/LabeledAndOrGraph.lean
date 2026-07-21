-- Build and traverse AND-OR graphs
import Lean
import Std.Data.HashMap
import Std.Data.HashSet

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta


inductive Label where
| Unseen
| Unknown -- ?
| False -- F
| True (force_use : Bool) (assume : Option Bool)
  -- false, None: T/A
  -- false, Some(false): T
  -- false, Some(true): A
  -- true, None: T/A !
  -- true, Some(false): T!
  -- true, Some(true): A!

def labelString (label : Label) : MetaM String := do
  return match label with
  | Label.Unknown => "?"
  | Label.False => "F"
  | Label.True false false => "T"
  | Label.True false true => "A"
  | Label.True true false => "T!"
  | Label.True true true => "A!"
  | _ => "Should not be here"

structure LabeledANDORGraph where
  or_nodes : HashMap String String -- id, node struct
  edges : List (String × String) -- id to id
  labels : HashMap String Label
  assume : List String
  bang : List String
  false_ : List String
  unseen : List String

-- return the conclusion of an AND-node (its parent)
def conclusion (graph : LabeledANDORGraph) (and_node : String) : MetaM String := do
  for edge in graph.edges do
    if edge.2 == and_node then
      return edge.1
  throwError "no parent"

-- return consumers of an OR-node (all of its parents)
def consumers (graph : LabeledANDORGraph) (or_node : String) : MetaM (List String) := do
  let mut consumers : List String := []
  for edge in graph.edges do
    if edge.2 == or_node then
      consumers := edge.1 :: consumers
  return consumers

-- return premises of an AND-node
def premises (graph : LabeledANDORGraph) (and_node : String) : MetaM (List String) := do
  let mut ps := []
  for edge in graph.edges do
    if edge.1 == and_node then
      ps := edge.2 :: ps
  return ps

def provableORNodes (graph : LabeledANDORGraph) (and_leaves : List String) : MetaM (List String) := do
  let mut inferred : HashSet String := {}
  let mut agenda : List (MetaM String) :=  and_leaves.map (conclusion graph)
  let mut count : HashMap String Nat := {}

  while agenda.length > 0 do
    let p ← agenda.head!
    agenda := agenda.tail
    if inferred.contains p then
      continue

    inferred := inferred.insert p

    for consumer in (← consumers graph p) do
      -- if consumer is not in count, add to count and initialize value to # args it consumes
      if !count.contains consumer then
        count := count.insert consumer (← premises graph consumer).length

      let c : Nat := count.get! consumer
      count := count.insert consumer (c - 1)

      -- if value is 0, all args have been proven
      if c - 1 == 0 then
        agenda := conclusion graph consumer :: agenda

  return inferred.toList

-- is an OR-node provable?
def provable (graph : LabeledANDORGraph) (and_leaves : List String) (or_node : String) : MetaM Bool := do
  let provable_or_nodes ← provableORNodes graph and_leaves
  logInfo m!"and_leaves : {and_leaves}"
  logInfo m!"provable or nodes : {provable_or_nodes}"
  return provable_or_nodes.contains or_node

def NonemptyCompletion (graph : LabeledANDORGraph) (node_id : String) (label : Label) : TacticM Bool := do
  let main ← getGoals
  let new_goal ← withLCtx {} {} do
    mkFreshExprMVar (some (mkConst ``True))
  --let new_goal ← mkFreshExprMVar (mkConst ``True)
  setGoals [new_goal.mvarId!]
  evalTactic (← `(tactic|
    bv_decide
  ))
  let num_remaining := (← getGoals).length
  setGoals main
  if num_remaining == 0 then
    return true
  return false
