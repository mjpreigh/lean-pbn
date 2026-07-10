-- Build and traverse AND-OR graphs
import Lean
import Std.Data.HashMap
import Std.Data.HashSet

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta

-- T
-- T! : prune
-- A! : prune and axiomotize
-- A : axiomotize
-- F : prune

structure SimpleANDORGraph where
  or_nodes : List (String × String)
  edges : List (String × String)

-- return the conclusion of an AND-node (its parent)
def conclusion (graph : SimpleANDORGraph) (and_node : String) : MetaM String := do
  for edge in graph.edges do
    if edge.2 == and_node then
      return edge.1
  throwError "no parent"

-- return consumers of an OR-node (all of its parents)
def consumers (graph : SimpleANDORGraph) (or_node : String) : MetaM (List String) := do
  let mut consumers : List String := []
  for edge in graph.edges do
    if edge.2 == or_node then
      consumers := edge.1 :: consumers
  return consumers

-- return premises of an AND-node
def premises (graph : SimpleANDORGraph) (and_node : String) : MetaM (List String) := do
  let mut ps := []
  for edge in graph.edges do
    if edge.1 == and_node then
      ps := edge.2 :: ps
  return ps

def provableORNodes (graph : SimpleANDORGraph) (and_leaves : List String) : MetaM (List String) := do
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
def provable (graph : SimpleANDORGraph) (and_leaves : List String) (or_node : String) : MetaM Bool := do
  let provable_or_nodes ← provableORNodes graph and_leaves
  logInfo m!"and_leaves : {and_leaves}"
  logInfo m!"provable or nodes : {provable_or_nodes}"
  return provable_or_nodes.contains or_node
