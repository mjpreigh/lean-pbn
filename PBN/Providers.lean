import Lean
import Std.Data.HashMap
import Std.Data.HashSet
import PBN.LabeledAndOrGraph
import PBN.Rust

open Std
open Lean Lean.Elab.Tactic
open Lean Elab Tactic Meta


def committed_labels : MetaM (List Label) := do
    return [Label.Unknown, Label.False, Label.True false false, Label.True false true, Label.True true false, Label.True true true]

def Random (graph : LabeledANDORGraph) : TacticM Unit := do
    let unseen : List String := graph.unseen -- get unseen nodes
    let random ← IO.rand 0 (unseen.length - 1) -- random number
    let node_id := unseen[random]!
    let node_str : String := graph.or_nodes.get! node_id
    let mut possible_labels : List String := []

    for label in (← committed_labels) do
        if (← NonemptyCompletion graph node_id label) then
            possible_labels := (← labelString label) :: possible_labels

    logInfo m!"Label {node_str} as :"
    for label in possible_labels do
        logInfo m!"{label}"
        --let a := Rust.add 10 10
        --logInfo m!"{a}"
        IO.println (Rust.add 10 20)
