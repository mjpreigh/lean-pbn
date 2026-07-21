-- freshGoal.mvarId!.setUserName `custom_goal
import Lean
import Std.Data.HashMap
import PBN.AndORGraph
import PBN.LabeledAndOrGraph
import PBN.Providers
import Aesop

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
      if (← local_goal.getType) == e then
        continue
      let mut new_local_goal ← local_goal.withContext do
          let and_or_graph ← constructGraph local_goal
          let new_goal ← deleteUnusableRulesAndIrrelevantArgs and_or_graph e local_goal
          pure (new_goal)
      new_goals := new_goals ++ [new_local_goal]

    return new_goals

  def checkSolved (goals : List MVarId) : TacticM Unit := do
    for goal in goals do
      goal.withContext do
        let main_goal ← goal.getType
        let lctx ← getLCtx
        for ldecl in lctx do
          unless ldecl.isImplementationDetail do
            let t ← inferType ldecl.toExpr
            if t == main_goal then
              let uname := mkIdent (ldecl.userName)
              evalTactic (← `(tactic| exact $uname))
    return

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
  checkSolved  new_goals


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
  -- m!"{new_goals}"
  -- so delete any hypotheses or props that are not reachable from t
  new_goals ← pruneNotReachable new_goals new_hyp_type
  replaceMainGoal new_goals
  checkSolved  new_goals

-- A and A! get added to the context and create new goals
-- A! and F cause pruning
elab "navaesop" "A![" A!:term,* "]" "A[" A:term,* "]" "T[" T:term,* "]" "T![" T!:term,* "]" "F[" F:term,* "]" "Q?[" Q?:term,* "]" : tactic => do

  --let HaveStr := (← ppExpr (← Term.elabType HaveTerm)).pretty
  --let HaventStr := (← ppExpr (← Term.elabType HaveTerm)).pretty


  -- run aesop
  let goal ← getMainGoal
  goal.withContext do
    let lctx ← getLCtx

    evalTactic (← `(tactic|
      set_option trace.aesop.tree true in
      aesop
    ))

    let mut labels : HashMap String Label := {}
    let mut assumed : HashSet String := {}

    for a in A!.getElems do
      let a_str := (← ppExpr (← Term.elabType a)).pretty
      assumed := assumed.insert a_str
      labels := labels.insert a_str (Label.True true true)
    for a in A.getElems do
      let a_str := (← ppExpr (← Term.elabType a)).pretty
      assumed := assumed.insert a_str
      labels := labels.insert a_str (Label.True false true)
    for t in T.getElems do
      let t_str := (← ppExpr (← Term.elabType t)).pretty
      labels := labels.insert t_str (Label.True false false)
    for t in T!.getElems do
      let t_str := (← ppExpr (← Term.elabType t)).pretty
      labels := labels.insert t_str (Label.True false true)
    for f in F.getElems do
      let f_str := (← ppExpr (← Term.elabType f)).pretty
      labels := labels.insert f_str Label.False
    for q? in Q?.getElems do
      let q?_str := (← ppExpr (← Term.elabType q?)).pretty
      labels := labels.insert q?_str Label.Unknown

    let mut goals : HashMap String String := {}
    let mut edges : List (String × String) := []
    let mut unseen : List String:= []
    let mut and_leaves : List String := []
    let mut consolidatingGoal := false
    let mut onGoal := false
    let mut onRule := false
    let mut currGoal := ""
    let mut currID := ""

    let traces ← getTraces
    let mut stringSet : HashSet String := {}

    -- make AND-OR graph

    for t in traces do

      let tree := toString (← t.msg.format)
      let lines := tree.split "\n"
      for line in lines do
        let mut lineStripped := line.replace "✅️" ""
        lineStripped := lineStripped.replace "❓️" ""
        lineStripped := lineStripped.replace "🏁" ""
        lineStripped := lineStripped.replace "❌" ""
        lineStripped := lineStripped.replace " " ""

        --logInfo "line:"
        --logInfo m!"{line}"

        if lineStripped.contains "[aesop.tree]"then
          consolidatingGoal := false
          if lineStripped.toList[13]! == 'G' then
            -- at a new goal
            consolidatingGoal := true
            -- get label
            currGoal := (line.copy.splitOn "⋯ ⊢ ")[1]!

            currID := "G" ++ ((lineStripped.splitOn "G")[1]!.splitOn "[")[0]!

          else if lineStripped.toList[13]! == 'R' && !lineStripped.contains "[aesop.tree]Rule:" then
            -- at a new rule
            currID := "R" ++ ((lineStripped.splitOn "R")[1]!.splitOn "[")[0]!
          else
          -- look for rule/goal metadata
            if lineStripped.contains "[aesop.tree]Childgoals:[]" then
              and_leaves := currID :: and_leaves
            else if lineStripped.contains "[aesop.tree]Childgoals:[" then
              -- collect children and add new edges from rule
              let children := (((lineStripped.splitOn "[")[2]!.replace "]" "").split ",").toList
              for child in children do
                if child != "" then
                  edges := (currID, "G" ++ child) :: edges
            else if lineStripped.contains "[aesop.tree]Childrapps:[" then

              --if currGoal == HaveStr then
              if assumed.contains currGoal then
                edges := (currID, "axiom") :: edges
                and_leaves := "axiom" :: and_leaves
              if !(labels.contains currGoal) then
                unseen := currID :: unseen
              -- collect children and add new goal node and edges from goal
              let children := (((lineStripped.splitOn "[")[2]!.replace "]" "").split ",").toList
              for child in children do
                if child != "" then
                  edges := (currID, "R" ++ child) :: edges
              goals := goals.insert currID currGoal
        else if consolidatingGoal == true then
          -- goal spans multiple lines
          currGoal := currGoal ++ "\n" ++ lineStripped

    --logInfo m!"goals : {goals}"
    --logInfo m!"edges : {edges}"

    let graph : LabeledANDORGraph := { or_nodes := goals , edges := edges, labels := labels, assume := [], bang := [], false_ := [], unseen := unseen}
    if (← provable graph and_leaves "G0") then
      logInfo "provable!!"
      for a in A.getElems do
        evalTactic (← `(tactic|
          have h : $a := ?_
        ))
      for a in A!.getElems do
        evalTactic (← `(tactic|
          have h : $a := ?_
        ))
      evalTactic (← `(tactic| aesop))
    else
      -- offer steps based on step provider
      logInfo "not provable"
      Random graph


elab "rust_test" : tactic => do
  logInfo m!"before"
  let output ← IO.Process.output {
    cmd := "./rustlib/target/debug/rustlib"
    args := #["A", "B", "C", "", "A", "C", "D"]
  }
  logInfo output.stdout
  logInfo m!"after"

elab "cmd_test" : tactic => do
  logInfo m!"before"
  let output ← IO.Process.output {
    cmd := "bash"
    args := #["-c", "echo hello > hello.txt"]
  }
  logInfo output.stdout
  logInfo m!"after"

-- A and A! take terms
-- rest take strings
-- if it has a projection it probably can't be A or A!
-- merge OR nodes with same goal but different ids into one (children)
elab "aonav_aesop" provider:str "A![" A!:term,* "]" "A[" A:term,* "]" "T[" T:str,* "]" "T![" T!:str,* "]" "F[" F:str,* "]" "Q?[" Q?:str,* "]" : tactic => do

    -- run aesop
  let goal ← getMainGoal
  goal.withContext do
    let lctx ← getLCtx

    evalTactic (← `(tactic|
      set_option trace.aesop.tree true in
      aesop
    ))

    -- construct a json style string and write to a file
    -- keep track of unique AND and OR nodes and edges that are seen
    -- sets for AND/OR nodes, map from each node to a set of its children for edges

    let mut goals : HashMap String String := {} --id to goal
    let mut goals_backwards : HashMap String (HashSet String) := {} -- goal to id
    let mut rules : HashSet String := {}
    let mut edges : HashMap String (HashSet String) := {}
    let mut unseen : List String:= []
    let mut and_leaves : List String := []
    let mut consolidatingGoal := false
    let mut onGoal := false
    let mut onRule := false
    let mut currGoal := ""
    let mut currID := ""

    let mut traces ← getTraces
    let mut stringSet : HashSet String := {}

    -- make AND-OR graph

    for t in traces do

      let tree := toString (← t.msg.format)
      let lines := tree.split "\n"
      for line in lines do
        --let mut lineStripped := line.replace "✅️" ""
        let mut lineStripped := String.ofList (line.toString.toList.filter (fun x => x.isAlphanum || x == '[' || x == ']' || x == '.' || x == '%'  || x == '⋯' || x == '⊢' || x == '|' || x == ':' || x == '(' || x == ')' || x == '?' || x == ','))
        --logInfo m!"{line}"
        --logInfo m!"{lineStripped}"
        --let mut lineStripped := line.replace "{[^a-zA-Z0-9]}" ""
        --let lscopy := lineStripped
        --lineStripped := "[aesop.tree]" ++ (lscopy.splitOn "[aesop.tree]")[1]!
        --lineStripped := lineStripped.replace "❓️" ""
        --lineStripped := lineStripped.replace "🏁" ""
        --lineStripped := lineStripped.replace "❌" ""
        --lineStripped := lineStripped.replace " " ""
        --lineStripped := lineStripped.replace "\t" ""
        --lineStripped := lineStripped.replace "\n" ""
        --let x := lineStripped.toList.filter (fun c => c.toNat < 32 || c.toNat == 127 || (c.toNat >= 128 && c.toNat <= 159))


        --logInfo "line:"
        --logInfo m!"{line}"

        if lineStripped.contains "[aesop.tree]"then
          consolidatingGoal := false
          --logInfo m!"{lineStripped} : {lineStripped.toList[13]!}"
          if lineStripped.toList[12]! == 'G' then
            -- at a new goal
            consolidatingGoal := true
            -- get label
            --currGoal := (lineStripped.splitOn "⋯⊢")[1]!
            currGoal := (line.copy.splitOn "⋯ ⊢ ")[1]!
            currID := "G" ++ ((lineStripped.splitOn "G")[1]!.splitOn "[")[0]!
            goals := goals.insert currID currGoal
            if !goals_backwards.contains currGoal then
              goals_backwards := goals_backwards.insert currGoal {currID}
            else
              let mut set := goals_backwards.get! currGoal
              set := set.insert currID
              goals_backwards := goals_backwards.insert currGoal set

          else if lineStripped.toList[12]! == 'R' && !lineStripped.contains "[aesop.tree]Rule:" then
            --logInfo m!"{line}"
            -- at a new rule
            currID := "R" ++ ((lineStripped.splitOn "R")[1]!.splitOn "[")[0]!
            rules := rules.insert currID
          else
          -- look for rule/goal metadata
            if lineStripped.contains "[aesop.tree]Childgoals:[]" then
              and_leaves := currID :: and_leaves
            else if lineStripped.contains "[aesop.tree]Childgoals:[" then
              -- collect children and add new edges from rule
              let children := (((lineStripped.splitOn "[")[2]!.replace "]" "").split ",").toList
              for child in children do
              let mut children_ids : HashSet String := {}
              for child in children do
                if child != "" then
                  children_ids := children_ids.insert ("G" ++ child)
              if edges.contains currID then
                let mut set := edges.get! currID
                for s in set do
                  set := set.insert s
                edges := edges.insert currID set
              else
                edges := edges.insert currID children_ids
            else if lineStripped.contains "[aesop.tree]Childrapps:[" then
              --logInfo m!"{currID}"
              --logInfo m!"{line}"

              -- collect children and add new goal node and edges from goal
              let children := (((lineStripped.splitOn "[")[2]!.replace "]" "").split ",").toList
              let mut children_ids : HashSet String := {}
              for child in children do
                if child != "" then
                  children_ids := children_ids.insert ("R" ++ child)
              if edges.contains currID then
                let mut set := edges.get! currID
                for s in set do
                  set := set.insert s
                edges := edges.insert currID set
              else
                edges := edges.insert currID children_ids
        else if consolidatingGoal == true then
          -- goal spans multiple lines
          let old_goal := currGoal
          currGoal := currGoal ++ " " ++ lineStripped
          goals := goals.insert currID currGoal
          if !goals_backwards.contains old_goal then
              goals_backwards := goals_backwards.insert currGoal {currID}
          else
            let mut set := goals_backwards.get! old_goal
            set := set.insert currID
            goals_backwards := goals_backwards.insert currGoal set

    /-for goal in goals do
      logInfo m!"goal: {goal}"
    for (goal,set) in goals_backwards do
      logInfo m!"bacakwards goal: {goal}"
      for s in set do
        logInfo m!"   {s}"-/
    let mut json_str := "{ \"graph\": {\n  \"metadata\": {\n    \"goal\": \"G0\"\n  },\n  \"nodes\": {"
    for (id,goal) in goals do
      json_str := json_str ++ s!"\n    \"{id}\": \{      \"label\": \"{goal}\",\n      \"metadata\": \{\n        \"kind\": \"OR\"\n      }\n      },"
    for id in rules do
      json_str := json_str ++ s!"\n    \"{id}\": \{\n      \"metadata\": \{\n        \"kind\": \"AND\"\n      }\n      },"
    -- cut off the last comma
    json_str := (json_str.dropEnd 1).copy
    json_str := json_str ++ s!"\n  },"
    json_str := json_str ++ "\n  \"edges\": ["
    for (parent, children) in edges do
      for child in children do
        json_str := json_str ++ s!"\n    \{\n      \"source\": \"{parent}\",\n      \"target\": \"{child}\"\n    },"
    -- cut off the last comma
    json_str := (json_str.dropEnd 1).copy
    json_str := json_str ++ "\n  ]\n} }"

    IO.FS.writeFile "aesopjson.json" json_str
    let mut working_args : Array String := #[]
    working_args := working_args.push "aesopjson.json"
    working_args := working_args.push provider.getString

    -- for each label list
      -- match goal to goalid(s?)
      -- add "id label" to working_args
    for a in A!.getElems do
      let a_str := (← ppExpr (← Term.elabType a)).pretty
      let goal_ids := goals_backwards.get! a_str
      for id in goal_ids do
        working_args := working_args.push s!"{id} A!"
    for a in A.getElems do
      let a_str := (← ppExpr (← Term.elabType a)).pretty
      let goal_ids := goals_backwards.get! a_str
      for id in goal_ids do
        working_args := working_args.push s!"{id} A"
    for t in T.getElems do
      --let t_str := (← ppExpr (← Term.elabType t)).pretty
      let goal_ids := goals_backwards.get! t.getString
      for id in goal_ids do
        working_args := working_args.push s!"{id} T"
    for t in T!.getElems do
      let goal_ids := goals_backwards.get! t.getString
      for id in goal_ids do
        working_args := working_args.push s!"{id} T!"
    for f in F.getElems do
      let goal_ids := goals_backwards.get! f.getString
      for id in goal_ids do
        working_args := working_args.push s!"{id} F"
    for q? in Q?.getElems do
      let goal_ids := goals_backwards.get! q?.getString
      for id in goal_ids do
        working_args := working_args.push s!"{id} ?"

    let output ← IO.Process.output {
      cmd := "./aonav/target/debug/aonav"
      --args := #["aesopjson.json", "G0 T!", "G1 T!"]
      args := working_args
    }
    let res := output.stdout
    logInfo res

    if res == s!"Valid!\n" then
      logInfo res
      let main_goal ← getMainGoal
      main_goal.withContext do
        for a in A.getElems do
          evalTactic (← `(tactic|
            have h : $a := ?_
          ))
        for a in A!.getElems do
          evalTactic (← `(tactic|
            have h : $a := ?_
          ))
        evalTactic (← `(tactic| aesop))
