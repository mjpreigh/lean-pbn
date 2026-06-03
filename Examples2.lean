import PBN

theorem testinggg (a b c d u w y z : Prop) (f : b → c → a) (g : c → d → a) (x : w → d) (j : a → u → y):
    y :=
  by
  --printAndOrGraph
  --navhave! doesn't prune props yet

  navhavent c

theorem ao_example2 (A B C D M E X Z Y P : Prop) (f : B → C → A) (g : C → D → M → A) (h : E → X → Z → B) (i : Z → Y → P → B) :
    A :=
  by
  navhave hC : C end
  navhave! hB : B end
  exact f hB hC
  . sorry
  . navhave! hZ : Z end
    navhave hY : Y end
    navhavent Y -- hY still in Z context bc not part of and/or graph
    navhave! hX : X end
    navhave hE : E end
    exact h hE hX hZ
    . sorry
    . sorry
    . sorry

  /-
    navhave hC : C end
    navhave! hB : B end
    . apply proof_of_C
    . navhave! hZ : Z end
      navhave hY : Y end
      navhavent Y
      navhave! hX : X end
      navhave hE : E end
      . apply proof_of_Z
      . apply proof_of_X
      . apply proof_of_E
        -/





  -- should the stuff that is proven secondarily from navhave be propogated to the other contexts?
  -- should anything be pruned from navhave? Stuff that can only be used to prove the thing that was just"have"d?
  -- later on this would not be included in other new contexts
  -- can a user navhave! something that is already in the context? Like if b is proven and then navhave! b
  -- does this work with and/or/exists/forall ?
  -- creating a lot of graphs throughout new hypotheses, pruning, etc and traversing these graphs. How concerned should I be right now about speed of this?
  -- navhave! only prunes in the main context?
  -- after main context is prunes the next navhave context will have its reduced hypotheses, but the contexts copied before will have more
  -- does my definition of reachable / could be used in a proof with work?

  -- get rid of the new graph stuff
  -- deleting props

  -- when to do what in which contexts
  -- what stuff should stick around in new contexts? What if it's a rule that is not part of the current and/or graph for that context's goal?

-- how strict should pruning be? In navhavent if there is a rule that could still be applied if stuff is provided but it would not currently be productive for the goal?
-- how much to take into account that the lean context can have new rules added in the middle of a proof?
