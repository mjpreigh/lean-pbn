import PBN

theorem testinggg (a b c d w y z : Prop) (f : b → c → a) (g : c → d → a) (x : d → b):
    a :=
  by
  --printAndOrGraph

  navhave! hb : b end



  -- should the stuff that is proven secondarily from navhave be propogated to the other contexts?
  -- should anything be pruned from navhave? Stuff that can only be used to prove the thing that was just"have"d?
  -- later on this would not be included in other new contexts
  -- can a user navhave! something that is already in the context? Like if b is proven and then navhave! b
  -- does this work with and/or/exists/forall ?
  -- creating a lot of graphs throughout new hypotheses, pruning, etc and traversing these graphs. How concerned should I be right now about speed of this?
  -- navhave! only prunes in the main context?
