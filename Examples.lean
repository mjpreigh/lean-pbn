import PBN

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
    sorry
    --navigate

  theorem test (a b c d m : Prop) (f : a → b) (h : c → d) (i : b → d) (j: m → d) (k : a → b → c) (M : b → a) (bb : b):
    (b → c) :=
  by
    --navigate
    --printANDOR
    sorry

  def test2 (a : Prop) (b : Prop) (c : Prop) (d : Prop) (m : Prop) (f : Int → String) (f2 : Int → String)  (g : a → Int) (h : c → d) (i : b → d) (j: m → d) (k : a → b → c) (bb : b):
    (a → String) :=
  by
    intro ha
    apply f
    have x := i ?bbbb
    . sorry
    sorry
    --navigate

  theorem testingg (c d e : Prop) (g : d → e → c) (hd : d) (he : e) :
    c :=
  by
    have x := g hd he
    --navigate
    sorry

  theorem testinggg (a b c d e : Prop) (g : a → b → d → e → c) (hd : d) (he : e) :
    e → c :=
  by
    --navigate
    sorry

  theorem testingggg (a b c : Prop) (ab : a → b) (bc : b → c):
    a → c :=
  by
    intro ha
    --have x := ab ha
    --navigate
    sorry

def testinggggg (a b c d f : Prop) (hb : b) (hc : c) (bca : b → c → a) (cda : c → d → a):
    a :=
  by
    navigate

    --have ha := bca hb hc
    printANDOR
    navbottomup
    --have x := bca hb
    sorry

  theorem testd (a b c d m : Prop) (f : a → b) (k : a → b → c) :
    c :=
  by
    --navigate
    --printANDOR
    --navbottomup
    sorry

theorem testt (a b c d e x y z : Prop) (f : b → c → a) (g : c → d → a) (h : e → x → z → b) (i : z → y → b)
 (he : e) (hx : x) (hy : y) (hz : z)
:
    a :=
  by
    --navhave m b
    --navprune m b
    --navigate
    --have hx: x := sorry
   -- have h' he hz := h he hx hz

   -- have he: e := sorry
    --have h' := h he

   -- all_goals have hb: b := ?b
   -- all_goals have hx: x := sorry
   -- all_goals have hz: z := sorry
    --case b => grind

      -- apply h <;> trivial




    --printANDOR
    --navbottomup
    sorry

theorem testtt (a b c d e x y z : Prop) (f : b → c → a) (g : c → d → a) (h : e → x → z → b) (i : z → y → b):
    a :=
  by

    navhave hz:z end
    navhave hx:x end
    --navhave hd d
    navhave hc:c end
    navhave he:e -n hb ha end



    --have hb : b := sorry
    --navbottomup


    --navhave h b
   -- . exact hy
   -- . apply ea h
   -- . exact he

    --navprune h e

    --navprune e he

    --navhave h e
    --navprune h e
    --. apply ea
     -- exact h
    --. exact hy
    --. exact he
