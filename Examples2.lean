import PBN
import Aesop

--set_option trace.aesop.tree true
--set_option trace.Elab.definition true
set_option pp.all true



set_option aesop.check.all true

/-abbrev Variable := String

def State := Variable → Nat

inductive Stmt : Type where
  | skip : Stmt
  | assign : Variable → (State → Nat) → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo : (State → Prop) → Stmt → Stmt

infix:60 ";; " => Stmt.seq

export Stmt (skip assign seq ifThenElse whileDo)

set_option quotPrecheck false in
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)

inductive BigStep : Stmt → State → State → Prop where
  | protected skip (s : State) :
    BigStep skip s s
  | protected assign (x : Variable) (a : State → Nat) (s : State) :
    BigStep (assign x a) s (s[x ↦ a s])
  | protected seq {S T : Stmt} {s t u : State} (hS : BigStep S s t) (hT : BigStep T t u) :
    BigStep (S;; T) s u
  | protected if_true {B : State → Prop} {s t : State} (hcond : B s) (S T : Stmt) (hbody : BigStep S s t) :
    BigStep (ifThenElse B S T) s t
  | protected if_false {B : State → Prop} {s t : State} (hcond : ¬ B s) (S T : Stmt) (hbody : BigStep T s t) :
    BigStep (ifThenElse B S T) s t
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep S s t) (hrest : BigStep (whileDo B S) t u) :
    BigStep (whileDo B S) s u
  | while_false {B S s} (hcond : ¬ B s) :
    BigStep (whileDo B S) s s

notation:55 "(" S:55 "," s:55 ")" " ⇓ " t:55 => BigStep S s t

add_aesop_rules safe [BigStep.skip, BigStep.assign, BigStep.seq, BigStep.while_false]
add_aesop_rules 50% [apply BigStep.while_true]
add_aesop_rules safe [
  (by apply BigStep.if_true (hcond := by assumption) (hbody := by assumption)),
  (by apply BigStep.if_false (hcond := by assumption) (hbody := by assumption))
]

@[aesop unsafe]
theorem state_extensionality {S : Stmt} {s1 s2 t : State}
  (eq: ∀ v, s1 v = s2 v) (h : (S, s1) ⇓ t) : (S, s2) ⇓ t :=
  by
    have h : s1 = s2 := by funext; aesop
    aesop

namespace BigStep

--@[aesop safe destruct]
--theorem cases_if_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ⇓ t → (S, s) ⇓ t := by
  --intro h; cases h <;> aesop

@[aesop safe destruct]
theorem cases_if_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ⇓ t → (T, s) ⇓ t := by
  intro h; cases h <;> aesop

@[aesop 30%]
theorem and_excluded {P Q R : Prop} (hQ : P → Q) (hR : ¬ P → R) : (P ∧ Q ∨ ¬ P ∧ R) := by
  by_cases h : P <;> aesop

theorem if_iff {B S T s t} : (ifThenElse B S T, s) ⇓ t ↔
    (B s ∧ (S, s) ⇓ t) ∨ (¬ B s ∧ (T, s) ⇓ t) := by
    navaesop "A!" (BigStep S s t)

  --aesop
  --navaesop


end BigStep-/





















theorem testinggg (a b c d u w y z : Prop) (f : b → c → a) (g : c → d → a) (x : w → d) (j : a → u → y):
    y :=
  by
  --printAndOrGraph
  --navhave! doesn't prune props yet

  navhavent c

theorem exists_five : ∃ n : Nat, n = 5 := by
  apply Exists.intro


theorem ao_exampleee (A B C D M E X Z Y P Q L : Prop) (f : B → C → Q → L → A) (g : C → B → A) (h : E → X → Z → B) (i : Z → Y → P → B) (j : M → D) (hX : X) (hZ : Z) :
    A :=
  by


theorem ao_example2 (A B C D M E X Z Y P Q L : Prop) (g : C → B → A) (h : X → Z → B) (i : Z → Y → P → B) (j : M → D) (hX : X) (hZ : Z) :
    A :=
  by
  --have hC : C := ?_
  --aesop
  navaesop "C" C
  --have hM : M := ?_



  --navaesop
  --navaesop
  --aesop
  /-navhave hM : M end
  navhave hQ : Q end
  navaesop
  aesop



  navhave hC : C end
  navhave! hB : B end


  . sorry
  . navhave! hZ : Z end
    navhave hY : Y end
    navhavent Y -- hY still in Z context bc not part of and/or graph
    navhave! hX : X end
    navhave hE : E end
    . sorry
    . sorry
    . sorry-/

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

theorem more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a := by
  intro f hc hb
  navhave hab : a → b end
  . intro ha
    exact hb



theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b := by
  sorry

theorem about_Impl (a b : Prop) :
  ¬ a ∨ b → a → b := by
  intro f ha
  navhave na : ¬a end


def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

theorem EM_of_DN : DoubleNegation → ExcludedMiddle := by
  --printAndOrGraph
  unfold DoubleNegation
  unfold ExcludedMiddle
  intro dn a

  --apply dn
  --intro n










-- do every possible application first?
  -- should the stuff that is proven secondarily from navhave be propogated to the other contexts?
  -- should anything be pruned from navhave? Stuff that can only be used to prove the thing that was just"have"d?
  -- later on this would not be included in other new contexts
  -- can a user navhave! something that is already in the context? Like if b is proven and then navhave! b
  -- does this work with and/or/exists/forall ?
  -- navhave! only prunes in the main context?
  -- after main context is prunes the next navhave context will have its reduced hypotheses, but the contexts copied before will have more
  -- does my definition of reachable / could be used in a proof with work?

  -- deleting props

  -- when to do what in which contexts
  -- what stuff should stick around in new contexts? What if it's a rule that is not part of the current and/or graph for that context's goal?

-- how strict should pruning be? In navhavent if there is a rule that could still be applied if stuff is provided but it would not currently be productive for the goal?
-- how much to take into account that the lean context can have new rules added in the middle of a proof?

-- how much does it matter what is displayed in the context vs the state of the and/or graph? Like when y is leftover from a navhavnet y because it wasn't in the and/or graph?
-- what if context needs to be massaged through intros and such?
