import Examples.ProofRequirementSupport

/-! Coordinator reference solutions. Withheld from authors until attempts close. -/
namespace ProofRequirementTrial.Reference

universe u v

/-- Reversing a binary operation suffices; associativity is not used. -/
structure Reverses (A : Type u) (m : A → A → A) (f : A → A) : Prop where
  reverse_op : ∀ x y, f (m x y) = m (f y) (f x)

theorem blocks {A : Type u} {m : A → A → A} {f : A → A}
    (h : Reverses A m f) (x y z : A) :
    f (m x (m y z)) = m (m (f z) (f y)) (f x) := by
  calc
    f (m x (m y z)) = m (f (m y z)) (f x) := h.reverse_op x (m y z)
    _ = m (m (f z) (f y)) (f x) :=
      congrArg (fun t => m t (f x)) (h.reverse_op y z)

/-- Faithful replay of the source detour requires an extra law. -/
theorem blocks_detour {A : Type u} {m : A → A → A} {f : A → A}
    (h : Reverses A m f) (involution : ∀ x, f (f x) = x) (x y z : A) :
    f (m x (m y z)) = m (m (f z) (f y)) (f x) := by
  calc
    f (m x (m y z)) = f (m (f (f x)) (m y z)) :=
      congrArg (fun t => f (m t (m y z))) (involution x).symm
    _ = f (m x (m y z)) :=
      congrArg (fun t => f (m t (m y z))) (involution x)
    _ = m (m (f z) (f y)) (f x) := blocks h x y z

def lists : Reverses (List Nat) Targets.listOp Targets.listFlip :=
  ⟨List.reverse_append⟩

def bools : Reverses Bool Targets.boolOp Targets.boolFlip := by
  constructor
  intro x y
  cases x <;> cases y <;> rfl

theorem list_blocks (x y z : List Nat) :
    (x ++ (y ++ z)).reverse = (z.reverse ++ y.reverse) ++ x.reverse :=
  blocks lists x y z

theorem bool_blocks (x y z : Bool) :
    Bool.xor x (Bool.xor y z) = Bool.xor (Bool.xor z y) x :=
  blocks bools x y z

example : ([1, 2] ++ ([3] ++ [4, 5])).reverse = [5, 4, 3, 2, 1] :=
  list_blocks [1, 2] [3] [4, 5]

example : ([] ++ ([] ++ []) : List Nat).reverse = [] := list_blocks [] [] []

example : Bool.xor true (Bool.xor false true) = false := bool_blocks true false true

theorem bad_associative (x y z : Bool) :
    Targets.badOp (Targets.badOp x y) z = Targets.badOp x (Targets.badOp y z) := rfl

theorem bad_reversal : ¬ Reverses Bool Targets.badOp Targets.boolFlip := by
  intro h
  have impossible := h.reverse_op true false
  cases impossible

theorem bad_blocks :
    Targets.boolFlip (Targets.badOp true (Targets.badOp false false)) ≠
      Targets.badOp (Targets.badOp (Targets.boolFlip false) (Targets.boolFlip false))
        (Targets.boolFlip true) := by decide

/-- The source's full right-unit law is stronger than the observation needs. -/
structure ObservedUnit (A : Type u) (B : Type v) (m : A → A → A)
    (e : A) (observe : A → B) : Prop where
  observe_unit : ∀ x, observe (m x e) = observe x

def selected {A : Type u} {B : Type v} {m : A → A → A} {e : A} {observe : A → B}
    (h : ObservedUnit A B m e observe) (x : A) :
    { y : A // observe y = observe (m x e) } :=
  ⟨x, (h.observe_unit x).symm⟩

theorem selected_value {A : Type u} {B : Type v} {m : A → A → A}
    {e : A} {observe : A → B} (h : ObservedUnit A B m e observe) (x : A) :
    (selected h x).val = x := rfl

def listObserved : ObservedUnit (List Nat) Nat Targets.listOp Targets.listUnit
    Targets.listObserve := ⟨fun x => congrArg List.length (List.append_nil x)⟩

def boolObserved : ObservedUnit Bool Bool Targets.boolOp Targets.boolUnit
    Targets.boolObserve := by
  constructor
  intro x
  cases x <;> rfl

example : (selected listObserved [1, 2]).val = [1, 2] := selected_value _ _
example : (selected listObserved []).val = [] := selected_value _ _
example : (selected boolObserved true).val = true := selected_value _ _

theorem selected_recovers_source (x : List Nat) : selected listObserved x = Source.selected x := rfl

theorem missing_observed_unit : ¬ ObservedUnit Nat Nat Nat.add 1 id := by
  intro h
  have impossible := h.observe_unit 0
  cases impossible

theorem wrong_selection : ¬ (∃ w : { y : Nat // y = 0 + 1 }, w.val = 0) := by
  rintro ⟨w, hw⟩
  have impossible : (0 : Nat) = 1 := hw.symm.trans w.property
  cases impossible

/-- Existence is inhabited even where the specified selection is impossible. -/
example : Nonempty { y : Nat // y = 0 + 1 } := ⟨⟨1, rfl⟩⟩

def alternative : { y : List Nat // y.length = ([1] ++ []).length } := ⟨[2], rfl⟩

theorem selected_distinguishable : (selected listObserved [1]).val ≠ alternative.val := by decide

def erase {A : Type u} {p : A → Prop} (w : Subtype p) : Nonempty (Subtype p) := ⟨w⟩

theorem erasure_equal : erase (selected listObserved [1]) = erase alternative :=
  Subsingleton.elim _ _

theorem erasure_cannot_recover :
    ¬ ∃ recover : Nonempty { y : List Nat // y.length = ([1] ++ []).length } → List Nat,
      (∀ w, recover (erase w) = w.val) := by
  rintro ⟨recover, law⟩
  apply selected_distinguishable
  exact (law (selected listObserved [1])).symm.trans
    ((congrArg recover erasure_equal).trans (law alternative))

end ProofRequirementTrial.Reference
