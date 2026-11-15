import Examples.ProofRequirementSupport

namespace ProofRequirementTrial.Assisted

universe u

/-- Reversing one binary operation is enough to reverse three blocks. -/
def ReversesOperation {A : Type u} (m : A → A → A) (f : A → A) : Prop :=
  ∀ x y, f (m x y) = m (f y) (f x)

/-- Replay the source body, retaining the ambient law and both involution steps. -/
theorem reverseBlocks_replay {A : Type u} (m : A → A → A) (f : A → A)
    (e : A) (_ambient : ∀ t, m t e = t)
    (involutive : ∀ t, f (f t) = t) (reverse : ReversesOperation m f)
    (x y z : A) :
    f (m x (m y z)) = m (m (f z) (f y)) (f x) := by
  calc
    f (m x (m y z)) = f (m (f (f x)) (m y z)) :=
      congrArg (fun t => f (m t (m y z))) (involutive x).symm
    _ = f (m x (m y z)) :=
      congrArg (fun t => f (m t (m y z))) (involutive x)
    _ = m (f (m y z)) (f x) := reverse x (m y z)
    _ = m (m (f z) (f y)) (f x) :=
      congrArg (fun t => m t (f x)) (reverse y z)

/-- The same conclusion with the cancelling involution detour removed. -/
theorem reverseBlocks {A : Type u} (m : A → A → A) (f : A → A)
    (reverse : ReversesOperation m f) (x y z : A) :
    f (m x (m y z)) = m (m (f z) (f y)) (f x) := by
  calc
    f (m x (m y z)) = m (f (m y z)) (f x) := reverse x (m y z)
    _ = m (m (f z) (f y)) (f x) :=
      congrArg (fun t => m t (f x)) (reverse y z)

theorem list_reverses : ReversesOperation Targets.listOp Targets.listFlip := by
  intro x y
  exact List.reverse_append

theorem bool_reverses : ReversesOperation Targets.boolOp Targets.boolFlip := by
  intro x y
  cases x <;> cases y <;> rfl

theorem list_reverseBlocks (x y z : List Nat) :
    Targets.listFlip (Targets.listOp x (Targets.listOp y z)) =
      Targets.listOp (Targets.listOp (Targets.listFlip z) (Targets.listFlip y))
        (Targets.listFlip x) :=
  reverseBlocks _ _ list_reverses x y z

theorem bool_reverseBlocks (x y z : Bool) :
    Targets.boolFlip (Targets.boolOp x (Targets.boolOp y z)) =
      Targets.boolOp (Targets.boolOp (Targets.boolFlip z) (Targets.boolFlip y))
        (Targets.boolFlip x) :=
  reverseBlocks _ _ bool_reverses x y z

theorem list_replay (x y z : List Nat) :
    Targets.listFlip (Targets.listOp x (Targets.listOp y z)) =
      Targets.listOp (Targets.listOp (Targets.listFlip z) (Targets.listFlip y))
        (Targets.listFlip x) :=
  reverseBlocks_replay _ _ [] List.append_nil List.reverse_reverse list_reverses x y z

theorem list_empty :
    Targets.listFlip (Targets.listOp [] (Targets.listOp [] [])) = [] := by
  calc
    _ = Targets.listOp (Targets.listOp (Targets.listFlip []) (Targets.listFlip []))
        (Targets.listFlip []) := list_reverseBlocks [] [] []
    _ = [] := rfl

theorem list_nonempty :
    Targets.listFlip (Targets.listOp [1, 2] (Targets.listOp [3] [4, 5])) =
      [5, 4, 3, 2, 1] := by
  calc
    _ = Targets.listOp (Targets.listOp (Targets.listFlip [4, 5]) (Targets.listFlip [3]))
        (Targets.listFlip [1, 2]) := list_reverseBlocks [1, 2] [3] [4, 5]
    _ = [5, 4, 3, 2, 1] := rfl

theorem bool_application :
    Targets.boolFlip (Targets.boolOp true (Targets.boolOp false true)) = false := by
  calc
    _ = Targets.boolOp (Targets.boolOp (Targets.boolFlip true) (Targets.boolFlip false))
        (Targets.boolFlip true) := bool_reverseBlocks true false true
    _ = false := rfl

theorem bad_conclusion :
    Targets.boolFlip (Targets.badOp true (Targets.badOp false false)) ≠
      Targets.badOp (Targets.badOp (Targets.boolFlip false) (Targets.boolFlip false))
        (Targets.boolFlip true) := by decide

theorem bad_obligation : ¬ ReversesOperation Targets.badOp Targets.boolFlip := by
  intro h
  have impossible := h true false
  change true = false at impossible
  cases impossible


universe v

/-- A carrier right unit suffices for selection under every observation. -/
def RightUnit {A : Type u} (m : A → A → A) (e : A) : Prop :=
  ∀ x, m x e = x

/-- Source dependency replay: symmetry, observer congruence, then subtype pairing. -/
def select {A : Type u} {B : Type v} (m : A → A → A) (e : A)
    (observe : A → B) (unit : RightUnit m e) (x : A) :
    { y : A // observe y = observe (m x e) } :=
  ⟨x, congrArg observe (unit x).symm⟩

theorem select_value {A : Type u} {B : Type v} (m : A → A → A) (e : A)
    (observe : A → B) (unit : RightUnit m e) (x : A) :
    (select m e observe unit x).val = x := rfl

theorem list_rightUnit : RightUnit Targets.listOp Targets.listUnit := by
  intro x
  exact List.append_nil x

theorem bool_rightUnit : RightUnit Targets.boolOp Targets.boolUnit := by
  intro x
  cases x <;> rfl

def listSelected (x : List Nat) :
    { y : List Nat // Targets.listObserve y =
      Targets.listObserve (Targets.listOp x Targets.listUnit) } :=
  select _ _ _ list_rightUnit x

def boolSelected (x : Bool) :
    { y : Bool // Targets.boolObserve y =
      Targets.boolObserve (Targets.boolOp x Targets.boolUnit) } :=
  select _ _ _ bool_rightUnit x

theorem listSelected_value (x : List Nat) : (listSelected x).val = x :=
  select_value _ _ _ list_rightUnit x

theorem boolSelected_value (x : Bool) : (boolSelected x).val = x :=
  select_value _ _ _ bool_rightUnit x

theorem listSelected_source (x : List Nat) : listSelected x = Source.selected x := by
  apply Subtype.ext
  exact listSelected_value x

theorem selected_empty : (listSelected []).val = [] := listSelected_value []

theorem selected_nonempty : (listSelected [1, 2]).val = [1, 2] :=
  listSelected_value [1, 2]

theorem selected_true : (boolSelected true).val = true := boolSelected_value true

/-- An inhabited fiber does not guarantee that it contains the supplied input. -/
def natWitness : { y : Nat // id y = id (Nat.add 0 1) } := ⟨1, rfl⟩

theorem nat_witness_exists : Nonempty { y : Nat // id y = id (Nat.add 0 1) } :=
  ⟨natWitness⟩

theorem nat_selection_impossible :
    ¬ ∃ w : { y : Nat // id y = id (Nat.add 0 1) }, w.val = 0 := by
  rintro ⟨w, hw⟩
  have hp := w.property
  change w.val = 1 at hp
  rw [hw] at hp
  cases hp

theorem nat_rightUnit_missing : ¬ RightUnit Nat.add 1 := by
  intro h
  have impossible := h 0
  change 1 = 0 at impossible
  cases impossible

/-- The observation-level consequence also fails in the Nat negative model. -/
theorem nat_observation_law_missing :
    ¬ (∀ x : Nat, id (Nat.add x 1) = id x) := by
  intro h
  have impossible := h 0
  change 1 = 0 at impossible
  cases impossible

def alternative :
    { y : List Nat // Targets.listObserve y =
      Targets.listObserve (Targets.listOp [1] Targets.listUnit) } :=
  ⟨[2], rfl⟩

theorem selected_alternative_differ : (listSelected [1]).val ≠ alternative.val := by
  decide

/-- Erasure to Prop cannot retain the projection of two distinct witnesses. -/
theorem no_projection_recovery {A : Type u} {P : A → Prop}
    (a b : { x : A // P x }) (different : a.val ≠ b.val) :
    ¬ ∃ recover : Nonempty { x : A // P x } → A,
      ∀ w : { x : A // P x }, recover ⟨w⟩ = w.val := by
  rintro ⟨recover, preserves⟩
  apply different
  calc
    a.val = recover ⟨a⟩ := (preserves a).symm
    _ = recover ⟨b⟩ := congrArg recover (Subsingleton.elim _ _)
    _ = b.val := preserves b

theorem list_erasure_no_recovery :
    ¬ ∃ recover :
      Nonempty { y : List Nat // Targets.listObserve y =
        Targets.listObserve (Targets.listOp [1] Targets.listUnit) } → List Nat,
      ∀ w : { y : List Nat // Targets.listObserve y =
        Targets.listObserve (Targets.listOp [1] Targets.listUnit) },
        recover ⟨w⟩ = w.val :=
  no_projection_recovery (listSelected [1]) alternative selected_alternative_differ

end ProofRequirementTrial.Assisted
