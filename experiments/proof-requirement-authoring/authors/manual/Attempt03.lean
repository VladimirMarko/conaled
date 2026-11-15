import Examples.ProofRequirementSupport

namespace ProofRequirementTrial.Manual

universe u

/-- A two-input law sufficient for reversing three blocks. -/
structure ReversalRequirements {A : Type u} (m : A → A → A) (f : A → A) : Prop where
  reverse_op : ∀ x y, f (m x y) = m (f y) (f x)

/-- Requirements actually used by the original proof body. -/
structure OriginalReversalRequirements {A : Type u} (m : A → A → A) (f : A → A)
    : Prop extends ReversalRequirements m f where
  involutive : ∀ x, f (f x) = x

/-- Replay includes the unused source ambient law as a separate parameter. -/
theorem reverseBlocks_original {A : Type u} (m : A → A → A) (f : A → A)
    (e : A) (_ambient : ∀ t, m t e = t) (h : OriginalReversalRequirements m f)
    (x y z : A) : f (m x (m y z)) = m (m (f z) (f y)) (f x) := by
  calc
    f (m x (m y z)) = f (m (f (f x)) (m y z)) :=
      congrArg (fun t => f (m t (m y z))) (h.involutive x).symm
    _ = f (m x (m y z)) :=
      congrArg (fun t => f (m t (m y z))) (h.involutive x)
    _ = m (f (m y z)) (f x) := h.reverse_op x (m y z)
    _ = m (m (f z) (f y)) (f x) :=
      congrArg (fun t => m t (f x)) (h.reverse_op y z)

/-- Removing the canceling involution steps removes that requirement. -/
theorem reverseBlocks {A : Type u} {m : A → A → A} {f : A → A}
    (h : ReversalRequirements m f) (x y z : A) :
    f (m x (m y z)) = m (m (f z) (f y)) (f x) := by
  calc
    f (m x (m y z)) = m (f (m y z)) (f x) := h.reverse_op x (m y z)
    _ = m (m (f z) (f y)) (f x) :=
      congrArg (fun t => m t (f x)) (h.reverse_op y z)

theorem listReversal : ReversalRequirements Targets.listOp Targets.listFlip where
  reverse_op := fun _ _ => List.reverse_append

theorem listOriginalReversal : OriginalReversalRequirements Targets.listOp Targets.listFlip where
  toReversalRequirements := listReversal
  involutive := List.reverse_reverse

theorem boolReversal : ReversalRequirements Targets.boolOp Targets.boolFlip where
  reverse_op := by intro x y; cases x <;> cases y <;> rfl

theorem boolOriginalReversal : OriginalReversalRequirements Targets.boolOp Targets.boolFlip where
  toReversalRequirements := boolReversal
  involutive := by intro x; rfl

theorem list_original_replay (x y z : List Nat) :
    Targets.listFlip (Targets.listOp x (Targets.listOp y z)) =
      Targets.listOp (Targets.listOp (Targets.listFlip z) (Targets.listFlip y))
        (Targets.listFlip x) :=
  reverseBlocks_original _ _ [] List.append_nil listOriginalReversal x y z

theorem bool_original_replay (x y z : Bool) :
    Targets.boolFlip (Targets.boolOp x (Targets.boolOp y z)) =
      Targets.boolOp (Targets.boolOp (Targets.boolFlip z) (Targets.boolFlip y))
        (Targets.boolFlip x) :=
  reverseBlocks_original _ _ false (by intro t; cases t <;> rfl) boolOriginalReversal x y z

theorem list_reverseBlocks (x y z : List Nat) :
    Targets.listFlip (Targets.listOp x (Targets.listOp y z)) =
      Targets.listOp (Targets.listOp (Targets.listFlip z) (Targets.listFlip y))
        (Targets.listFlip x) := reverseBlocks listReversal x y z

theorem bool_reverseBlocks (x y z : Bool) :
    Targets.boolFlip (Targets.boolOp x (Targets.boolOp y z)) =
      Targets.boolOp (Targets.boolOp (Targets.boolFlip z) (Targets.boolFlip y))
        (Targets.boolFlip x) := reverseBlocks boolReversal x y z

theorem list_empty :
    Targets.listFlip (Targets.listOp [] (Targets.listOp [] [])) = [] := by
  exact list_reverseBlocks [] [] []

theorem list_nonempty :
    Targets.listFlip (Targets.listOp [1,2] (Targets.listOp [3] [4,5])) = [5,4,3,2,1] := by
  calc
    _ = Targets.listOp (Targets.listOp (Targets.listFlip [4,5]) (Targets.listFlip [3]))
      (Targets.listFlip [1,2]) := list_reverseBlocks [1,2] [3] [4,5]
    _ = [5,4,3,2,1] := rfl

theorem bool_application :
    Targets.boolFlip (Targets.boolOp true (Targets.boolOp false true)) = false := by
  exact bool_reverseBlocks true false true

theorem bad_target_failure :
    Targets.boolFlip (Targets.badOp true (Targets.badOp false false)) ≠
      Targets.badOp (Targets.badOp (Targets.boolFlip false) (Targets.boolFlip false))
        (Targets.boolFlip true) := by decide

theorem bad_reverse_op_failure :
    Targets.boolFlip (Targets.badOp true false) ≠
      Targets.badOp (Targets.boolFlip false) (Targets.boolFlip true) := by decide

theorem bad_requirements_impossible : ¬ ReversalRequirements Targets.badOp Targets.boolFlip := by
  intro h
  exact bad_reverse_op_failure (h.reverse_op true false)


universe v

/-- The source construction uses equality before observing. -/
def RightUnit {A : Type u} (m : A → A → A) (e : A) : Prop := ∀ x, m x e = x

/-- The selected input only requires equality after observing. -/
def ObservedRightUnit {A : Type u} {B : Type v}
    (m : A → A → A) (e : A) (observe : A → B) : Prop :=
  ∀ x, observe (m x e) = observe x

theorem observedRightUnit_of_rightUnit {A : Type u} {B : Type v}
    {m : A → A → A} {e : A} (observe : A → B) (h : RightUnit m e) :
    ObservedRightUnit m e observe := fun x => congrArg observe (h x)

/-- Original source proof, with its right-unit dependency retained. -/
def selected_original {A : Type u} {B : Type v}
    {m : A → A → A} {e : A} (observe : A → B) (h : RightUnit m e) (x : A) :
    {y : A // observe y = observe (m x e)} :=
  ⟨x, congrArg observe (h x).symm⟩

theorem selected_original_value {A : Type u} {B : Type v}
    {m : A → A → A} {e : A} (observe : A → B) (h : RightUnit m e) (x : A) :
    (selected_original observe h x).val = x := rfl

/-- This construction retains the supplied input as data. -/
def selected {A : Type u} {B : Type v}
    {m : A → A → A} {e : A} {observe : A → B}
    (h : ObservedRightUnit m e observe) (x : A) :
    {y : A // observe y = observe (m x e)} := ⟨x, (h x).symm⟩

theorem selected_value {A : Type u} {B : Type v}
    {m : A → A → A} {e : A} {observe : A → B}
    (h : ObservedRightUnit m e observe) (x : A) : (selected h x).val = x := rfl

/-- Weakening requirements preserves the entire subtype value. -/
theorem selected_agrees_original {A : Type u} {B : Type v}
    {m : A → A → A} {e : A} (observe : A → B) (h : RightUnit m e) (x : A) :
    selected (observedRightUnit_of_rightUnit observe h) x = selected_original observe h x := by
  apply Subtype.ext
  rfl

theorem listRightUnit : RightUnit Targets.listOp Targets.listUnit := List.append_nil

theorem boolRightUnit : RightUnit Targets.boolOp Targets.boolUnit := by
  intro x
  cases x <;> rfl

theorem listObservedRightUnit :
    ObservedRightUnit Targets.listOp Targets.listUnit Targets.listObserve :=
  observedRightUnit_of_rightUnit Targets.listObserve listRightUnit

theorem boolObservedRightUnit :
    ObservedRightUnit Targets.boolOp Targets.boolUnit Targets.boolObserve :=
  observedRightUnit_of_rightUnit Targets.boolObserve boolRightUnit

def selectedList (x : List Nat) :
    {y : List Nat // Targets.listObserve y =
      Targets.listObserve (Targets.listOp x Targets.listUnit)} :=
  selected listObservedRightUnit x

def selectedBool (x : Bool) :
    {y : Bool // Targets.boolObserve y =
      Targets.boolObserve (Targets.boolOp x Targets.boolUnit)} :=
  selected boolObservedRightUnit x

theorem selectedList_value (x : List Nat) : (selectedList x).val = x :=
  selected_value listObservedRightUnit x

theorem selectedBool_value (x : Bool) : (selectedBool x).val = x :=
  selected_value boolObservedRightUnit x

theorem list_selected_original_replay (x : List Nat) :
    selected_original Targets.listObserve listRightUnit x = Source.selected x := by
  apply Subtype.ext
  rfl

theorem selectedList_eq_source (x : List Nat) : selectedList x = Source.selected x := by
  apply Subtype.ext
  exact selectedList_value x

theorem bool_selected_original_replay (x : Bool) :
    (selected_original Targets.boolObserve boolRightUnit x).val = x :=
  selected_original_value Targets.boolObserve boolRightUnit x

theorem selectedList_empty : (selectedList []).val = [] := selectedList_value []
theorem selectedList_nonempty : (selectedList [1,2]).val = [1,2] := selectedList_value [1,2]
theorem selectedBool_true : (selectedBool true).val = true := selectedBool_value true

/-- A fiber is inhabited even though it cannot contain the requested input. -/
def natAlternative : {y : Nat // id y = id (Nat.add 0 1)} := ⟨1, rfl⟩

theorem nat_witness_exists : Nonempty {y : Nat // id y = id (Nat.add 0 1)} :=
  ⟨natAlternative⟩

theorem nat_selection_impossible :
    ¬ ∃ y : {y : Nat // id y = id (Nat.add 0 1)}, y.val = 0 := by
  intro ⟨y, hy⟩
  have hp : y.val = 1 := y.property
  rw [hy] at hp
  cases hp

theorem nat_observed_right_unit_missing : ¬ ObservedRightUnit Nat.add 1 id := by
  intro h
  have hp : 1 = 0 := h 0
  cases hp

/-- The two list witnesses live in exactly the same fiber. -/
def listAlternative :
    {y : List Nat // Targets.listObserve y =
      Targets.listObserve (Targets.listOp [1] Targets.listUnit)} := ⟨[2], rfl⟩

theorem list_witness_values_differ : (selectedList [1]).val ≠ listAlternative.val := by
  decide

theorem erased_witnesses_equal :
    (⟨selectedList [1]⟩ : Nonempty {y : List Nat // Targets.listObserve y =
      Targets.listObserve (Targets.listOp [1] Targets.listUnit)}) = ⟨listAlternative⟩ := rfl

/-- No function of the erased evidence recovers every original witness value. -/
theorem no_recovery_from_nonempty :
    ¬ ∃ recover :
      Nonempty {y : List Nat // Targets.listObserve y =
        Targets.listObserve (Targets.listOp [1] Targets.listUnit)} → List Nat,
      ∀ y : {y : List Nat // Targets.listObserve y =
        Targets.listObserve (Targets.listOp [1] Targets.listUnit)},
        recover ⟨y⟩ = y.val := by
  intro ⟨recover, h⟩
  have hselected := h (selectedList [1])
  have halternative := h listAlternative
  exact list_witness_values_differ (hselected.symm.trans halternative)

end ProofRequirementTrial.Manual
