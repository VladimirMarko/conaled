import Examples.ProofRequirementSupport

namespace ProofRequirementTrial.Manual

universe u

/-- A two-input law sufficient for reversing three blocks. -/
structure ReversalRequirements {A : Type u} (m : A → A → A) (f : A → A) : Prop where
  reverse_op : ∀ x y, f (m x y) = m (f y) (f x)

/-- Requirements actually used by the original proof body. -/
structure OriginalReversalRequirements {A : Type u} (m : A → A → A) (f : A → A)
    extends ReversalRequirements m f : Prop where
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

def listReversal : ReversalRequirements Targets.listOp Targets.listFlip where
  reverse_op := fun _ _ => List.reverse_append

def listOriginalReversal : OriginalReversalRequirements Targets.listOp Targets.listFlip where
  toReversalRequirements := listReversal
  involutive := List.reverse_reverse

def boolReversal : ReversalRequirements Targets.boolOp Targets.boolFlip where
  reverse_op := by intro x y; cases x <;> cases y <;> rfl

def boolOriginalReversal : OriginalReversalRequirements Targets.boolOp Targets.boolFlip where
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

end ProofRequirementTrial.Manual
