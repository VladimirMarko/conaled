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

end ProofRequirementTrial.Assisted
