import SquareKit.UnaryInteraction

namespace Examples.UnaryInteraction
open SquareKit.CommutingOperations SquareKit.UnaryInteraction

def involution : Presentation Unit := ⟨Unit, fun _ => [(), ()], fun _ => []⟩
def idempotent : Presentation Unit := ⟨Unit, fun _ => [(), ()], fun _ => [()]⟩

theorem flip_valid : Valid involution onLeft := fun _ x => left_involution x
theorem reset_valid : Valid idempotent onRight := fun _ x => right_idempotent x
theorem copy_valid : Valid idempotent copyLeft := fun _ x => copy_idempotent x

def joint : SquareKit.GuardedTheory.Model (guarded (tensor involution idempotent)) :=
  model _ (Sum.elim onLeft onRight)
    ((tensor_valid_iff _ _ _ _).mpr ⟨flip_valid, reset_valid, independent_interchange⟩)

/-- The changed operation is still admitted by the sum of the own theories. -/
def changedSum : SquareKit.GuardedTheory.Model (guarded (union involution idempotent)) :=
  model _ (Sum.elim onLeft copyLeft) (union_valid _ _ _ _ flip_valid copy_valid)

theorem changed_tensor_rejected : ¬ Valid (tensor involution idempotent)
    (Sum.elim onLeft copyLeft) := by
  intro h
  exact changed_mixed_law_fails ((tensor_valid_iff _ _ _ _).mp h).2.2

/-- Arbitrarily interleaved words are interpreted through both representations. -/
theorem all_words (w : List (Unit ⊕ Unit)) (p : Bool × Bool) :
    (term w).eval joint.toAlgebra (fun _ => p) =
      interpret onLeft onRight (split w) p :=
  comparison onLeft onRight independent_interchange w (fun _ => p)

/-- Two flips cancel while the reset remains, regardless of interleaving. -/
theorem interleaved :
    (term [Sum.inl (), Sum.inr (), Sum.inl ()]).eval joint.toAlgebra
      (fun _ => (true, true)) = (true, false) := by
  rw [all_words]
  rfl

theorem two_blocks (a b : List Unit × List Unit) (p : Bool × Bool) :
    interpret onLeft onRight (a.1 ++ b.1, a.2 ++ b.2) p =
      interpret onLeft onRight a (interpret onLeft onRight b p) :=
  interpret_product onLeft onRight independent_interchange a b p

/-- Reusing the same reordering with copy-left changes an observable result. -/
theorem changed_normalization_fails :
    run (Sum.elim onLeft copyLeft) [Sum.inr (), Sum.inl ()] (false, false) ≠
      interpret onLeft copyLeft (split [Sum.inr (), Sum.inl ()]) (false, false) := by
  decide

end Examples.UnaryInteraction
