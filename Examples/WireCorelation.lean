import SquareKit.WireCorelation

namespace Examples.WireCorelation
open SquareKit.WireCorelation
open SquareKit.OpenConstraint (behavior)

/-- Two terminals share false; true is an orphan internal node. -/
def joined : Cospan Unit Unit := ⟨Bool, fun _ => false, fun _ => false⟩

theorem joined_behavior (a b : Unit → Bool) :
    behavior (network joined) a b ↔ a () = b () := by
  rw [exact_blackbox]
  constructor
  · intro h; exact h (.inl ()) (.inr ()) rfl
  · intro h x y he
    cases x with
    | inl x => cases y with
      | inl y => rfl
      | inr y => exact h
    | inr x => cases y with
      | inl y => exact h.symm
      | inr y => rfl

/-- The new quotient construction is exercised through the exact comparison. -/
theorem composed_joined (a b : Unit → Bool) :
    behavior (network (reduce (compose (reduce joined) (reduce joined)))) a b ↔
      a () = b () := by
  rw [reduced_composition, SquareKit.OpenConstraint.behavior_compose]
  simp only [joined_behavior]
  constructor
  · rintro ⟨c, h, k⟩; exact h.trans k
  · intro h; exact ⟨a, rfl, h⟩

theorem rejects_disagreement :
    ¬ behavior (network (reduce (compose (reduce joined) (reduce joined))))
      (fun _ => false) (fun _ => true) := by
  rw [composed_joined]
  decide

/-- Empty boundary but an orphan node: an empty color domain cannot fill it. -/
def orphan : Cospan Empty Empty := ⟨Unit, Empty.elim, Empty.elim⟩

theorem orphan_no_empty_coloring :
    ¬ behavior (network orphan) (Empty.elim : Empty → Empty) Empty.elim := by
  rintro ⟨v, _⟩
  exact (v ()).elim

theorem reduced_orphan_has_empty_coloring :
    behavior (network (reduce orphan)) (Empty.elim : Empty → Empty) Empty.elim := by
  refine ⟨?_, fun x => x.elim, fun x => x.elim⟩
  intro z
  apply False.elim
  obtain ⟨x, _⟩ := z.property
  cases x with
  | inl x => exact x.elim
  | inr x => exact x.elim

end Examples.WireCorelation
