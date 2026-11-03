import Applications.Checking.OrderCertificate

/-! Checked uses of the experimental checker, including the boundary of its law. -/
namespace Examples.OrderCertificate
open _root_.OrderCertificate

def ltCmp (x y : Nat) : Bool := decide (x < y)

theorem lt_law (x y : Nat) : ltCmp x y = true ↔ x < y := by simp [ltCmp]

/-- The worked certificate has three increasing entries, not consecutive ranks. -/
theorem increasing : (checkedLengthSquare lt_law).impl [2, 5, 9] = some 3 := by
  apply (checkedLength_correct lt_law _).mpr
  decide

/-- A rejected duplicate cannot release a length. -/
theorem duplicate : (checkedLengthSquare lt_law).impl [2, 5, 5] = none := by rfl

theorem decreasing : adjacent ltCmp [9, 5, 2] = false := by decide

theorem empty : (checkedLengthSquare lt_law).impl [] = some 0 := by
  exact (checkedLength_correct lt_law []).mpr List.Pairwise.nil

theorem singleton : (checkedLengthSquare lt_law).impl [7] = some 1 := by
  apply (checkedLength_correct lt_law _).mpr
  decide

/-- Reusing the contract at a different relation permits equal neighboring entries. -/
theorem nonstrict :
    adjacent (fun x y : Nat => decide (x ≤ y)) [2, 2, 5] =
      reference (fun x y : Nat => decide (x ≤ y)) [2, 2, 5] :=
  refinement (R := (· ≤ ·)) (by intros; simp) _

/-- Adjacency is insufficient without transitivity: 0→1→2 skips the pair 0→2. -/
theorem nontransitive :
    adjacent (fun x y : Nat => decide (y = x + 1)) [0, 1, 2] = true ∧
    reference (fun x y : Nat => decide (y = x + 1)) [0, 1, 2] = false := by
  decide

/-- Acceptance gives a usable uniqueness fact to ordinary Lean consumers. -/
theorem accepted_nodup (xs : List Nat)
    (accepted : adjacent ltCmp xs = true) : xs.Nodup := by
  have hp : xs.Pairwise (· < ·) :=
    (reference_correct lt_law xs).mp ((refinement lt_law xs) ▸ accepted)
  exact hp.imp (fun h => Nat.ne_of_lt h)

end Examples.OrderCertificate
