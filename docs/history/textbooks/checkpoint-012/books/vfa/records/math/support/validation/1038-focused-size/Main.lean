import Mathlib.Data.Nat.Size

-- Source-extracted reproduction of the previously failing example.
-- This focused check does not validate the entire project or replace any gate.
example : ¬ ∃ bound : Nat, ∀ n : Nat, n.size ≤ bound := by
  rintro ⟨bound,h⟩
  have large := h (2^bound)
  rw [Nat.size_pow] at large
  omega
