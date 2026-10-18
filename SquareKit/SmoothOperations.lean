import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Experimental finite-arity smooth operations, shared by model constructions and AD. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothAlgebra

abbrev Operation (n : ℕ) := {f : (Fin n → ℝ) → ℝ // ContDiff ℝ ∞ f}

def projection {n : ℕ} (i : Fin n) : Operation n :=
  ⟨fun x => x i, contDiff_apply ℝ (fun _ => ℝ) i⟩
def constant (n : ℕ) (a : ℝ) : Operation n := ⟨fun _ => a, contDiff_const⟩
def substitute {m n : ℕ} (f : Operation n) (g : Fin n → Operation m) : Operation m :=
  ⟨fun x => f.val (fun i => (g i).val x),
    f.property.comp (contDiff_pi.mpr (fun i => (g i).property))⟩
def addition : Operation 2 :=
  ⟨fun x => x 0 + x 1, (contDiff_apply ℝ (fun _ => ℝ) 0).add (contDiff_apply ℝ (fun _ => ℝ) 1)⟩
def multiplication : Operation 2 :=
  ⟨fun x => x 0 * x 1, (contDiff_apply ℝ (fun _ => ℝ) 0).mul (contDiff_apply ℝ (fun _ => ℝ) 1)⟩

end SquareKit.SmoothAlgebra
