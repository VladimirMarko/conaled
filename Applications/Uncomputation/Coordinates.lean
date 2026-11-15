import Applications.Uncomputation.Finite
import Applications.Linear.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Coordinates in the delta basis, orthonormal for `pairing`. Product basis
indices implement tensor composition; coordinate sums in MatrixBackend's
cartesian clients have a different meaning. -/
namespace Uncomputation
open scoped Kronecker

noncomputable def coordinates {A B : Type} [Fintype A] [DecidableEq A]
    (e : A ≃ B) : Matrix B A ℂ := LinearMap.toMatrix' (coherent e)

theorem coordinates_decode {A B : Type} [Fintype A] [DecidableEq A]
    (e : A ≃ B) : Matrix.toLin' (coordinates e) = coherent e :=
  Matrix.toLin'_toMatrix' _

theorem coordinates_entry {A B : Type} [Fintype A] [DecidableEq A]
    (e : A ≃ B) (b : B) (a : A) :
    coordinates e b a = if e.symm b = a then 1 else 0 := by
  simp [coordinates, LinearMap.toMatrix'_apply, Pi.single_apply, eq_comm]

theorem coordinates_comp {A B D : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (f : B ≃ D) :
    coordinates (e.trans f) = coordinates f * coordinates e :=
  by simpa only [coordinates, coherent_comp] using LinearMap.toMatrix'_comp (coherent f) (coherent e)

theorem coordinates_identity {A : Type} [Fintype A] [DecidableEq A] :
    coordinates (Equiv.refl A) = 1 := by
  simp [coordinates]

theorem coordinates_tensor {A B D E : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (e : A ≃ B) (f : D ≃ E) :
    coordinates (Equiv.prodCongr e f) = coordinates e ⊗ₖ coordinates f := by
  ext ⟨b, z⟩ ⟨a, d⟩
  simp only [coordinates_entry, Matrix.kronecker_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply]
  split_ifs <;> simp_all

theorem coordinates_adjoint {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) :
    coordinates e.symm = (coordinates e).conjTranspose := by
  ext a b
  simp only [coordinates_entry, Matrix.conjTranspose_apply, Equiv.symm_symm]
  have h : e a = b ↔ e.symm b = a := by
    constructor <;> intro h
    · rw [← h]; simp
    · rw [← h]; simp
  by_cases he : e a = b <;> simp_all

theorem coordinates_unitary {A : Type} [Fintype A] [DecidableEq A]
    (e : A ≃ A) : (coordinates e).conjTranspose * coordinates e = 1 := by
  rw [← coordinates_adjoint, ← coordinates_comp]
  simpa using (coordinates_identity (A := A))

end Uncomputation
