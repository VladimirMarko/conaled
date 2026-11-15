import Applications.Orbifold.Lorentz
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv

/-! Coordinates with an actual even-Clifford realization. The augmented form
uses ((x,y),t); the timelike coordinate is last in this product representation. -/
noncomputable section
open Matrix CliffordAlgebra
namespace Orbifold.Clifford

abbrev Plane := ℝ × ℝ

def positive : QuadraticForm ℝ Plane :=
  (QuadraticMap.sq (R := ℝ)).prod (QuadraticMap.sq (R := ℝ))

abbrev form := CliffordAlgebra.EquivEven.Q' positive
abbrev Algebra := CliffordAlgebra form
abbrev PlaneAlgebra := CliffordAlgebra positive

@[simp] theorem positive_apply (v : Plane) : positive v = v.1*v.1 + v.2*v.2 := by
  simp [positive, QuadraticMap.sq_apply]

@[simp] theorem form_apply (v : Plane × ℝ) : form v = v.1.1*v.1.1 + v.1.2*v.1.2 - v.2*v.2 := by
  rw [CliffordAlgebra.EquivEven.Q'_apply, positive_apply]

/-- Timelike generator, square -1. -/
def e0 : Algebra := CliffordAlgebra.EquivEven.e0 positive
def e1 : Algebra := CliffordAlgebra.EquivEven.v positive (1,0)
def e2 : Algebra := CliffordAlgebra.EquivEven.v positive (0,1)

@[simp] theorem e0_sq : e0 * e0 = -1 := CliffordAlgebra.EquivEven.e0_mul_e0 positive
@[simp] theorem e1_sq : e1 * e1 = 1 := by
  simpa [e1] using CliffordAlgebra.EquivEven.v_sq_scalar positive (1,0)
@[simp] theorem e2_sq : e2 * e2 = 1 := by
  simpa [e2] using CliffordAlgebra.EquivEven.v_sq_scalar positive (0,1)

private def b : PlaneAlgebra := ι positive (1,0)
private def c : PlaneAlgebra := ι positive (0,1)

@[simp] private theorem b_sq : b*b = 1 := by simp [b]
@[simp] private theorem c_sq : c*c = 1 := by simp [c]
private theorem cb : c*b = -(b*c) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := positive) (0,1) (1,0)
  have hz : c*b + b*c = 0 := by simpa [b,c,QuadraticMap.polar] using h
  exact eq_neg_of_add_eq_zero_left hz

/-- Four coordinates; their realization is proved injective below. -/
@[ext] structure Coordinates where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def smallValue (r : Coordinates) : PlaneAlgebra :=
  r.a • 1 + r.b • b + r.c • c + r.d • (b*c)

/-- An actual element of the even subalgebra, via Mathlib's algebra equivalence. -/
def evenValue (r : Coordinates) : CliffordAlgebra.even form :=
  CliffordAlgebra.equivEven positive (smallValue r)

def value (r : Coordinates) : Algebra := evenValue r

private def pauli : Plane →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun v := !![v.1,v.2; v.2,-v.1]
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp; ring
  map_smul' a v := by ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem pauli_sq (v : Plane) :
    pauli v * pauli v = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (positive v) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;> ring

private def pauliRepresentation : PlaneAlgebra →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  CliffordAlgebra.lift positive ⟨pauli, pauli_sq⟩

private theorem pauli_smallValue (r : Coordinates) :
    pauliRepresentation (smallValue r) = !![r.a+r.b,r.c+r.d; r.c-r.d,r.a-r.b] := by
  simp only [smallValue, map_add, map_smul, map_one, map_mul]
  simp only [pauliRepresentation, b, c, CliffordAlgebra.lift_ι_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli] <;> ring

theorem smallValue_injective : Function.Injective smallValue := by
  intro r s h
  have hm := congrArg pauliRepresentation h
  rw [pauli_smallValue, pauli_smallValue] at hm
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hm
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hm
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hm
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hm
  simp at h00 h01 h10 h11
  ext <;> linarith

theorem value_injective : Function.Injective value := by
  intro r s h
  apply smallValue_injective
  apply (CliffordAlgebra.equivEven positive).injective
  exact Subtype.ext h

def product (r s : Coordinates) : Coordinates :=
  ⟨r.a*s.a+r.b*s.b+r.c*s.c-r.d*s.d,
   r.a*s.b+r.b*s.a-r.c*s.d+r.d*s.c,
   r.a*s.c+r.c*s.a+r.b*s.d-r.d*s.b,
   r.a*s.d+r.d*s.a+r.b*s.c-r.c*s.b⟩

private theorem b_bc : b*(b*c) = c := by rw [← mul_assoc, b_sq, one_mul]
private theorem c_bc : c*(b*c) = -b := by
  rw [← mul_assoc, cb, neg_mul, mul_assoc, c_sq, mul_one]
private theorem bc_b : (b*c)*b = -c := by
  rw [mul_assoc, cb, mul_neg, b_bc]
private theorem bc_c : (b*c)*c = b := by rw [mul_assoc, c_sq, mul_one]
private theorem bc_bc : (b*c)*(b*c) = -1 := by
  rw [← mul_assoc, bc_b, neg_mul, c_sq]

theorem smallValue_product (r s : Coordinates) :
    smallValue (product r s) = smallValue r * smallValue s := by
  simp only [smallValue, product, add_mul, mul_add, smul_mul_smul_comm,
    one_mul, mul_one, b_sq, c_sq, cb, b_bc, c_bc, bc_b, bc_c, bc_bc,
    smul_neg]
  module

theorem value_product (r s : Coordinates) :
    value (product r s) = value r * value s := by
  change ((CliffordAlgebra.equivEven positive (smallValue (product r s)) :
    CliffordAlgebra.even form) : Algebra) = _
  rw [smallValue_product, map_mul]
  rfl

theorem product_assoc (r s t : Coordinates) : product (product r s) t = product r (product s t) := by
  apply value_injective
  simp only [value_product, mul_assoc]

def reversed (r : Coordinates) : Coordinates := ⟨r.a,-r.b,-r.c,-r.d⟩
def twisted (r : Coordinates) : Coordinates := ⟨r.a,-r.b,-r.c,r.d⟩
def scalar (a : ℝ) : Coordinates := ⟨a,0,0,0⟩
def norm (r : Coordinates) : ℝ := r.a^2 + r.d^2 - r.b^2 - r.c^2

@[simp] theorem value_scalar (a : ℝ) : value (scalar a) = a • (1 : Algebra) := by
  simp [value, evenValue, scalar, smallValue]

theorem product_reversed (r : Coordinates) : product r (reversed r) = scalar (norm r) := by
  ext <;> simp [product, reversed, scalar, norm] <;> ring

theorem reversed_product (r : Coordinates) : product (reversed r) r = scalar (norm r) := by
  ext <;> simp [product, reversed, scalar, norm] <;> ring

theorem norm_product (r s : Coordinates) : norm (product r s) = norm r * norm s := by
  simp [norm, product]; ring

theorem value_expansion (r : Coordinates) :
    value r = r.a • 1 + r.b • (e0*e1) + r.c • (e0*e2) + r.d • (e1*e2) := by
  change ((CliffordAlgebra.toEven positive (smallValue r) :
    CliffordAlgebra.even form) : Algebra) = _
  simp only [smallValue, map_add, map_smul, map_one, map_mul,
    Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_one,
    Subalgebra.coe_mul, b, c, CliffordAlgebra.toEven_ι]
  congr 2
  rw [← mul_assoc, CliffordAlgebra.EquivEven.e0_mul_v_mul_e0]
  rfl

private theorem e10 : e1*e0 = -(e0*e1) :=
  (CliffordAlgebra.EquivEven.neg_e0_mul_v positive (1,0)).symm
private theorem e20 : e2*e0 = -(e0*e2) :=
  (CliffordAlgebra.EquivEven.neg_e0_mul_v positive (0,1)).symm
private theorem e21 : e2*e1 = -(e1*e2) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := form) ((0,1),0) ((1,0),0)
  have hz : e2*e1 + e1*e2 = 0 := by
    simpa [e1,e2,CliffordAlgebra.EquivEven.v,QuadraticMap.polar] using h
  exact eq_neg_of_add_eq_zero_left hz

theorem value_reversed (r : Coordinates) : value (reversed r) = CliffordAlgebra.reverse (value r) := by
  simp only [value_expansion, reversed, map_add, map_smul,
    CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_one]
  simp only [e0, e1, e2, CliffordAlgebra.EquivEven.reverse_e0,
    CliffordAlgebra.EquivEven.reverse_v]
  change _ = r.a • 1 + r.b • (e1*e0) + r.c • (e2*e0) + r.d • (e2*e1)
  rw [e10,e20,e21]
  simp [e0,e1,e2]

theorem e0_value (r : Coordinates) : e0 * value r = value (twisted r) * e0 := by
  simp only [value_expansion, twisted, mul_add, add_mul, mul_smul_comm,
    smul_mul_assoc, mul_one, one_mul, neg_smul]
  have h1 : e0*(e0*e1) = -e1 := by rw [← mul_assoc, e0_sq, neg_one_mul]
  have h2 : e0*(e0*e2) = -e2 := by rw [← mul_assoc, e0_sq, neg_one_mul]
  have h3 : (e0*e1)*e0 = e1 := by
    exact CliffordAlgebra.EquivEven.e0_mul_v_mul_e0 positive (1,0)
  have h4 : (e0*e2)*e0 = e2 := by
    exact CliffordAlgebra.EquivEven.e0_mul_v_mul_e0 positive (0,1)
  have h5 : (e1*e2)*e0 = e0*(e1*e2) := by
    rw [mul_assoc, e20, mul_neg, ← mul_assoc, e10, neg_mul, neg_neg, mul_assoc]
  simp only [neg_mul, smul_mul_assoc, h1,h2,h3,h4,h5,smul_neg]

/-- Time-first vectors are reindexed into Mathlib's space-first augmented form. -/
def primal (X : Lorentz.Vector) : Algebra := ι form ((X 1, X 2), X 0)
def vectorCoordinates (X : Lorentz.Vector) : Coordinates := ⟨X 0,X 1,X 2,0⟩

theorem primal_eq (X : Lorentz.Vector) : primal X = value (vectorCoordinates X) * e0 := by
  have hv : CliffordAlgebra.EquivEven.v positive (X 1, X 2) = X 1 • e1 + X 2 • e2 := by
    change CliffordAlgebra.EquivEven.v positive (X 1, X 2) =
      X 1 • CliffordAlgebra.EquivEven.v positive (1,0) +
      X 2 • CliffordAlgebra.EquivEven.v positive (0,1)
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [primal, CliffordAlgebra.EquivEven.ι_eq_v_add_smul_e0, hv, value_expansion]
  simp only [vectorCoordinates, zero_smul, add_zero, add_mul, smul_mul_assoc, one_mul]
  have h1 : (e0*e1)*e0 = e1 := CliffordAlgebra.EquivEven.e0_mul_v_mul_e0 positive (1,0)
  have h2 : (e0*e2)*e0 = e2 := CliffordAlgebra.EquivEven.e0_mul_v_mul_e0 positive (0,1)
  rw [h1,h2]
  change X 1 • e1 + X 2 • e2 + X 0 • e0 = _
  abel

/-- Independently calculated coefficients of actual Clifford conjugation. -/
def sandwichMatrix (r : Coordinates) : Lorentz.Matrix3 :=
  !![r.a^2+r.b^2+r.c^2+r.d^2, 2*(r.a*r.b-r.c*r.d), 2*(r.a*r.c+r.b*r.d);
     2*(r.a*r.b+r.c*r.d), r.a^2+r.b^2-r.c^2-r.d^2, 2*(r.b*r.c+r.a*r.d);
     2*(r.a*r.c-r.b*r.d), 2*(r.b*r.c-r.a*r.d), r.a^2-r.b^2+r.c^2-r.d^2]

theorem sandwich_coordinates (r : Coordinates) (X : Lorentz.Vector) :
    product (product r (vectorCoordinates X)) (twisted (reversed r)) =
      vectorCoordinates (sandwichMatrix r *ᵥ X) := by
  ext <;> simp [product, vectorCoordinates, twisted, reversed, sandwichMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem sandwich_primal (r : Coordinates) (X : Lorentz.Vector) :
    value r * primal X * CliffordAlgebra.reverse (value r) =
      primal (sandwichMatrix r *ᵥ X) := by
  rw [primal_eq, ← value_reversed, mul_assoc, mul_assoc, e0_value,
    ← mul_assoc (value (vectorCoordinates X)), ← mul_assoc,
    ← value_product, ← value_product, ← product_assoc, sandwich_coordinates, ← primal_eq]

end Orbifold.Clifford
