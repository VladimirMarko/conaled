import Applications.Rendering.Response
import Applications.Probability.FiniteKernel
import Mathlib.Tactic

/-! Checked spatial observations and dependence-sensitive response composition. -/
namespace Examples.RenderingResponse
open Applications.Rendering Applications.Probability
open scoped BigOperators ENNReal
open MeasureTheory

abbrev ScalarResponse := Response ℚ ℚ

/-- Scalar physical interpretation for this example: emitted light is nonnegative,
transmission is between zero (opaque) and one (transparent). -/
def Admissible (r : ScalarResponse) : Prop :=
  0 ≤ r.emission ∧ 0 ≤ r.transmission ∧ r.transmission ≤ 1

theorem admissible_mul {a b : ScalarResponse} (ha : Admissible a) (hb : Admissible b) :
    Admissible (a * b) := by
  refine ⟨add_nonneg ha.1 (mul_nonneg ha.2.1 hb.1), mul_nonneg ha.2.1 hb.2.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left hb.2.2 ha.2.1).trans (by simpa using ha.2.2)

theorem eval_nonneg {r : ScalarResponse} (hr : Admissible r) {light : ℚ} (hl : 0 ≤ light) :
    0 ≤ r.eval light := add_nonneg hr.1 (mul_nonneg hr.2.1 hl)

theorem transparent (r : ScalarResponse) (light : ℚ) :
    (1 * r).eval light = r.eval light := by
  rw [Response.eval_mul, Response.eval_one]

theorem opaque_front (emission : ℚ) (back : ScalarResponse) (light : ℚ) :
    ((⟨emission, 0⟩ : ScalarResponse) * back).eval light = emission := by
  rw [Response.eval_mul]
  simp [Response.eval]

/-- Transparent transmission alone is not identity when emission is nonzero. -/
theorem transparent_emitting : (⟨2, 1⟩ : ScalarResponse).eval 3 = 5 := by
  norm_num [Response.eval]

theorem order_control :
    ((⟨2, 1/2⟩ : ScalarResponse) * ⟨3, 1/3⟩).eval 0 = 7/2 ∧
    ((⟨3, 1/3⟩ : ScalarResponse) * ⟨2, 1/2⟩).eval 0 = 11/3 := by
  constructor <;> rw [Response.eval_mul] <;> norm_num [Response.eval]

/-- Emission need not be scalar: the same law acts on a three-channel value. -/
theorem channels :
    ((⟨![1, 0, 2], 1/2⟩ : Response ℚ (Fin 3 → ℚ)) *
      ⟨![2, 4, 0], 1/3⟩).eval 0 = ![2, 2, 2] := by
  rw [Response.eval_mul]
  ext i
  fin_cases i <;> norm_num [Response.eval]

/-- Exact rational point samples. Geometry is needed only by this selected field. -/
abbrev Point (n : ℕ) := Fin n → ℚ

def radiusSquared {n : ℕ} (p : Point n) : ℚ := ∑ i, p i ^ 2

def front {n : ℕ} (p : Point n) : ScalarResponse := ⟨radiusSquared p, 1/2⟩
def back {n : ℕ} (p : Point n) : ScalarResponse := ⟨radiusSquared p + 1, 1/3⟩

theorem layers_admissible {n : ℕ} (p : Point n) :
    Admissible (front p) ∧ Admissible (back p) := by
  have h : 0 ≤ radiusSquared p := Finset.sum_nonneg fun i _ => sq_nonneg (p i)
  constructor <;> constructor
  · exact h
  · norm_num [front]
  · exact add_nonneg h (by norm_num)
  · norm_num [back]

/-- The observer chooses a point; no ray integration is claimed. -/
def sample {n : ℕ} (p : Point n) : ℚ :=
  Response.observe (front * back) id (fun _ => 0) p

theorem sample_eq {n : ℕ} (p : Point n) : sample p = 3/2 * radiusSquared p + 1/2 := by
  rw [sample, Response.observe_mul]
  simp [Response.observe, front, back, Response.eval]
  ring

theorem sample_two : sample ![1, 2] = 8 := by
  rw [sample_eq]
  norm_num [radiusSquared, Fin.sum_univ_succ]

theorem sample_two_changed : sample ![2, 2] = 25/2 := by
  rw [sample_eq]
  norm_num [radiusSquared, Fin.sum_univ_succ]

theorem sample_three : sample ![1, 2, 3] = 43/2 := by
  rw [sample_eq]
  norm_num [radiusSquared, Fin.sum_univ_succ]

/-- The third coordinate changes the actual observation. -/
theorem sample_three_changed : sample ![1, 2, 4] = 32 := by
  rw [sample_eq]
  norm_num [radiusSquared, Fin.sum_univ_succ]

/-- A nonidentity coordinate translation, in any finite dimension. -/
def shift (n : ℕ) : Point n ≃ Point n where
  toFun p i := p i + 1
  invFun p i := p i - 1
  left_inv p := by funext i; simp
  right_inv p := by funext i; simp

theorem shift_nonidentity : shift 3 (![0, 0, 0]) ≠ ![0, 0, 0] := by
  intro h
  have := congrFun h 0
  norm_num [shift] at this

/-- Both layers and the observer move; the incoming scalar is coordinate invariant. -/
theorem shifted_observation {n : ℕ} (query : ℚ → Point n) (incoming : ℚ → ℚ) :
    Response.observe (Response.reindex (shift n).symm front *
      Response.reindex (shift n).symm back) (shift n ∘ query) incoming =
      Response.observe (front * back) query incoming :=
  Response.observe_reindex_mul (shift n) front back query incoming

/-- A moving 3D query consumes the coordinate and composition theorem. -/
theorem shifted_three :
    Response.observe (Response.reindex (shift 3).symm front *
      Response.reindex (shift 3).symm back)
      (shift 3 ∘ (fun t : ℚ => ![1, 2, t])) (fun _ => 0) 3 = 43/2 := by
  rw [shifted_observation]
  exact sample_three

/-- Omitting the scene pullback really changes the selected observation. -/
theorem shift_query_only : sample (shift 3 ![1, 2, 3]) = 44 := by
  rw [sample_eq]
  norm_num [radiusSquared, shift, Fin.sum_univ_succ]

/-- Finite probability tables retain the joint sample, before applying the response. -/
def fair : Table Unit Bool where
  entry _ _ := 1/2
  nonneg _ _ := by norm_num
  sum_row _ := by norm_num [Fintype.sum_bool]

def shared : Table Unit (Bool × Bool) :=
  Table.comp (Table.deterministic fun b => (b, b)) fair

/-- Retain the first draw and append a fresh draw from `fair`. -/
def appendFair : Table Bool (Bool × Bool) where
  entry b p := if b = p.1 then fair.entry () p.2 else 0
  nonneg b p := by split <;> norm_num [fair]
  sum_row b := by cases b <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, fair]

def independent : Table Unit (Bool × Bool) := Table.comp appendFair fair

theorem shared_entry (b c : Bool) : shared.entry () (b, c) = if b = c then 1/2 else 0 := by
  cases b <;> cases c <;> norm_num [shared, Table.comp, Table.deterministic, fair,
    Fintype.sum_bool]

theorem independent_entry (b c : Bool) :
    independent.entry () (b, c) = fair.entry () b * fair.entry () c := by
  cases b <;> cases c <;> norm_num [independent, Table.comp, appendFair, fair,
    Fintype.sum_bool]

/-- Equal first and second marginals do not imply interchangeable joint observations. -/
theorem marginals (b : Bool) :
    (Table.comp (Table.deterministic Prod.fst) shared).entry () b = fair.entry () b ∧
    (Table.comp (Table.deterministic Prod.snd) shared).entry () b = fair.entry () b ∧
    (Table.comp (Table.deterministic Prod.fst) independent).entry () b = fair.entry () b ∧
    (Table.comp (Table.deterministic Prod.snd) independent).entry () b = fair.entry () b := by
  cases b <;> norm_num [Table.comp, Table.deterministic, Fintype.sum_prod_type,
    Fintype.sum_bool, shared_entry, independent_entry, fair]

def gate (b : Bool) : ScalarResponse := ⟨0, if b then 1 else 0⟩

theorem gate_admissible (b : Bool) : Admissible (gate b) := by
  cases b <;> norm_num [Admissible, gate]

/-- Unit incoming light measures combined transmission of the two zero-emission layers. -/
def transmitted (p : Bool × Bool) : ℚ := (gate p.1 * gate p.2).eval 1

theorem transmitted_eq (b c : Bool) : transmitted (b, c) = if b && c then 1 else 0 := by
  rw [transmitted, Response.eval_mul]
  cases b <;> cases c <;> norm_num [gate, Response.eval]

theorem transmitted_bounds (p : Bool × Bool) : 0 ≤ transmitted p ∧ transmitted p ≤ 1 := by
  rw [transmitted_eq]
  cases p.1 <;> cases p.2 <;> norm_num

/-- The unit-light observation is exactly the represented combined transmission. -/
theorem transmitted_eq_transmission (p : Bool × Bool) :
    transmitted p = (gate p.1 * gate p.2).transmission := by
  rw [transmitted_eq, Response.mul_transmission]
  cases p.1 <;> cases p.2 <;> norm_num [gate]

/-- Nonnegative expectation under the existing table-to-kernel interpretation. -/
noncomputable def expected (t : Table Unit (Bool × Bool)) : ℝ≥0∞ :=
  ∫⁻ p, mass (transmitted p) ∂t.kernel ()

theorem expected_shared : expected shared = 1/2 := by
  rw [expected, Table.lintegral_kernel]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, transmitted_eq, shared_entry,
    mass, ENNReal.ofReal_div_of_pos]

theorem expected_independent : expected independent = 1/4 := by
  rw [expected, Table.lintegral_kernel]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, transmitted_eq, independent_entry,
    fair, mass, ENNReal.ofReal_div_of_pos]

/-- Multiplying marginal expected transmissions loses the shared draw's dependence. -/
theorem dependence_matters : expected shared ≠ expected independent := by
  rw [expected_shared, expected_independent]
  norm_num

end Examples.RenderingResponse
