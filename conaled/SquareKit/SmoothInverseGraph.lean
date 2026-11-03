import SquareKit.SmoothLocalGluing
import SquareKit.SmoothHadamard

/-! Experimental analytic extension and divisibility on the inverse graph.
Local solutions are glued by the finite-dimensional smooth partition of unity. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace SquareKit.SmoothInverseGraph
variable {n : ℕ}

def base (z : Fin (n+1) → ℝ) : Fin n → ℝ := fun i => z i.castSucc
def graph (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.snoc x (f x)⁻¹
def relation (f : (Fin n → ℝ) → ℝ) (z : Fin (n+1) → ℝ) : ℝ := f (base z) * z (Fin.last n) - 1

@[simp] theorem base_graph (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : base (graph f x) = x := by
  funext i; simp [base,graph]
@[simp] theorem graph_last (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : graph f x (Fin.last n) = (f x)⁻¹ := by
  simp [graph]

theorem base_smooth : ContDiff ℝ ∞ (base (n := n)) :=
  contDiff_pi.mpr (fun i => contDiff_apply ℝ _ i.castSucc)

theorem relation_smooth {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (relation f) :=
  ((hf.comp base_smooth).mul (contDiff_apply ℝ _ (Fin.last n))).sub contDiff_const

theorem nonzero_of_relation_zero {f : (Fin n → ℝ) → ℝ} {z : Fin (n+1) → ℝ}
    (hz : relation f z = 0) : f (base z) ≠ 0 := by
  intro h; simp [relation,h] at hz

theorem graph_of_relation_zero {f : (Fin n → ℝ) → ℝ} {z : Fin (n+1) → ℝ}
    (hz : relation f z = 0) : graph f (base z) = z := by
  have he : f (base z) * z (Fin.last n) = 1 := sub_eq_zero.mp hz
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [graph_last]
    exact (eq_inv_of_mul_eq_one_right he).symm
  · simp [graph,base]

theorem relation_graph {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : f x ≠ 0) : relation f (graph f x) = 0 := by
  simp [relation,hx]

/-- Every function smooth on f≠0 has a globally smooth inverse-graph extension. -/
theorem extension {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (g : (Fin n → ℝ) → ℝ) (hg : ContDiffOn ℝ ∞ g {x | f x ≠ 0}) :
    ∃ H : (Fin (n+1) → ℝ) → ℝ, ContDiff ℝ ∞ H ∧ ∀ x, f x ≠ 0 → H (graph f x) = g x := by
  let S := {z | relation f z = 0}
  let W := {z : Fin (n+1) → ℝ | f (base z) ≠ 0}
  have hs : IsClosed S := isClosed_eq (relation_smooth hf).continuous continuous_const
  have hw : IsOpen W := isOpen_ne_fun (hf.comp base_smooth).continuous continuous_const
  obtain ⟨H,hH,he⟩ := SmoothLocalGluing.closed_extension S W hs hw
    (fun _ hz => nonzero_of_relation_zero hz) (fun z => g (base z))
    (hg.comp base_smooth.contDiffOn (fun _ hz => hz))
  exact ⟨H,hH,fun x hx => by simpa using he (graph f x) (relation_graph hx)⟩

theorem graph_smoothOn {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (graph f) {x | f x ≠ 0} := by
  apply contDiffOn_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [graph_last]
    exact hf.contDiffOn.inv (fun _ hx => hx)
  · simpa [graph] using (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).contDiffOn

theorem graph_base_smoothOn {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (fun z => graph f (base z)) {z : Fin (n+1) → ℝ | f (base z) ≠ 0} :=
  (graph_smoothOn hf).comp base_smooth.contDiffOn (fun _ hz => hz)

/-- Hadamard along the single added coordinate, with the base coordinates fixed. -/
theorem vertical_factor {H : (Fin (n+1) → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    (f : (Fin n → ℝ) → ℝ) (z : Fin (n+1) → ℝ) :
    H z - H (graph f (base z)) =
      (z (Fin.last n) - (f (base z))⁻¹) *
        SmoothHadamard.coefficient H (Fin.last n) (z,graph f (base z)) := by
  rw [SmoothHadamard.factorization hH, Fin.sum_univ_castSucc]
  simp [graph,base]

/-- Vanishing on the inverse graph gives divisibility by its defining relation
in the ordinary ring of globally smooth functions. -/
theorem divisibility {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {H : (Fin (n+1) → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    (hv : ∀ x, f x ≠ 0 → H (graph f x) = 0) :
    ∃ Q : (Fin (n+1) → ℝ) → ℝ, ContDiff ℝ ∞ Q ∧ ∀ z, relation f z * Q z = H z := by
  let W := {z : Fin (n+1) → ℝ | f (base z) ≠ 0}
  let V := {z : Fin (n+1) → ℝ | relation f z ≠ 0}
  have hw : IsOpen W := isOpen_ne_fun (hf.comp base_smooth).continuous continuous_const
  have hvv : IsOpen V := isOpen_ne_fun (relation_smooth hf).continuous continuous_const
  let q := fun z => SmoothHadamard.coefficient H (Fin.last n) (z,graph f (base z)) / f (base z)
  have hq : ContDiffOn ℝ ∞ q W :=
    ((SmoothHadamard.coefficient_smooth hH (Fin.last n)).comp_contDiffOn
      (contDiffOn_id.prodMk (graph_base_smoothOn hf))).div (hf.comp base_smooth).contDiffOn
        (fun _ hz => hz)
  have hqe (z) (hz : z ∈ W) : relation f z * q z = H z := by
    have he := vertical_factor hH f z
    rw [hv (base z) hz,sub_zero] at he
    rw [he]
    dsimp [relation,q]
    field_simp [show f (base z) ≠ 0 from hz]
  apply SmoothLocalGluing.scalar_equation
  intro z
  by_cases hz : z ∈ W
  · exact ⟨W,hw.mem_nhds hz,q,hq,hqe⟩
  · have hn : relation f z ≠ 0 := by
      have he : f (base z) = 0 := not_ne_iff.mp hz
      simp [relation,he]
    refine ⟨V,hvv.mem_nhds hn,fun z => H z / relation f z,
      hH.contDiffOn.div (relation_smooth hf).contDiffOn (fun _ hy => hy),?_⟩
    intro y hy
    exact mul_div_cancel₀ (H y) hy

end SquareKit.SmoothInverseGraph
