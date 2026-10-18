import SquareKit.SmoothIdealLocal
import SquareKit.SmoothPresentedLocalization
import SquareKit.SmoothInverseGraph

/-! Experimental exact local coefficient criterion for presented smooth localization.
The graph relation and the original ideal are both retained. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SquareKit.SmoothAlgebra.PresentedLocalization
open SmoothInverseGraph
variable {n m : ℕ}

abbrev graphValue (p : Free n) (H : Free (n+1)) : (Fin n → ℝ) → ℝ :=
  fun x => H.val (graph p.val x)

theorem graphValue_smooth (p : Free n) (H : Free (n+1)) :
    ContDiffOn ℝ ∞ (graphValue p H) {x | p.val x ≠ 0} :=
  (show ContDiff ℝ ∞ H.val from H.property).comp_contDiffOn (graph_smoothOn p.property)

private theorem relation_graph_value (r : Fin m → Free n) (p : Free n)
    (x : Fin n → ℝ) (hx : p.val x ≠ 0) :
    (fun j => (Presentation.relations r (equation p) j).val (graph p.val x)) =
      Fin.snoc (fun j => (r j).val x) 0 := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Presentation.relations,Fin.snoc_last]
    exact relation_graph hx
  · simp only [Presentation.relations,Fin.snoc_castSucc]
    change (r i).val (SmoothInverseGraph.base (graph p.val x)) = _
    rw [base_graph]

/-- A localized representative is zero exactly when its graph restriction lies
locally in the original finitely generated ideal, with smooth coefficients. -/
theorem zero_iff_local (r : Fin m → Free n) (p : Free n) (H : Free (n+1)) :
    Presentation.projection (Presentation.relations r (equation p)) H = 0 ↔
      ∀ x, p.val x ≠ 0 → LocalIdeal.Mem r (graphValue p H) x := by
  change Ideal.Quotient.mk (Presentation.ideal (Presentation.relations r (equation p))) H = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hh x hx
    obtain ⟨c,hc⟩ := (Ideal.mem_span_range_iff_exists_fun.mp hh)
    refine ⟨{y | p.val y ≠ 0},(isOpen_ne_fun
      (show ContDiff ℝ ∞ p.val from p.property).continuous continuous_const).mem_nhds hx,
      fun y j => (c j.castSucc).val (graph p.val y),?_,?_⟩
    · exact contDiffOn_pi.mpr (fun j => graphValue_smooth p (c j.castSucc))
    · intro y hy
      have he := congrArg (fun q : Free (n+1) => q.val (graph p.val y)) hc
      rw [show (∑ i, c i * Presentation.relations r (equation p) i).val =
        ∑ i, (c i * Presentation.relations r (equation p) i).val from
        map_sum (Free (n+1)).val _ Finset.univ] at he
      simp only [Finset.sum_apply,Subalgebra.coe_mul,Pi.mul_apply] at he
      have hr := relation_graph_value r p y hy
      simp_rw [congrFun hr] at he
      rw [Fin.sum_univ_castSucc] at he
      simp only [Fin.snoc_castSucc,Fin.snoc_last,mul_zero,add_zero] at he
      simpa only [mul_comm] using he.symm
  · intro hh
    apply (LocalIdeal.global_iff (Presentation.relations r (equation p)) H).mpr
    intro z
    let W := {z : Fin (n+1) → ℝ | p.val (SmoothInverseGraph.base z) ≠ 0}
    have hw : IsOpen W := isOpen_ne_fun
      ((show ContDiff ℝ ∞ p.val from p.property).comp base_smooth).continuous continuous_const
    by_cases hz : z ∈ W
    · obtain ⟨U,hU,c,hc,he⟩ := hh (SmoothInverseGraph.base z) hz
      let V := SmoothInverseGraph.base ⁻¹' U ∩ W
      have hv : V ∈ 𝓝 z := inter_mem (base_smooth.continuous.continuousAt.preimage_mem_nhds hU) (hw.mem_nhds hz)
      let q := fun z => SmoothHadamard.coefficient H.val (Fin.last n)
        (z,graph p.val (SmoothInverseGraph.base z)) / p.val (SmoothInverseGraph.base z)
      have hq : ContDiffOn ℝ ∞ q W :=
        ((SmoothHadamard.coefficient_smooth (show ContDiff ℝ ∞ H.val from H.property) (Fin.last n)).comp_contDiffOn
          (contDiffOn_id.prodMk (graph_base_smoothOn p.property))).div
            ((show ContDiff ℝ ∞ p.val from p.property).comp base_smooth).contDiffOn (fun _ h => h)
      refine ⟨V,hv,fun y => Fin.snoc (c (SmoothInverseGraph.base y)) (q y),?_,?_⟩
      · apply contDiffOn_pi.mpr
        intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [Fin.snoc_last] using hq.mono inter_subset_right
        · simp only [Fin.snoc_castSucc]
          exact (contDiff_apply ℝ (fun _ : Fin m => ℝ) i).comp_contDiffOn
            (hc.comp base_smooth.contDiffOn (fun _ hy => hy.1))
      · intro y hy
        rw [Fin.sum_univ_castSucc]
        simp only [Presentation.relations,Fin.snoc_castSucc,Fin.snoc_last]
        change H.val y = (∑ j, (r j).val (SmoothInverseGraph.base y)*c (SmoothInverseGraph.base y) j) + relation p.val y*q y
        rw [← he (SmoothInverseGraph.base y) hy.1]
        have h := vertical_factor (show ContDiff ℝ ∞ H.val from H.property) p.val y
        have hqeq : relation p.val y*q y = H.val y-graphValue p H (SmoothInverseGraph.base y) := by
          rw [h]
          dsimp [q,relation]
          field_simp [show p.val (SmoothInverseGraph.base y) ≠ 0 from hy.2]
        rw [hqeq]
        ring
    · apply LocalIdeal.of_generator_ne_zero _ (Fin.last m) (f := H.val) ?_ univ_mem
        (show ContDiff ℝ ∞ H.val from H.property).contDiffOn
      simp only [Presentation.relations,Fin.snoc_last]
      change relation p.val z ≠ 0
      have hp : p.val (SmoothInverseGraph.base z) = 0 := not_ne_iff.mp hz
      simp [relation,hp]

theorem base_zero_iff_local (r : Fin m → Free n) (p f : Free n) :
    base r p (Presentation.projection r f) = 0 ↔
      ∀ x, p.val x ≠ 0 → LocalIdeal.Mem r f.val x := by
  have hb := congrArg (fun h : Hom (Free n) (Carrier r p) => h f)
    (Presentation.inclusion_projection r (equation p))
  change base r p (Presentation.projection r f) =
    Presentation.projection (Presentation.relations r (equation p)) (Localization.extend f) at hb
  rw [hb,zero_iff_local]
  have he : graphValue p (Localization.extend (k := 1) f) = f.val := by
    funext x
    exact congrArg f.val (base_graph p.val x)
  rw [he]


end SquareKit.SmoothAlgebra.PresentedLocalization
