import SquareKit.SmoothIdealLocal

/-! Experimental finite gluing modulo a finitely generated smooth ideal.
The construction uses subordinate smooth partitions, and keeps coefficient equations
on neighborhoods rather than reducing to values on the ordinary zero locus. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace SquareKit.SmoothAlgebra.LocalIdeal
variable {n m k : ℕ}

private theorem zero_near {w : Space n → ℝ} {x : Space n} (hx : x ∉ tsupport w) :
    w =ᶠ[𝓝 x] 0 := by
  filter_upwards [(isClosed_tsupport w).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

private theorem supported_mul {U : Set (Space n)} (hU : IsOpen U)
    (w f : Space n → ℝ) (hw : ContDiff ℝ ∞ w) (hs : tsupport w ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (fun x => w x*f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport w
  · exact hw.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [zero_near hx] with y hy
    simp [hy]

/-- Compatible local representatives glue modulo the ideal on a finite open cover.
Compatibility is an equality of germs with smooth ideal coefficients. -/
theorem finite_gluing (r : Fin m → Free n) (U : Fin k → Set (Space n))
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (f : Fin k → Space n → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hc : ∀ i j x, x ∈ U i → x ∈ U j → Mem r (fun y => f i y-f j y) x) :
    ∃ g : Free n, ∀ i x, x ∈ U i → Mem r (fun y => g.val y-f i y) x := by
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ,Space n))
    isClosed_univ U hU (fun x _ => mem_iUnion.mpr (hcover x))
  let g : Free n := ⟨fun x => ∑ j, ρ j x*f j x,
    ContDiff.sum (fun j _ => supported_mul (hU j) (ρ j) (f j) (ρ j).contMDiff.contDiff (hρ j) (hf j))⟩
  refine ⟨g,fun i x hx => ?_⟩
  have hterm (j : Fin k) : Mem r (fun y => ρ j y*(f j y-f i y)) x := by
    by_cases hj : x ∈ tsupport (ρ j)
    · exact mul (hc j i x (hρ j hj) hx) univ_mem (ρ j).contMDiff.contDiff.contDiffOn
    · apply congr (zero r x)
      filter_upwards [zero_near hj] with y hy
      simp [hy]
  apply congr (sum (fun j y => ρ j y*(f j y-f i y)) x hterm)
  apply Filter.Eventually.of_forall
  intro y
  change (∑ j, ρ j y*(f j y-f i y)) = (∑ j, ρ j y*f j y)-f i y
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  have he : ∑ j, ρ j y = 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ y)
  rw [he,one_mul]

end SquareKit.SmoothAlgebra.LocalIdeal
