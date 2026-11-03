import SquareKit.SmoothIdealGluing

/-! Experimental gluing modulo finite smooth ideals on arbitrary small open covers.
Local finiteness belongs to the constructed partition, not to the input cover. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace SquareKit.SmoothAlgebra.LocalIdeal
variable {n m : ℕ} {ι : Type*}

/-- Local ideal membership is closed under a genuinely finite sum. -/
theorem finset_sum (r : Fin m → Free n) (f : ι → Space n → ℝ) (x : Space n)
    (S : Finset ι) (h : ∀ i ∈ S, Mem r (f i) x) : Mem r (fun y => ∑ i ∈ S, f i y) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using zero r x
  | @insert i S hi ih =>
    simpa [Finset.sum_insert hi] using add (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Arbitrary cover gluing retains local coefficient equations in the full ideal.
A locally finite subordinate smooth partition supplies the assembled function. -/
theorem arbitrary_gluing (r : Fin m → Free n) (U : ι → Set (Space n))
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (f : ι → Space n → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hc : ∀ i j x, x ∈ U i → x ∈ U j → Mem r (fun y => f i y-f j y) x) :
    ∃ g : Free n, ∀ i x, x ∈ U i → Mem r (fun y => g.val y-f i y) x := by
  classical
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ,Space n))
    isClosed_univ U hU (fun x _ => mem_iUnion.mpr (hcover x))
  let g : Free n := ⟨fun x => ∑ᶠ j, ρ j x * f j x, by
    exact (hρ.contMDiff_finsum_smul hU (fun i => (hf i).contMDiffOn)).contDiff⟩
  refine ⟨g,fun i x hx => ?_⟩
  obtain ⟨V,hV,hfin⟩ := ρ.locallyFinite x
  let S := hfin.toFinset
  have hs (y : Space n) (hy : y ∈ V) : Function.support (fun j => ρ j y) ⊆ (S : Set ι) := by
    intro j hj
    exact hfin.mem_toFinset.mpr ⟨y,hj,hy⟩
  have hterm (j : ι) : Mem r (fun y => ρ j y*(f j y-f i y)) x := by
    by_cases hj : x ∈ tsupport (ρ j)
    · exact mul (hc j i x (hρ j hj) hx) univ_mem (ρ j).contMDiff.contDiff.contDiffOn
    · apply congr (zero r x)
      filter_upwards [(isClosed_tsupport (ρ j)).isOpen_compl.mem_nhds hj] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  apply congr (finset_sum r (fun j y => ρ j y*(f j y-f i y)) x S (fun j _ => hterm j))
  filter_upwards [hV] with y hy
  change (∑ j ∈ S, ρ j y*(f j y-f i y)) = (∑ᶠ j, ρ j y*f j y)-f i y
  rw [finsum_eq_sum_of_support_subset _ ((Function.support_mul_subset_left _ _).trans (hs y hy))]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  have he : ∑ j ∈ S, ρ j y = 1 :=
    (finsum_eq_sum_of_support_subset _ (hs y hy)).symm.trans (ρ.sum_eq_one (mem_univ y))
  rw [he,one_mul]

end SquareKit.SmoothAlgebra.LocalIdeal
