import SquareKit.SmoothPrincipalDescent
import SquareKit.SmoothOpenCover
import SquareKit.SmoothIdealArbitraryGluing

/-! Experimental arbitrary principal localization descent. Neighborhood coefficient
identities preserve the full quotient ideal and its nilpotents. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SquareKit.SmoothAlgebra.OpenCover
open PresentedLocalization PrincipalCover
variable {n m : ℕ} {ι : Type*}

/-- Every compatible tuple, including tuples containing nilpotent coefficients, has one gluing. -/
theorem exists_unique (r : Fin m → Free n) (p : ι → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i)))
    (a : ∀ i, Carrier r (p i)) (ha : Compatible r p a) :
    ∃! b : Presentation.Carrier r, ∀ i, base r (p i) b = a i := by
  choose H hH using (fun i => Ideal.Quotient.mk_surjective (a i))
  let v : ι ⊕ Fin m → Free n := Sum.elim p r
  let U : ι ⊕ Fin m → Set (Fin n → ℝ) := fun i => {x | (v i).val x ≠ 0}
  let f : ι ⊕ Fin m → (Fin n → ℝ) → ℝ := Sum.elim (fun i => graphValue (p i) (H i)) (fun _ _ => 0)
  have hU : ∀ i, IsOpen (U i) := fun i => isOpen_ne_fun
    (show ContDiff ℝ ∞ (v i).val from (v i).property).continuous continuous_const
  have hc : ∀ x, ∃ i, x ∈ U i := by
    intro x
    rcases ambient_cover r p hs x with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨Sum.inl i,by simpa [U,v] using hi⟩
    · exact ⟨Sum.inr j,by simpa [U,v] using hj⟩
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i) := by
    intro i
    refine Sum.rec (fun j => ?_) (fun j => ?_) i
    · simpa [f,U,v] using graphValue_smooth (p j) (H j)
    · simpa [f,U,v] using (contDiffOn_const (c := (0 : ℝ)) (s := {x | (r j).val x ≠ 0}) (𝕜 := ℝ) (n := ∞))
  have hcompat : ∀ i j x, x ∈ U i → x ∈ U j → LocalIdeal.Mem r (fun y => f i y-f j y) x := by
    intro i j
    refine Sum.rec (fun i => ?_) (fun i => ?_) i <;>
      refine Sum.rec (fun j => ?_) (fun j => ?_) j
    · intro x hi hj
      simp only [U,v,Sum.elim_inl] at hi hj
      simp only [f,Sum.elim_inl]
      apply overlap_compatible_local r (p i) (p j) (H i) (H j) ?_ x hi hj
      change overlapLeft r (p i) (p j) (Ideal.Quotient.mk _ (H i)) =
        overlapRight r (p i) (p j) (Ideal.Quotient.mk _ (H j))
      rw [hH i,hH j]
      exact ha i j
    · intro x hi hj
      apply LocalIdeal.of_generator_ne_zero r j (by simpa [U,v] using hj) ((hU _).mem_nhds hi)
      simpa only [f,U,v,Sum.elim_inl,Sum.elim_inr] using (graphValue_smooth (p i) (H i)).sub (contDiffOn_const (c := (0 : ℝ)))
    · intro x hi hj
      apply LocalIdeal.of_generator_ne_zero r i (by simpa [U,v] using hi) ((hU _).mem_nhds hj)
      simpa only [f,U,v,Sum.elim_inl,Sum.elim_inr] using (contDiffOn_const (c := (0 : ℝ))).sub (graphValue_smooth (p j) (H j))
    · intro x _ _
      simpa [f] using LocalIdeal.zero r x
  obtain ⟨g,hg⟩ := LocalIdeal.arbitrary_gluing r U hU hc f hf hcompat
  have hresult (i : ι) : base r (p i) (Presentation.projection r g)=a i := by
    have hz : Presentation.projection (Presentation.relations r (equation (p i))) (Localization.extend g-H i)=0 := by
      apply (zero_iff_local r (p i) (Localization.extend g-H i)).mpr
      intro x hx
      have hl := hg (Sum.inl i) x (by simpa [U,v] using hx)
      have he : graphValue (p i) (Localization.extend (k := 1) g-H i) = fun y => g.val y-graphValue (p i) (H i) y := by
        funext y
        change g.val (SmoothInverseGraph.base (SmoothInverseGraph.graph (p i).val y)) - _ = _
        rw [SmoothInverseGraph.base_graph]
      rw [he]
      simpa [f] using hl
    change (Presentation.projection (Presentation.relations r (equation (p i)))).toAlgHom (Localization.extend g-H i)=0 at hz
    rw [map_sub,sub_eq_zero] at hz
    have hp := congrArg (fun h : Hom (Free n) (Carrier r (p i)) => h g) (Presentation.inclusion_projection r (equation (p i)))
    change base r (p i) (Presentation.projection r g) = Presentation.projection _ (Localization.extend g) at hp
    exact hp.trans (hz.trans (hH i))
  exact ⟨Presentation.projection r g,hresult,fun b hb => separated r p hs b _ (fun i => (hb i).trans (hresult i).symm)⟩

end SquareKit.SmoothAlgebra.OpenCover
