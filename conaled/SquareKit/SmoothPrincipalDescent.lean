import SquareKit.SmoothOverlapRestriction
import SquareKit.SmoothIdealGluing

/-! Experimental scalar descent for finite principal covers of finite smooth presentations.
All compatible localized elements glue. The proof uses smooth partitions and exact local
ideal coefficient equations, without a fraction denominator bound or point detection. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SquareKit.SmoothAlgebra.PrincipalCover
open PresentedLocalization
variable {n m k : ℕ}

/-- The two restrictions agree in the actual algebra overlap. -/
def Compatible {ι : Type*} (r : Fin m → Free n) (p : ι → Free n) (a : ∀ i, Carrier r (p i)) : Prop :=
  ∀ i j, overlapLeft r (p i) (p j) (a i) = overlapRight r (p i) (p j) (a j)

/-- Every compatible tuple, including tuples containing nilpotent coefficients, has one gluing. -/
theorem exists_unique (r : Fin m → Free n) (p : Fin k → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i)))
    (a : ∀ i, Carrier r (p i)) (ha : Compatible r p a) :
    ∃! b : Presentation.Carrier r, ∀ i, base r (p i) b = a i := by
  choose H hH using (fun i => Ideal.Quotient.mk_surjective (a i))
  let v : Fin (k+m) → Free n := Fin.append p r
  let U : Fin (k+m) → Set (Fin n → ℝ) := fun i => {x | (v i).val x ≠ 0}
  let f : Fin (k+m) → (Fin n → ℝ) → ℝ := Fin.append (fun i => graphValue (p i) (H i)) (fun _ _ => 0)
  have hU : ∀ i, IsOpen (U i) := fun i => isOpen_ne_fun
    (show ContDiff ℝ ∞ (v i).val from (v i).property).continuous continuous_const
  have hc : ∀ x, ∃ i, x ∈ U i := by
    intro x
    rcases ambient_cover r p hs x with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨i.castAdd m,by simpa [U,v] using hi⟩
    · exact ⟨j.natAdd k,by simpa [U,v] using hj⟩
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [f,U,v] using graphValue_smooth (p j) (H j)
    · simpa [f,U,v] using (contDiffOn_const (c := (0 : ℝ)) (s := {x | (r j).val x ≠ 0}) (𝕜 := ℝ) (n := ∞))
  have hcompat : ∀ i j x, x ∈ U i → x ∈ U j → LocalIdeal.Mem r (fun y => f i y-f j y) x := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro x hi hj
      simp only [U,v,Fin.append_left] at hi hj
      simp only [f,Fin.append_left]
      apply overlap_compatible_local r (p i) (p j) (H i) (H j) ?_ x hi hj
      change overlapLeft r (p i) (p j) (Ideal.Quotient.mk _ (H i)) =
        overlapRight r (p i) (p j) (Ideal.Quotient.mk _ (H j))
      rw [hH i,hH j]
      exact ha i j
    · intro x hi hj
      apply LocalIdeal.of_generator_ne_zero r j (by simpa [U,v] using hj) ((hU _).mem_nhds hi)
      simpa only [f,U,v,Fin.append_left,Fin.append_right] using (graphValue_smooth (p i) (H i)).sub (contDiffOn_const (c := (0 : ℝ)))
    · intro x hi hj
      apply LocalIdeal.of_generator_ne_zero r i (by simpa [U,v] using hi) ((hU _).mem_nhds hj)
      simpa only [f,U,v,Fin.append_left,Fin.append_right] using (contDiffOn_const (c := (0 : ℝ))).sub (graphValue_smooth (p j) (H j))
    · intro x _ _
      simpa [f] using LocalIdeal.zero r x
  obtain ⟨g,hg⟩ := LocalIdeal.finite_gluing r U hU hc f hf hcompat
  have hresult (i : Fin k) : base r (p i) (Presentation.projection r g)=a i := by
    have hz : Presentation.projection (Presentation.relations r (equation (p i))) (Localization.extend g-H i)=0 := by
      apply (zero_iff_local r (p i) (Localization.extend g-H i)).mpr
      intro x hx
      have hl := hg (i.castAdd m) x (by simpa [U,v] using hx)
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

end SquareKit.SmoothAlgebra.PrincipalCover
