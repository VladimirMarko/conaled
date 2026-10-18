import SquareKit.SmoothLocalGluing
import SquareKit.SmoothPresentation

/-! Experimental local membership in finitely generated smooth ideals.
Local coefficient equations, rather than values at real points, retain nilpotents. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace SquareKit.SmoothAlgebra.LocalIdeal
variable {n m : ℕ}
abbrev Space (n : ℕ) := Fin n → ℝ

/-- A smooth coefficient equation on a neighborhood of the specified point. -/
def Mem (r : Fin m → Free n) (f : Space n → ℝ) (x : Space n) : Prop :=
  ∃ U ∈ 𝓝 x, ∃ c : Space n → (Fin m → ℝ), ContDiffOn ℝ ∞ c U ∧
    ∀ y ∈ U, f y = ∑ j, (r j).val y * c y j

theorem zero (r : Fin m → Free n) (x : Space n) : Mem r (fun _ => 0) x := by
  refine ⟨univ,univ_mem,fun _ _ => 0,contDiffOn_const,?_⟩
  simp

theorem congr {r : Fin m → Free n} {f g : Space n → ℝ} {x : Space n}
    (h : Mem r f x) (he : f =ᶠ[𝓝 x] g) : Mem r g x := by
  obtain ⟨U,hU,c,hc,hf⟩ := h
  obtain ⟨V,hV,hg⟩ := eventually_iff_exists_mem.mp he
  exact ⟨U ∩ V,inter_mem hU hV,c,hc.mono inter_subset_left,
    fun y hy => (hg y hy.2).symm.trans (hf y hy.1)⟩

theorem add {r : Fin m → Free n} {f g : Space n → ℝ} {x : Space n}
    (hf : Mem r f x) (hg : Mem r g x) : Mem r (fun y => f y+g y) x := by
  obtain ⟨U,hU,c,hc,hf⟩ := hf
  obtain ⟨V,hV,d,hd,hg⟩ := hg
  refine ⟨U ∩ V,inter_mem hU hV,fun y => c y+d y,
    (hc.mono inter_subset_left).add (hd.mono inter_subset_right),?_⟩
  intro y hy
  dsimp only
  rw [hf y hy.1,hg y hy.2,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact (mul_add _ _ _).symm

theorem mul {r : Fin m → Free n} {f g : Space n → ℝ} {x : Space n}
    (hf : Mem r f x) {V : Set (Space n)} (hV : V ∈ 𝓝 x) (hg : ContDiffOn ℝ ∞ g V) :
    Mem r (fun y => g y*f y) x := by
  obtain ⟨U,hU,c,hc,hf⟩ := hf
  refine ⟨U ∩ V,inter_mem hU hV,fun y => g y • c y,
    (hg.mono inter_subset_right).smul (hc.mono inter_subset_left),?_⟩
  intro y hy
  dsimp only
  rw [hf y hy.1,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change g y*((r j).val y*c y j) = (r j).val y*(g y*c y j)
  ring

theorem sum {r : Fin m → Free n} {k : ℕ} (f : Fin k → Space n → ℝ) (x : Space n)
    (h : ∀ i, Mem r (f i) x) : Mem r (fun y => ∑ i, f i y) x := by
  have hf : ∀ S : Finset (Fin k), Mem r (fun y => ∑ i ∈ S, f i y) x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using zero r x
    | @insert i S hi ih => simpa [Finset.sum_insert hi] using add (h i) ih
  exact hf Finset.univ

/-- A nonzero ideal generator is locally invertible, including for local smooth functions. -/
theorem of_generator_ne_zero (r : Fin m → Free n) (j : Fin m) {f : Space n → ℝ}
    {x : Space n} (hj : (r j).val x ≠ 0) {U : Set (Space n)}
    (hU : U ∈ 𝓝 x) (hf : ContDiffOn ℝ ∞ f U) : Mem r f x := by
  let V := {y | (r j).val y ≠ 0}
  have hv : IsOpen V := isOpen_ne_fun (show ContDiff ℝ ∞ (r j).val from (r j).property).continuous continuous_const
  refine ⟨U ∩ V,inter_mem hU (hv.mem_nhds hj),fun y i => if i=j then f y/(r j).val y else 0,?_,?_⟩
  · apply contDiffOn_pi.mpr
    intro i
    by_cases hi : i=j
    · simp only [hi,ite_true]
      exact (hf.mono inter_subset_left).div
        (show ContDiff ℝ ∞ (r j).val from (r j).property).contDiffOn (fun y hy => hy.2)
    · simp only [hi,ite_false]
      exact contDiffOn_const
  · intro y hy
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact (mul_div_cancel₀ (f y) hy.2).symm

theorem global_iff (r : Fin m → Free n) (f : Free n) :
    f ∈ Presentation.ideal r ↔ ∀ x, Mem r f.val x := by
  rw [Presentation.ideal, Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c,hc⟩ x
    refine ⟨univ,univ_mem,fun y j => (c j).val y,?_,?_⟩
    · exact (contDiff_pi.mpr (fun j => show ContDiff ℝ ∞ (c j).val from (c j).property)).contDiffOn
    · intro y _
      have he := congrArg (fun p : Free n => p.val y) hc
      simpa only [show ∀ (v : Fin m → Free n), (∑ j, v j).val = ∑ j, (v j).val from fun v => map_sum (Free n).val v Finset.univ, Subalgebra.coe_mul, Finset.sum_apply, Pi.mul_apply, mul_comm] using he.symm
  · intro hl
    let t : Space n → Set (Fin m → ℝ) := fun x => {v | f.val x = ∑ j, (r j).val x * v j}
    have ht : ∀ x, Convex ℝ (t x) := by
      intro x u hu v hv a b ha hb hab
      change f.val x = ∑ j, (r j).val x * (a*u j+b*v j)
      calc
        f.val x = a*f.val x+b*f.val x := by rw [← add_mul,hab,one_mul]
        _ = a*(∑ j, (r j).val x*u j)+b*(∑ j, (r j).val x*v j) := by rw [← hu,← hv]
        _ = _ := by rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]; congr 1; funext j; ring
    obtain ⟨c,hc⟩ := exists_contMDiffMap_forall_mem_convex_of_local (𝓘(ℝ,Space n)) ht
      (fun x => by
        obtain ⟨U,hU,c,hs,he⟩ := hl x
        exact ⟨U,hU,c,hs.contMDiffOn,he⟩)
    refine ⟨fun j => ⟨fun x => c x j,(contDiff_apply ℝ (fun _ : Fin m => ℝ) j).comp c.contMDiff.contDiff⟩,?_⟩
    apply Subtype.ext
    funext x
    simpa only [show ∀ (v : Fin m → Free n), (∑ j, v j).val = ∑ j, (v j).val from fun v => map_sum (Free n).val v Finset.univ, Subalgebra.coe_mul, Finset.sum_apply, Pi.mul_apply, mul_comm] using (hc x).symm

end SquareKit.SmoothAlgebra.LocalIdeal
