import SquareKit.SmoothLocalizationLocalIdeal
import SquareKit.SmoothLocalizationBaseChange

/-! Experimental finite principal smooth covers with the ordinary unit-ideal condition.
The empty cover is allowed precisely for a trivial algebra. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothAlgebra.PrincipalCover
variable {A B : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
  [CommRing B] [Algebra ℝ B] [Structure B] {k : ℕ}

/-- Ordinary ideal generation, equivalently a finite linear combination equal to one. -/
def Covers (s : Fin k → A) : Prop := ∃ c : Fin k → A, ∑ i, c i*s i = 1

omit [Algebra ℝ A] [Structure A] in
theorem covers_iff_span (s : Fin k → A) : Covers s ↔ Ideal.span (Set.range s) = ⊤ := by
  rw [Ideal.eq_top_iff_one,Ideal.mem_span_range_iff_exists_fun]
  rfl

theorem map_covers (h : Hom A B) (s : Fin k → A) (hs : Covers s) : Covers (fun i => h (s i)) := by
  obtain ⟨c,hc⟩ := hs
  refine ⟨fun i => h (c i),?_⟩
  have he := congrArg h.toAlgHom hc
  simp only [map_sum,map_mul,map_one] at he
  exact he

omit [Algebra ℝ A] [Structure A] in
theorem empty_iff (s : Fin 0 → A) : Covers s ↔ Subsingleton A := by
  simp only [Covers,Fin.sum_univ_zero]
  constructor
  · rintro ⟨_,h⟩
    exact subsingleton_of_zero_eq_one h
  · intro h
    exact ⟨Fin.elim0,Subsingleton.elim _ _⟩

variable {n m : ℕ}

def realPoint (r : Fin m → Free n) (x : Fin n → ℝ) (hx : ∀ j, (r j).val x = 0) :
    Hom (Presentation.Carrier r) ℝ := Quotient.lift (Presentation.ideal r) (evaluate x) (by
  have hi : Presentation.ideal r ≤ RingHom.ker (evaluate x).toAlgHom := by
    apply Ideal.span_le.mpr
    rintro f ⟨j,rfl⟩
    exact hx j
  exact fun f hf => hi hf)

/-- Every real point of the ordinary relation locus lies in a covering principal open. -/
theorem covers_zero_locus (r : Fin m → Free n) (p : Fin k → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) (x : Fin n → ℝ)
    (hx : ∀ j, (r j).val x = 0) : ∃ i, (p i).val x ≠ 0 := by
  obtain ⟨c,hc⟩ := map_covers (realPoint r x hx) _ hs
  by_contra h
  push Not at h
  have he : (∑ i, c i*realPoint r x hx (Presentation.projection r (p i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    change c i*(p i).val x = 0
    rw [h i,mul_zero]
  rw [he] at hc
  exact zero_ne_one hc

/-- No point of the ambient coordinate space can have all cover and relation generators zero. -/
theorem ambient_cover (r : Fin m → Free n) (p : Fin k → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) (x : Fin n → ℝ) :
    (∃ i, (p i).val x ≠ 0) ∨ (∃ j, (r j).val x ≠ 0) := by
  by_cases hr : ∃ j, (r j).val x ≠ 0
  · exact Or.inr hr
  · exact Or.inl (covers_zero_locus r p hs x (by simpa using hr))

/-- For finite presentations this algebraic cover condition agrees with covering
all real points of the ordinary zero locus. This does not identify quotient elements
by their values at those points. -/
theorem covers_iff_zero_locus (r : Fin m → Free n) (p : Fin k → Free n) :
    Covers (fun i => Presentation.projection r (p i)) ↔
      ∀ x : Fin n → ℝ, (∀ j, (r j).val x=0) → ∃ i, (p i).val x ≠ 0 := by
  constructor
  · exact fun hs => covers_zero_locus r p hs
  · intro hc
    let v : Fin (k+m) → Free n := Fin.append p r
    have hi : (1 : Free n) ∈ Presentation.ideal v := by
      apply (LocalIdeal.global_iff v 1).mpr
      intro x
      by_cases hr : ∃ j, (r j).val x ≠ 0
      · obtain ⟨j,hj⟩ := hr
        exact LocalIdeal.of_generator_ne_zero v (j.natAdd k) (by simpa [v] using hj)
          Filter.univ_mem contDiffOn_const
      · obtain ⟨i,hi⟩ := hc x (by simpa using hr)
        exact LocalIdeal.of_generator_ne_zero v (i.castAdd m) (by simpa [v] using hi)
          Filter.univ_mem contDiffOn_const
    obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
    refine ⟨fun i => Presentation.projection r (c (i.castAdd m)),?_⟩
    have he := congrArg (Presentation.projection r).toAlgHom hc
    simp only [map_add,map_sum,map_mul,map_one,Fin.sum_univ_add,v,Fin.append_left,Fin.append_right] at he
    have hz (j : Fin m) : (Presentation.projection r).toAlgHom (r j)=0 := Presentation.relation_zero r j
    simp only [hz,mul_zero,Finset.sum_const_zero,add_zero] at he
    exact he

/-- Separatedness follows from local coefficient equations, including nilpotent elements. -/
theorem separated (r : Fin m → Free n) (p : Fin k → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i)))
    (a b : Presentation.Carrier r)
    (he : ∀ i, PresentedLocalization.base r (p i) a = PresentedLocalization.base r (p i) b) : a=b := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply (LocalIdeal.global_iff r (f-g)).mpr
  intro x
  rcases ambient_cover r p hs x with ⟨i,hi⟩ | ⟨j,hj⟩
  · apply (PresentedLocalization.base_zero_iff_local r (p i) (f-g)).mp ?_ x hi
    change (Hom.comp (PresentedLocalization.base r (p i)) (Presentation.projection r)).toAlgHom (f-g)=0
    rw [map_sub,sub_eq_zero]
    exact he i
  · exact LocalIdeal.of_generator_ne_zero r j hj Filter.univ_mem
      (show ContDiff ℝ ∞ (f-g).val from (f-g).property).contDiffOn

end SquareKit.SmoothAlgebra.PrincipalCover
