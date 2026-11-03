import SquareKit.SmoothPrincipalCover

/-! Experimental arbitrary principal covers defined on all real algebra points.
The algebra remains its full finite-presentation quotient, including nilpotents.
Analytic results allow Type u indices; the small categorical site uses Type. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothAlgebra.OpenCover
open PrincipalCover
variable {A B : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
  [CommRing B] [Algebra ℝ B] [Structure B] {ι : Type*}

def Covers (s : ι → A) : Prop := ∀ h : Hom A ℝ, ∃ i, h (s i) ≠ 0

theorem map_covers (h : Hom A B) (s : ι → A) (hs : Covers s) : Covers (fun i => h (s i)) :=
  fun k => hs (Hom.comp k h)

theorem trivial_covers [Subsingleton A] (s : ι → A) : Covers s := by
  intro h
  have he : (0 : ℝ)=1 := by
    calc
      0 = h.toAlgHom 0 := (map_zero h.toAlgHom).symm
      _ = h.toAlgHom 1 := congrArg h.toAlgHom (Subsingleton.elim _ _)
      _ = 1 := map_one h.toAlgHom
  exact (zero_ne_one he).elim

variable {n m : ℕ}

theorem realPoint_coordinates (r : Fin m → Free n) (h : Hom (Presentation.Carrier r) ℝ)
    (f : Free n) : h (Presentation.projection r f) =
      f.val (fun i => h (Presentation.projection r (generator i))) := by
  have he := evaluate_unique (Hom.comp h (Presentation.projection r))
  exact congrArg (fun k : Hom (Free n) ℝ => k f) he.symm

theorem covers_iff_zero_locus (r : Fin m → Free n) (p : ι → Free n) :
    Covers (fun i => Presentation.projection r (p i)) ↔
      ∀ x : Fin n → ℝ, (∀ j, (r j).val x=0) → ∃ i, (p i).val x ≠ 0 := by
  constructor
  · intro hs x hx
    exact hs (realPoint r x hx)
  · intro hc h
    let x := fun i => h (Presentation.projection r (generator i))
    have hr (j : Fin m) : (r j).val x=0 := by
      rw [← realPoint_coordinates r h,Presentation.relation_zero]
      exact map_zero h.toAlgHom
    obtain ⟨i,hi⟩ := hc x hr
    exact ⟨i,by rwa [realPoint_coordinates]⟩

theorem finite_iff {k : ℕ} (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) :
    Covers s ↔ PrincipalCover.Covers s := by
  have ha := covers_iff_zero_locus r (fun i => PresentedLocalization.representative r (s i))
  have hb := PrincipalCover.covers_iff_zero_locus r (fun i => PresentedLocalization.representative r (s i))
  simp only [PresentedLocalization.representative_eq] at ha hb
  exact ha.trans hb.symm

theorem empty_iff (r : Fin m → Free n) (s : Fin 0 → Presentation.Carrier r) :
    Covers s ↔ Subsingleton (Presentation.Carrier r) :=
  (finite_iff r s).trans (PrincipalCover.empty_iff s)

theorem ambient_cover (r : Fin m → Free n) (p : ι → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) (x : Fin n → ℝ) :
    (∃ i, (p i).val x≠0) ∨ (∃ j, (r j).val x≠0) := by
  by_cases hr : ∃ j, (r j).val x≠0
  · exact Or.inr hr
  · exact Or.inl ((covers_iff_zero_locus r p).mp hs x (by simpa using hr))

theorem separated (r : Fin m → Free n) (p : ι → Free n)
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

end SquareKit.SmoothAlgebra.OpenCover
