import Mathlib.CategoryTheory.Sites.Subsheaf

/-! Experimental local existential images for type-valued sheaves.
This interface uses Mathlib subfunctors directly and does not interpret syntax.
The indexing category, its morphisms, and sections have independent universes.
-/
namespace SquareKit.SheafImage
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A B : Sheaf J (Type w)}

/-- Existential image with witnesses on a covering sieve. -/
def localImage (Q : Subfunctor A.obj) (f : A ⟶ B) : Subfunctor B.obj :=
  (Q.image f.hom).sheafify J

/-- The sieve asks only for individual witnesses, with no overlap agreement. -/
theorem mem_localImage (Q : Subfunctor A.obj) (f : A ⟶ B)
    {U : Cᵒᵖ} (b : B.obj.obj U) :
    (localImage Q f).obj U b ↔
      (Q.image f.hom).sieveOfSection b ∈ J U.unop := Iff.rfl

/-- Explicit meaning of each arrow in the witnessing sieve. -/
theorem witness_arrow (Q : Subfunctor A.obj) (f : A ⟶ B)
    {U V : C} (g : V ⟶ U) (b : B.obj.obj (op U)) :
    (Q.image f.hom).sieveOfSection b g ↔
      ∃ a : A.obj.obj (op V), Q.obj (op V) a ∧
        f.hom.app (op V) a = B.obj.map g.op b := Iff.rfl

theorem localImage_isSheaf (Q : Subfunctor A.obj) (f : A ⟶ B) :
    Presieve.IsSheaf J (localImage Q f).toFunctor :=
  (Q.image f.hom).sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).mp B.property)

theorem restrict (Q : Subfunctor A.obj) (f : A ⟶ B)
    {U V : Cᵒᵖ} (g : U ⟶ V) {b : B.obj.obj U}
    (h : (localImage Q f).obj U b) :
    (localImage Q f).obj V (B.obj.map g b) := (localImage Q f).map g h

/-- Closure is essential here: an arbitrary target predicate need not contain
sections that belong to it only locally. -/
theorem adjunction (Q : Subfunctor A.obj) (f : A ⟶ B)
    (R : Subfunctor B.obj) (hR : Presieve.IsSheaf J R.toFunctor) :
    localImage Q f ≤ R ↔ Q ≤ R.preimage f.hom := by
  constructor
  · intro h
    exact (Subfunctor.image_le_iff _ _ _).mp ((Q.image f.hom).le_sheafify J |>.trans h)
  · intro h
    exact (Q.image f.hom).sheafify_le R ((Subfunctor.image_le_iff _ _ _).mpr h)
      ((isSheaf_iff_isSheaf_of_type _ _).mp B.property) hR

theorem monotone (f : A ⟶ B) {Q R : Subfunctor A.obj} (h : Q ≤ R) :
    localImage Q f ≤ localImage R f := by
  apply (adjunction Q f _ (localImage_isSheaf R f)).mpr
  intro U a ha
  exact (R.image f.hom).le_sheafify J U ⟨a, h U ha, rfl⟩

/-- Inverse image preserves closed predicates along sheaf morphisms. -/
theorem preimage_isSheaf (R : Subfunctor B.obj) (f : A ⟶ B)
    (hR : Presieve.IsSheaf J R.toFunctor) :
    Presieve.IsSheaf J (R.preimage f.hom).toFunctor := by
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).mp A.property)).mpr
  intro U a ha
  apply (Subfunctor.isSheaf_iff R
    ((isSheaf_iff_isSheaf_of_type _ _).mp B.property)).mp hR U (f.hom.app U a)
  apply J.superset_covering _ ha
  intro V g hg
  change R.obj (op V) (B.obj.map g.op (f.hom.app U a))
  rw [← NatTrans.naturality_apply]
  exact hg

/-- Conjunction of closed predicates on an ambient sheaf is closed. -/
theorem inf_isSheaf (P R : Subfunctor B.obj)
    (hP : Presieve.IsSheaf J P.toFunctor) (hR : Presieve.IsSheaf J R.toFunctor) :
    Presieve.IsSheaf J (P ⊓ R).toFunctor := by
  have hB := (isSheaf_iff_isSheaf_of_type _ _).mp B.property
  apply (Subfunctor.isSheaf_iff _ hB).mpr
  intro U b hb
  constructor
  · apply (Subfunctor.isSheaf_iff P hB).mp hP U b
    exact J.superset_covering (by intro V g hg; exact hg.1) hb
  · apply (Subfunctor.isSheaf_iff R hB).mp hR U b
    exact J.superset_covering (by intro V g hg; exact hg.2) hb

/-- A closed target condition can move inside a local existential.
The source predicate is unrestricted; local witnesses need not agree. -/
theorem frobenius (Q : Subfunctor A.obj) (f : A ⟶ B)
    (R : Subfunctor B.obj) (hR : Presieve.IsSheaf J R.toFunctor) :
    localImage (Q ⊓ R.preimage f.hom) f = localImage Q f ⊓ R := by
  apply le_antisymm
  · exact le_inf (monotone f inf_le_left) ((adjunction _ f R hR).mpr inf_le_right)
  · intro U b hb
    apply (mem_localImage _ _ b).mpr
    apply J.superset_covering _ hb.1
    intro V g hg
    rcases hg with ⟨a, ha, he⟩
    exact ⟨a, ⟨ha, by change R.obj _ (f.hom.app _ a); rw [he]; exact R.map g.op hb.2⟩, he⟩

/-- The conjunction on the right of Frobenius is a sheaf predicate. -/
theorem localImage_inf_isSheaf (Q : Subfunctor A.obj) (f : A ⟶ B)
    (R : Subfunctor B.obj) (hR : Presieve.IsSheaf J R.toFunctor) :
    Presieve.IsSheaf J (localImage Q f ⊓ R).toFunctor :=
  inf_isSheaf _ _ (localImage_isSheaf Q f) hR

/-- The top-predicate case is exactly Mathlib's chosen image predicate. -/
theorem top_eq_range (f : A ⟶ B) :
    localImage ⊤ f = (Subfunctor.range f.hom).sheafify J := by
  rw [localImage, Subfunctor.image_top]

/-- Sections of the local image are sections of Mathlib's image, over B. -/
def imageEquiv (f : A ⟶ B) (U : Cᵒᵖ) :
    (localImage ⊤ f).toFunctor.obj U ≃ (Sheaf.image f).obj.obj U :=
  Equiv.subtypeEquivRight fun b => by rw [top_eq_range]

theorem imageEquiv_inclusion (f : A ⟶ B) (U : Cᵒᵖ)
    (b : (localImage ⊤ f).toFunctor.obj U) :
    (Sheaf.imageι f).hom.app U (imageEquiv f U b) = b.val := rfl

theorem imageEquiv_naturality (f : A ⟶ B) {U V : Cᵒᵖ}
    (g : U ⟶ V) (b : (localImage ⊤ f).toFunctor.obj U) :
    imageEquiv f V ((localImage ⊤ f).toFunctor.map g b) =
      (Sheaf.image f).obj.map g (imageEquiv f U b) := rfl

/-- The equivalence also respects the chosen factor from the source. -/
theorem imageEquiv_factor (f : A ⟶ B) (U : Cᵒᵖ) (a : A.obj.obj U) :
    imageEquiv f U ⟨f.hom.app U a,
      (Subfunctor.le_sheafify _ _ _) ⟨a, trivial, rfl⟩⟩ =
        (Sheaf.toImage f).hom.app U a := rfl

theorem image_factorization (f : A ⟶ B) :
    Sheaf.toImage f ≫ Sheaf.imageι f = f := Sheaf.toImage_ι f

end SquareKit.SheafImage
