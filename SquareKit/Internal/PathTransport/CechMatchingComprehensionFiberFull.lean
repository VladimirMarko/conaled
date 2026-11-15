import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberArrowEquiv

/-! Fullness of fiber extraction follows from lifting exactly the vertical total arrows. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable {Z : Type v} [Category.{u} Z]
variable (E : Z ⥤ Datum (A.total h).toDiagram) (d : Datum D.toDiagram)
variable (he : E ⋙ (A.projection h).functor = (Functor.const Z).obj d)

theorem fixedBaseFunctor_full
    (lift : ∀ (x y : Z) (p : E.obj x ⟶ E.obj y),
      (A.projection h).functor.map p ≫ eqToHom (Functor.congr_obj he y) =
        eqToHom (Functor.congr_obj he x) → ∃ f : x ⟶ y, E.map f = p) :
    (fixedBaseFunctor A h E d he).Full where
  map_surjective {x y} q := by
    let k := ofDatumArrowEquiv (Functor.congr_obj he x) (Functor.congr_obj he y)
    obtain ⟨f,hf⟩ := lift x y (k.symm q).val (k.symm q).property
    refine ⟨f, ?_⟩
    apply Fiber.Hom.ext
    change eqToHom _ ≫ E.map f ≫ eqToHom _ = q.matchingArrow
    rw [hf]
    exact congrArg Fiber.Hom.matchingArrow (k.apply_symm_apply q)

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
