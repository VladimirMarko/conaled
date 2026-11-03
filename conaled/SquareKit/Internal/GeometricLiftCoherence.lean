import SquareKit.Internal.SliceSourceChange
import SquareKit.Internal.SliceRebase

/-! Coherent source substitution on arbitrary geometric lift categories. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Functor
universe vF vB vC vG vH uF uB uC uG uH
variable {F : Type uF} {B : Type uB} {C : Type uC} {G : Type uG} {H : Type uH}
variable [Category.{vF} F] [Category.{vB} B] [Category.{vC} C]
variable [Category.{vG} G] [Category.{vH} H]
variable {h : GeometricMorphism F B} {π : GeometricMorphism C B}

/-- A compatible inverse-image isomorphism is an isomorphism of lifts. -/
def Lift.isoMk {k l : Lift h π} (e : k.morphism.inverseImage ≅ l.morphism.inverseImage)
    (over : whiskerLeft π.inverseImage e.hom ≫ l.comparison.hom = k.comparison.hom) : k ≅ l where
  hom := ⟨e.hom, over⟩
  inv := ⟨e.inv, by
    rw [← over]
    apply NatTrans.ext
    funext X
    change e.inv.app _ ≫ (e.hom.app _ ≫ _) = _
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]⟩
  hom_inv_id := Lift.Hom.ext e.hom_inv_id
  inv_hom_id := Lift.Hom.ext e.inv_hom_id

/-- Identity source substitution compares with the identity after rebasing by the unitor. -/
def Lift.sourceIdentityIso :
    Lift.precompFunctor (h := h) (π := π) (identity F) ⋙
      Lift.rebaseFunctor (h := (identity F).comp h) (h' := h)
        (Functor.rightUnitor h.inverseImage) ≅ 𝟭 (Lift h π) :=
  NatIso.ofComponents (fun k => Lift.isoMk (Functor.rightUnitor k.morphism.inverseImage) (by
    apply NatTrans.ext
    funext X
    simp [Lift.precompFunctor, Lift.precomp, Lift.rebase, Lift.rebaseFunctor, identity]
    change 𝟙 _ ≫ k.comparison.hom.app X = 𝟙 _ ≫ k.comparison.hom.app X ≫ 𝟙 _
    simp)) (by
      intro k l α
      apply Lift.Hom.ext
      apply NatTrans.ext
      funext X
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Associative source substitution compares after rebasing by the associator. -/
def Lift.sourceCompIso (f : GeometricMorphism G F) (g : GeometricMorphism H G) :
    (Lift.precompFunctor (h := h) (π := π) f ⋙ Lift.precompFunctor g) ⋙
      Lift.rebaseFunctor (h := g.comp (f.comp h)) (h' := (g.comp f).comp h)
        (Functor.associator h.inverseImage f.inverseImage g.inverseImage) ≅
      Lift.precompFunctor (g.comp f) :=
  NatIso.ofComponents (fun k => Lift.isoMk
    (Functor.associator k.morphism.inverseImage f.inverseImage g.inverseImage) (by
      apply NatTrans.ext
      funext X
      simp [Lift.precompFunctor, Lift.precomp, Lift.rebase, Lift.rebaseFunctor, comp])) (by
        intro k l α
        apply Lift.Hom.ext
        apply NatTrans.ext
        funext X
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SquareKit.Internal.GeometricMorphism
