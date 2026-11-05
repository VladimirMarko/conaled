import SquareKit.Internal.PathTransport.StrictTwoTransformation
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Strict B]
omit [Strict A] [Strict B] in
/-- Extensional equality of raw higher-functor data retains all dependent boundaries. -/
theorem prelaxData_ext (D E : PrelaxFunctorStruct A B)
    (ho : ∀ x, D.obj x = E.obj x)
    (hm : ∀ {x y} (p : x ⟶ y), HEq (D.map p) (E.map p))
    (hc : ∀ {x y} {p q : x ⟶ y} (α : p ⟶ q), HEq (D.map₂ α) (E.map₂ α)) : D = E := by
  rcases D with ⟨⟨Do,Dm⟩,Dc⟩
  rcases E with ⟨⟨Eo,Em⟩,Ec⟩
  have hO : Do = Eo := funext ho
  subst Eo
  have hM : @Dm = @Em := by
    funext x y p
    exact eq_of_heq (hm p)
  subst Em
  have hC : @Dc = @Ec := by
    funext x y p q α
    exact eq_of_heq (hc α)
  subst Ec
  rfl

omit [Strict A] [Strict B] in
/-- Equality of raw object, arrow, and cell operations determines a strict functor. -/
theorem strictFunctorData_ext {F G : StrictPseudofunctor A B}
    (h : F.toPrelaxFunctorStruct = G.toPrelaxFunctorStruct) : F = G := by
  apply StrictTwoTransformation.functor_ext
  have aux (H K : PrelaxFunctor A B)
      (h : H.toPrelaxFunctorStruct = K.toPrelaxFunctorStruct) : H = K := by
    cases H
    cases K
    cases h
    rfl
  exact aux _ _ h

/-- Reuse all strict higher functor laws when only the presentation of its data changes.
The caller proves equality of object, arrow, and cell operations; no coherence law
is requested again. The returned operations are definitionally the supplied data. -/
def strictFunctorOfEqualData (F : StrictPseudofunctor A B)
    (D : PrelaxFunctorStruct A B) (e : D = F.toPrelaxFunctorStruct) :
    StrictPseudofunctor A B := StrictPseudofunctor.mk'' {
  toPrelaxFunctorStruct := D
  map₂_id := by cases e; exact F.map₂_id
  map₂_comp := by cases e; exact F.map₂_comp
  map_id := by cases e; exact F.map_id
  map_comp := by cases e; exact F.map_comp
  map₂_whisker_left := by
    cases e
    intro a b c f g g' α
    simpa only [F.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
      F.map₂_whisker_left f α
  map₂_whisker_right := by
    cases e
    intro a b c f f' α g
    simpa only [F.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
      F.map₂_whisker_right α g
}
/-- Data normalization preserves the exact original strict higher functor. -/
theorem strictFunctorOfEqualData_eq (F : StrictPseudofunctor A B)
    (D : PrelaxFunctorStruct A B) (e : D = F.toPrelaxFunctorStruct) :
    strictFunctorOfEqualData F D e = F := by
  cases e
  exact StrictTwoTransformation.functor_ext rfl
end SquareKit.Internal.PathTransport
