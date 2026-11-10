import SquareKit.Internal.PathTransport.CechMatchingCanonical

/-! Strict local squares preserve the complete canonical matching functor. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D E : StrictDiagram.{u,v}} {C B : Type v} [Category.{u} C] [Category.{u} B]

theorem equalFunctor_precompose (T : C ⥤ B) (U : B ⥤ E.localCategory)
    (hU : U ⋙ E.first = U ⋙ E.second)
    (hTU : (T ⋙ U) ⋙ E.first = (T ⋙ U) ⋙ E.second) :
    T ⋙ E.equalFunctor U hU = E.equalFunctor (T ⋙ U) hTU := rfl

theorem canonical_square (F : StrictMap D E) (R : C ⥤ D.localCategory)
    (T : C ⥤ B) (U : B ⥤ E.localCategory)
    (hD : R ⋙ D.first = R ⋙ D.second) (hE : U ⋙ E.first = U ⋙ E.second)
    (q : R ⋙ F.localMap = T ⋙ U) :
    D.equalFunctor R hD ⋙ F.functor = T ⋙ E.equalFunctor U hE := by
  have hRU : (R ⋙ F.localMap) ⋙ E.first = (R ⋙ F.localMap) ⋙ E.second := by
    rw [q, Functor.assoc, Functor.assoc, hE]
  rw [StrictMap.equalFunctor_map F R hD hRU]
  have hh : (T ⋙ U) ⋙ E.first = (T ⋙ U) ⋙ E.second := by
    rw [Functor.assoc, Functor.assoc, hE]
  rw [equalFunctor_precompose T U hE hh]
  congr 1
end SquareKit.Internal.PathTransport.CechMatching
