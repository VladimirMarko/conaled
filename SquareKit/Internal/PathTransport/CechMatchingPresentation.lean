import SquareKit.Internal.PathTransport.CechMatchingCone
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFunctor

/-! Equality adapters for presentations of the same matching construction. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
universe u v w
variable {D E : Diagram.{u,v}} {C : Type w} [Category.{u} C]
theorem coneFunctor_heq (q : D = E)
    {L : C ⥤ D.localCategory} {K : C ⥤ E.localCategory} (qL : HEq L K)
    {η : L ⋙ D.first ≅ L ⋙ D.second} {θ : K ⋙ E.first ≅ K ⋙ E.second}
    (qη : HEq η θ) (h : ConeLaws L η) (k : ConeLaws K θ) :
    HEq (coneFunctor L η h) (coneFunctor K θ k) := by
  subst E
  cases eq_of_heq qL
  cases eq_of_heq qη
  rfl

theorem functor_equivalence_iff (q : D = E)
    {F : C ⥤ Datum D} {G : C ⥤ Datum E} (qF : HEq F G) :
    F.IsEquivalence ↔ G.IsEquivalence := by
  subst E
  cases eq_of_heq qF
  rfl

theorem mappedFunctor_heq {D E T U : StrictDiagram.{u,v}}
    (q : D = E) (r : T = U)
    {F : C ⥤ Datum D.toDiagram} {G : C ⥤ Datum E.toDiagram} (qF : HEq F G)
    {S : StrictMap D T} {R : StrictMap E U} (qS : HEq S R) :
    HEq (F ⋙ S.functor) (G ⋙ R.functor) := by
  subst E
  subst U
  cases eq_of_heq qF
  cases eq_of_heq qS
  rfl

namespace Comprehension
variable {D : StrictDiagram.{u,u}}
theorem total_eq {A B : FamilyData D} (q : A = B)
    (h : A.Coherence) (k : B.Coherence) : A.total h = B.total k := by
  subst B
  rfl

variable {Z W : Type v} [Category.{u} Z] [Category.{u} W]
theorem fixedBase_precomp_equivalence_iff {A B : FamilyData D} (q : A = B)
    (h : A.Coherence) (k : B.Coherence)
    {F : Z ⥤ Datum (A.total h).toDiagram}
    {G : Z ⥤ Datum (B.total k).toDiagram} (qF : HEq F G)
    (J : W ⥤ Z) (d : Datum D.toDiagram)
    (hf : (J ⋙ F) ⋙ (A.projection h).functor = (Functor.const W).obj d)
    (hg : (J ⋙ G) ⋙ (B.projection k).functor = (Functor.const W).obj d) :
    (fixedBaseFunctor A h (J ⋙ F) d hf).IsEquivalence ↔
      (fixedBaseFunctor B k (J ⋙ G) d hg).IsEquivalence := by
  subst B
  cases eq_of_heq qF
  rfl
end Comprehension
end SquareKit.Internal.PathTransport.CechMatching
