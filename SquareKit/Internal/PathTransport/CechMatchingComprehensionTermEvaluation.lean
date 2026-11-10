import SquareKit.Internal.PathTransport.CechMatchingComprehensionEffectivity

/-! Whole section evaluation supplies endpoint recovery without concrete reduction. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable {C : Grpd.{u,u}} (F : C ⥤ Grpd.{u,u})
variable (E : Extend F ⥤ Datum (A.total h).toDiagram) (R : C ⥤ Datum D.toDiagram)
variable (square : E ⋙ (A.projection h).functor =
  Grothendieck.forget (F ⋙ Grpd.forgetToCat) ⋙ R)
variable (s : GroupoidModel.Section F) (T : Datum D.toDiagram ⥤ Datum (A.total h).toDiagram)
variable (ht : T ⋙ (A.projection h).functor = 𝟭 _)

structure TermEvaluationComparison where
  comparison : s.lift ⋙ E ≅ R ⋙ T
  endpoint : ∀ c, (Effectivity.fiber A h F E R square c).obj (s.obj c) =
    Fiber.ofDatum (T.obj (R.obj c)) (Functor.congr_obj ht (R.obj c))

def termEvaluationComparison (naturality : s.lift ⋙ E = R ⋙ T) :
    TermEvaluationComparison A h F E R square s T ht where
  comparison := eqToIso naturality
  endpoint c := by
    apply Fiber.datum_injective
    change (Fiber.ofDatum _ _).datum = (Fiber.ofDatum _ _).datum
    rw [Fiber.datum_ofDatum, Fiber.datum_ofDatum]
    exact Functor.congr_obj naturality c

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
