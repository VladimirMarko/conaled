import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFunctor

noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
variable {d : Datum D.toDiagram} {e f : Datum (A.total h).toDiagram}

/-- A total arrow over the common base is an arrow of the reconstructed fiber. -/
def ofDatumArrow (he : (A.projection h).functor.obj e = d)
    (hf : (A.projection h).functor.obj f = d) (p : e ⟶ f)
    (hp : (A.projection h).functor.map p ≫ eqToHom hf = eqToHom he) :
    Fiber.ofDatum e he ⟶ Fiber.ofDatum f hf where
  matchingArrow := eqToHom (Fiber.datum_ofDatum e he) ≫ p ≫
    eqToHom (Fiber.datum_ofDatum f hf).symm
  vertical := by
    have hv := congrArg (fun k => k.localArrow) hp
    simp only [Datum.comp_localArrow, Datum.eqToHom_localArrow] at hv
    change p.localArrow.base ≫ eqToHom (congrArg Datum.localObject hf) =
      eqToHom (congrArg Datum.localObject he) at hv
    let P := (A.projection h).functor ⋙ Datum.localFunctor
    change P.map (eqToHom (Fiber.datum_ofDatum e he) ≫ p ≫
      eqToHom (Fiber.datum_ofDatum f hf).symm) = _
    simp only [Functor.map_comp, eqToHom_map]
    change eqToHom _ ≫ p.localArrow.base ≫ eqToHom _ = _
    change eqToHom (congrArg Datum.localObject he).symm ≫ p.localArrow.base ≫
      eqToHom (congrArg Datum.localObject hf) = 𝟙 d.localObject
    erw [hv]
    simp

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
