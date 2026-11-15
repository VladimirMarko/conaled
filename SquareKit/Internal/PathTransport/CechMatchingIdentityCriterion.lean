import SquareKit.Internal.PathTransport.DiscreteHomEvaluation
import SquareKit.Internal.PathTransport.CechMatchingArrowComparison

/-! Identity effectivity from independently supplied values and exact local recovery. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable {Z : Type u} [Category.{u} Z]
variable (E : Z ⥤ Datum (A.total h).toDiagram) (d : Datum D.toDiagram)
variable (he : E ⋙ (A.projection h).functor = (Functor.const Z).obj d)

theorem identityValues_isEquivalence [ (fixedBaseFunctor A h E d he).Full]
    [ (fixedBaseFunctor A h E d he).Faithful]
    (x y : Z) (e f : Datum (A.total h).toDiagram)
    (hep : (A.projection h).functor.obj e = d) (hfp : (A.projection h).functor.obj f = d)
    (ex : E.obj x = e) (ey : E.obj y = f)
    {I : Type v}
    (k : I ≃ {p : e ⟶ f // (A.projection h).functor.map p ≫ eqToHom hfp = eqToHom hep})
    (V : Discrete (x ⟶ y) ⥤ Discrete I)
    (chosen : (x ⟶ y) → (e.localObject ⟶ f.localObject))
    (raw : (x ⟶ y) → ((E.obj x).localObject ⟶ (E.obj y).localObject))
    (hchosen : ∀ p, (k (V.obj (Discrete.mk p)).as).val.localArrow = chosen p)
    (htransport : ∀ p, chosen p = eqToHom (congrArg Datum.localObject ex.symm) ≫
      raw p ≫ eqToHom (congrArg Datum.localObject ey))
    (hraw : ∀ p, (E.map p).localArrow = raw p) : V.IsEquivalence := by
  have hx : fixedBaseObject A h E d he x = Fiber.ofDatum e hep := by
    apply Fiber.datum_injective
    change (Fiber.ofDatum _ _).datum = _
    rw [Fiber.datum_ofDatum, Fiber.datum_ofDatum]
    exact ex
  have hy : fixedBaseObject A h E d he y = Fiber.ofDatum f hfp := by
    apply Fiber.datum_injective
    change (Fiber.ofDatum _ _).datum = _
    rw [Fiber.datum_ofDatum, Fiber.datum_ofDatum]
    exact ey
  apply discreteHomEvaluation_isEquivalence (fixedBaseFunctor A h E d he) x y hx hy
    (k.trans (ofDatumArrowEquiv hep hfp)) V
  intro p
  refine fixedBaseArrow_endpoint A h E d he p e f hep hfp ex ey hx hy
    (k (V.obj (Discrete.mk p)).as).val ?_ (k (V.obj (Discrete.mk p)).as).property
  exact Datum.Hom.eq_conjugate _ _ ex ey
    ((hchosen p).trans ((htransport p).trans
      (congrArg (fun q => eqToHom (congrArg Datum.localObject ex.symm) ≫ q ≫
        eqToHom (congrArg Datum.localObject ey)) (hraw p).symm)))

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
