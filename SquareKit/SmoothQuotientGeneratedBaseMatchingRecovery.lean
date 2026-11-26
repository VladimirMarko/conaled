import SquareKit.SmoothQuotientGeneratedBaseMatching

/-! The actual generated base binder has constant relative matching coefficients,
with the primitive quotient datum and its local arrows retained. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ) (A : SplitSheaf.Ty X)

theorem liftedCoefficientIso_localObject (e : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) :
    ((liftedCoefficientIso a A).hom.obj e).localObject =
      AsSmall.up.obj (AsSmall.down.obj e).localObject := rfl

theorem liftedCoefficientIso_overlap (e : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) :
    ((liftedCoefficientIso a A).hom.obj e).overlap.hom =
      AsSmall.up.{0,1,0}.map (AsSmall.down.obj e).overlap.hom := rfl

theorem liftedCoefficientIso_localArrow
    {e f : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)} (g : e ⟶ f) :
    ((liftedCoefficientIso a A).hom.map g).localArrow =
      AsSmall.up.{0,1,0}.map (AsSmall.down.map g).localArrow := rfl

theorem baseCoefficientEquivalence_localObject_heq (e : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) :
    HEq (((baseCoefficientEquivalence a A).functor.obj e).localObject)
      (((liftedCoefficientIso a A).hom.obj e).localObject) :=
  (baseCoefficientComparison a A).localObject e

@[simp] theorem baseCoefficientEquivalence_localObject (e : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) :
    AsSmall.down.obj (((baseCoefficientEquivalence a A).functor.obj e).localObject) =
      (AsSmall.down.obj e).localObject := by
  have h := (eq_of_heq (baseCoefficientEquivalence_localObject_heq a A e)).trans (liftedCoefficientIso_localObject a A e)
  exact congrArg (fun z : AsSmall.{0} (Object a (SplitSheaf.extension A)) => AsSmall.down.obj z) h

/-- Recovery of the complete selected overlap across the presentation change. -/
theorem baseCoefficientComparison_overlap (e : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) :
    HEq (((baseCoefficientComparison a A).equivalence.functor.obj e).overlap.hom)
      (((liftedCoefficientIso a A).hom.obj e).overlap.hom) :=
  (baseCoefficientComparison a A).overlap e

/-- Recovery of the complete selected local arrow across the presentation change. -/
theorem baseCoefficientComparison_localArrow
    {e f : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)} (g : e ⟶ f) :
    HEq (((baseCoefficientComparison a A).equivalence.functor.map g).localArrow)
      (((liftedCoefficientIso a A).hom.map g).localArrow) :=
  (baseCoefficientComparison a A).localArrow g

end SquareKit.SmoothQuotientGeneratedMatching
