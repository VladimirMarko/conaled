import SquareKit.SmoothQuotientGeneratedBaseMatchingRecovery

noncomputable section
namespace Examples.GeneratedBaseMatching
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open Internal.PathTransport SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ) (A : SplitSheaf.Ty X)

/-- An arbitrary primitive matching object retains its local quotient object. -/
example (e : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) :
    AsSmall.down.obj (((baseCoefficientEquivalence a A).functor.obj e).localObject) =
      (AsSmall.down.obj e).localObject := baseCoefficient_local a A e

/-- A selected primitive matching arrow survives the universe bridge unchanged. -/
example {e f : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)} (g : e ⟶ f) :
    HEq (((baseCoefficientComparison a A).equivalence.functor.map g).localArrow)
      (((liftedCoefficientIso a A).hom.map g).localArrow) := baseCoefficient_localArrow a A g

/-- The actual base-binder fiber recovers every independently supplied primitive
matching datum over every independently supplied context datum. -/
example (d : Datum a hΓ A)
    (e : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) :
    ((basePrimitiveFamilyIso a hΓ A).hom.app d).obj
      (((basePrimitiveFamilyIso a hΓ A).inv.app d).obj e) = e :=
  CategoryTheory.Functor.congr_obj
    ((basePrimitiveFamilyIso a hΓ A).inv_hom_id_app d) e

/-- The natural comparison covers every context arrow, not only identities. -/
example {d e : Datum a hΓ A} (f : d ⟶ e) :
    (relativeMatchingFamily a hΓ (.base hΓ) A).map f ⋙
      (basePrimitiveFamilyIso a hΓ A).hom.app e =
        (basePrimitiveFamilyIso a hΓ A).hom.app d ⋙
          ((CategoryTheory.Functor.const (Datum a hΓ A)).obj
            (Grpd.of (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)))).map f :=
  (basePrimitiveFamilyIso a hΓ A).hom.naturality f

/-- The extension comparison is an equivalence with the actual generated
extended-context matching groupoid. -/
example : (baseComprehensionEquivalence a hΓ A).functor.IsEquivalence := inferInstance

end Examples.GeneratedBaseMatching
