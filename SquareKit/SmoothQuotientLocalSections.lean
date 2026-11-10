import SquareKit.SmoothQuotientGlobalSections
import SquareKit.SmoothQuotientDeformationBaseChange
import SquareKit.SmoothQuotientDeformationRestriction

/-! Assemble deformation sections from covering-context sections with explicit
cocycle matching. Parameter-compatible local recovery is a further obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The entire fiber square includes the selected quotient natural isomorphism.
It does not replace that isomorphism by equality of quotient objects. -/
theorem CocycleDatum.fiberBaseChange_square (f : Y ⟶ X) :
    Functor.whiskerLeft (Descent.descentFunctor a A) (restrictionFamily f) ≫
      Functor.whiskerRight (Descent.baseChangeComparison f).hom (family a Y) ≫
      Functor.whiskerLeft (Descent.baseChange f)
        (fiberComparison (a := a) (A := SplitSheaf.tySub A f)).hom =
    (fiberComparison (a := a) (A := A)).hom ≫ fiberBaseChange f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro h
  exact fiberBaseChange_comparison d f h

namespace LocalSection

/-- The section's local values satisfy the actual transport equation of every
quotient cocycle. This states local matching, without a global reconstruction. -/
def Matching (s : Section (setFamily (family a (SplitSheaf.Ext A)))) : Prop :=
  ∀ (d : Descent.Datum (a := a) A) (x : X.obj.Elements) (b c : A.family.obj x)
    (t : infinitesimal.obj.obj x.obj)
    (p : d.localObject.torsor.family.family.obj (SheafTorsor.Descent.point A x b)),
    ((s.obj d.localObject).as).map.hom.app x.obj
      (t, ⟨⟨x.val,c⟩,d.torsorDatum.transport x b c p⟩) =
    ((s.obj d.localObject).as).map.hom.app x.obj (t,⟨⟨x.val,b⟩,p⟩)

variable (s : Section (setFamily (family a (SplitSheaf.Ext A)))) (hs : Matching s)

/-- A local section yields compatible local deformation data at each cocycle. -/
def datum (d : Descent.Datum (a := a) A) : CocycleDatum (a := a) A where
  quotient := d
  localDeformation := (s.obj d.localObject).as
  compatible := hs d

private def setSection {Γ : Type*} [Category* Γ] (F : Γ ⥤ Type*)
    (x : ∀ γ, F.obj γ) (hx : ∀ {γ δ} (f : γ ⟶ δ), F.map f (x γ) = x δ) :
    Section (setFamily F) where
  obj γ := Discrete.mk (x γ)
  map f := eqToHom (congrArg Discrete.mk (hx f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Its action on every local quotient arrow supplies the required section
naturality on the cocycle category. -/
def onCocycles : Section (setFamily (CocycleDatum.fiberFamily (a := a) (A := A))) :=
  setSection _ (fun d => ⟨(s.obj d.localObject).as, hs d⟩) (by
    intro d e h
    apply Subtype.ext
    rw [CocycleDatum.fiberFamily_map_val]
    exact Discrete.eq_of_hom (s.map h.localArrow))

/-- Glue the section assembled from the covering-context section and matching.
The input is not a previously constructed section on the cocycle category. -/
def glue : Section (setFamily (family a X)) :=
  CocycleDatum.globalSection (onCocycles s hs)

/-- Recovery on every local object supplied with its cocycle data. Recovery
for arbitrary local objects without a chosen cocycle is not asserted here. -/
theorem glue_recover (d : Descent.Datum (a := a) A) :
    transport d.comparison (restrict (SplitSheaf.p A)
      (((glue s hs).obj d.object).as)) = (s.obj d.localObject).as :=
  congrArg Subtype.val (CocycleDatum.globalSection_recoverFiber (onCocycles s hs) d)

/-- At a descended context, the assembled section is precisely deformation
gluing of the supplied local section value. -/
theorem glue_eq_descend (d : Descent.Datum (a := a) A) :
    ((glue s hs).obj d.object).as = (datum s hs d).descend :=
  (datum s hs d).unique _ (glue_recover s hs d)

/-- Compatible covering-context section values remain compatible after gluing
and changing parameter, through the chosen comparison of descended contexts. -/
theorem glue_baseChange (f : Y ⟶ X)
    (t : Section (setFamily (family a (SplitSheaf.Ext (SplitSheaf.tySub A f)))))
    (ht : Matching t) (d : Descent.Datum (a := a) A)
    (hlocal : restrict (SplitSheaf.lift A f) (s.obj d.localObject).as =
      (t.obj (d.baseChange f).localObject).as) :
    transport (d.baseChangeComparison f)
        (restrict f (((glue s hs).obj d.object).as)) =
      ((glue t ht).obj (d.baseChange f).object).as := by
  rw [glue_eq_descend, glue_eq_descend]
  exact ((datum s hs d).baseChange_descend f).trans
    ((datum t ht (d.baseChange f)).unique _
      (((datum s hs d).baseChange f).recover.trans hlocal))

end LocalSection
end SquareKit.SmoothQuotientDeformations
