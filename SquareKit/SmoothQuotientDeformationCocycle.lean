import SquareKit.SmoothQuotientDeformationDescent

/-! Descent of a quotient object together with its deformation. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite SheafRelation
set_option backward.isDefEq.respectTransparency false
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
local notation "D" => SmoothOpenSite.infinitesimal

/-- Local deformation values agree under the actual torsor cocycle. Neither a
global quotient object nor a global deformation is a field. -/
structure CocycleDatum (A : SplitSheaf.Ty X) where
  quotient : SheafActionQuotient.Descent.Datum (a := a) A
  localDeformation : Deformation quotient.localObject
  compatible (x : X.obj.Elements) (b c : A.family.obj x) (t : (D).obj.obj x.obj)
    (p : quotient.localObject.torsor.family.family.obj (SheafTorsor.Descent.point A x b)) :
    localDeformation.map.hom.app x.obj
      (t, ⟨⟨x.val,c⟩,quotient.torsorDatum.transport x b c p⟩) =
    localDeformation.map.hom.app x.obj (t,⟨⟨x.val,b⟩,p⟩)

namespace CocycleDatum
variable (d : CocycleDatum (a := a) A)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Pull the local deformation back through the proved descent comparison. -/
def overGlobal : Deformation (reindex d.quotient.object (SplitSheaf.p A)) :=
  transport (Arrow.inverse d.quotient.comparison) d.localDeformation

theorem matching (U : SmoothPresentationSite.Siteᵒᵖ)
    (p q : (product D (SplitSheaf.Ext
      (reindex d.quotient.object (SplitSheaf.p A)).torsor.family)).obj.obj U)
    (h : (cover d.quotient.object (SplitSheaf.p A)).hom.app U p =
      (cover d.quotient.object (SplitSheaf.p A)).hom.app U q) :
    d.overGlobal.map.hom.app U p = d.overGlobal.map.hom.app U q := by
  rcases p with ⟨t,⟨⟨x,b⟩,p⟩⟩
  rcases q with ⟨s,⟨⟨y,c⟩,q⟩⟩
  have ht : t = s := congrArg Prod.fst h
  subst s
  have he := congrArg Prod.snd h
  have hx : x = y := congrArg Sigma.fst he
  subst y
  have hp : p = q := eq_of_heq (Sigma.mk.inj_iff.mp he).2
  subst q
  let z := X.obj.elementsMk U x
  change d.localDeformation.map.hom.app U
    (t,⟨⟨x,b⟩,SheafTorsor.Descent.evaluationEquiv d.quotient.torsorDatum z b p⟩) =
    d.localDeformation.map.hom.app U
    (t,⟨⟨x,c⟩,SheafTorsor.Descent.evaluationEquiv d.quotient.torsorDatum z c p⟩)
  rw [← SheafTorsor.Descent.evaluation_transport d.quotient.torsorDatum z b c p]
  exact (d.compatible z b c t _).symm

def fixedDatum : DescentDatum d.quotient.object (SplitSheaf.p A) where
  localDeformation := d.overGlobal
  compatible := d.matching

/-- The descended quotient object carries the descended deformation. -/
def descend : Deformation d.quotient.object := d.fixedDatum.descend

theorem recover : transport d.quotient.comparison (restrict (SplitSheaf.p A) d.descend) =
    d.localDeformation := by
  rw [show restrict (SplitSheaf.p A) d.descend = d.overGlobal from d.fixedDatum.descend_restrict]
  change transport d.quotient.comparison
    (transport (Arrow.inverse d.quotient.comparison) d.localDeformation) = _
  rw [← transport_comp]
  have he := (Arrow.toIso d.quotient.comparison).inv_hom_id
  change transport ((Arrow.toIso d.quotient.comparison).inv ≫
    (Arrow.toIso d.quotient.comparison).hom) d.localDeformation = _
  rw [he]
  exact transport_id d.localDeformation

/-- Recovery determines the global deformation uniquely. -/
theorem unique (h : Deformation d.quotient.object)
    (hh : transport d.quotient.comparison (restrict (SplitSheaf.p A) h) =
      d.localDeformation) : h = d.descend := by
  apply d.fixedDatum.descend_unique h
  have he := congrArg (transport (Arrow.inverse d.quotient.comparison)) hh
  rw [← transport_comp] at he
  have hc := (Arrow.toIso d.quotient.comparison).hom_inv_id
  change transport ((Arrow.toIso d.quotient.comparison).hom ≫
    (Arrow.toIso d.quotient.comparison).inv) (restrict (SplitSheaf.p A) h) =
    d.overGlobal at he
  rw [hc, transport_id] at he
  exact he

end CocycleDatum
end SquareKit.SmoothQuotientDeformations
