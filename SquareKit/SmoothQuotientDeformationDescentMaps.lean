import SquareKit.SheafActionQuotientDescentCategory
import SquareKit.SmoothQuotientDeformationCocycle

/-! Deformation descent respects the actual arrows of quotient cocycles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Local compatibility descends along the selected quotient arrow, not just
along an equality of its endpoints or its action on the base. -/
theorem CocycleDatum.descend_map (d e : CocycleDatum (a := a) A)
    (h : Descent.Map d.quotient e.quotient)
    (hh : transport h.localArrow d.localDeformation = e.localDeformation) :
    transport h.arrow d.descend = e.descend := by
  apply e.unique
  rw [transport_restrict]
  rw [← transport_comp]
  change transport ((h.arrow.reindex (SplitSheaf.p A)).comp e.quotient.comparison)
    (restrict (SplitSheaf.p A) d.descend) = _
  rw [Descent.Map.comparison_naturality a A h]
  change transport (d.quotient.comparison ≫ h.localArrow)
    (restrict (SplitSheaf.p A) d.descend) = _
  rw [transport_comp, d.recover]
  exact hh

/-- Restricting a descended compatibility recovers the supplied local one. -/
theorem CocycleDatum.map_descend_iff (d e : CocycleDatum (a := a) A)
    (h : Descent.Map d.quotient e.quotient) :
    transport h.arrow d.descend = e.descend ↔
      transport h.localArrow d.localDeformation = e.localDeformation := by
  constructor
  · intro hh
    have he := congrArg (fun k => transport e.quotient.comparison
      (restrict (SplitSheaf.p A) k)) hh
    rw [transport_restrict, ← transport_comp] at he
    change transport ((h.arrow.reindex (SplitSheaf.p A)).comp e.quotient.comparison)
      (restrict (SplitSheaf.p A) d.descend) = _ at he
    rw [Descent.Map.comparison_naturality a A h] at he
    change transport (d.quotient.comparison ≫ h.localArrow)
      (restrict (SplitSheaf.p A) d.descend) = _ at he
    rw [transport_comp, d.recover, e.recover] at he
    exact he
  · exact d.descend_map e h

/-- The relative local fiber over a supplied quotient cocycle. Compatibility
is a matching equation, not a supplied global deformation or gluing result. -/
def CocycleDatum.Fiber (d : Descent.Datum (a := a) A) :=
  {h : Deformation d.localObject //
    ∀ (x : X.obj.Elements) (b c : A.family.obj x) (t : infinitesimal.obj.obj x.obj)
      (p : d.localObject.torsor.family.family.obj (SheafTorsor.Descent.point A x b)),
      h.map.hom.app x.obj (t, ⟨⟨x.val,c⟩,d.torsorDatum.transport x b c p⟩) =
        h.map.hom.app x.obj (t,⟨⟨x.val,b⟩,p⟩)}

def CocycleDatum.ofFiber (d : Descent.Datum (a := a) A) (h : Fiber d) :
    CocycleDatum (a := a) A where
  quotient := d
  localDeformation := h.val
  compatible := h.property

/-- A global deformation supplies matching local data by the chosen comparison. -/
def CocycleDatum.restrictFiber (d : Descent.Datum (a := a) A)
    (h : Deformation d.object) : Fiber d := by
  refine ⟨transport d.comparison (restrict (SplitSheaf.p A) h), ?_⟩
  intro x b c t p
  change h.map.hom.app x.obj (t, ⟨x.val,
      (SheafTorsor.Descent.evaluationEquiv d.torsorDatum x c).symm
        (d.torsorDatum.transport x b c p)⟩) =
    h.map.hom.app x.obj (t, ⟨x.val,
      (SheafTorsor.Descent.evaluationEquiv d.torsorDatum x b).symm p⟩)
  rw [SheafTorsor.Descent.evaluation_inverse_transport]

/-- Effective relative fiber descent, in both directions. -/
def CocycleDatum.fiberEquivalence (d : Descent.Datum (a := a) A) :
    Deformation d.object ≃ Fiber d where
  toFun := restrictFiber d
  invFun h := (ofFiber d h).descend
  left_inv h := ((ofFiber d (restrictFiber d h)).unique h rfl).symm
  right_inv h := Subtype.ext (ofFiber d h).recover

/-- The relative local fibers form a family on the actual cocycle category.
The objectwise equivalences supply its action, and the next theorem identifies
that action with transport along the given local arrow. -/
def CocycleDatum.fiberFamily : Descent.Datum (a := a) A ⥤ Type where
  obj d := Fiber d
  map {d e} h := ↾fun s => fiberEquivalence e (transport h.arrow ((fiberEquivalence d).symm s))
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro s
    change fiberEquivalence d (transport (Descent.Map.ident d).arrow
      ((fiberEquivalence d).symm s)) = s
    rw [Descent.Map.arrow_ident]
    change fiberEquivalence d (transport (𝟙 d.object) ((fiberEquivalence d).symm s)) = s
    rw [transport_id, Equiv.apply_symm_apply]
  map_comp {d e r} h k := by
    apply ConcreteCategory.hom_ext
    intro s
    change fiberEquivalence r (transport (h.comp k).arrow ((fiberEquivalence d).symm s)) =
      fiberEquivalence r (transport k.arrow ((fiberEquivalence e).symm
        (fiberEquivalence e (transport h.arrow ((fiberEquivalence d).symm s)))))
    rw [Equiv.symm_apply_apply, Descent.Map.arrow_comp]
    exact congrArg (fiberEquivalence r) (transport_comp h.arrow k.arrow _)

/-- The constructed family map is exactly local-arrow transport. -/
theorem CocycleDatum.fiberFamily_map_val {d e : Descent.Datum (a := a) A}
    (h : Descent.Map d e) (s : Fiber d) :
    ((fiberFamily.map h) s).val = transport h.localArrow s.val := by
  change transport e.comparison
    (restrict (SplitSheaf.p A) (transport h.arrow (ofFiber d s).descend)) = _
  rw [transport_restrict, ← transport_comp]
  change transport ((h.arrow.reindex (SplitSheaf.p A)).comp e.comparison)
    (restrict (SplitSheaf.p A) (ofFiber d s).descend) = _
  rw [Descent.Map.comparison_naturality a A h]
  change transport (d.comparison ≫ h.localArrow)
    (restrict (SplitSheaf.p A) (ofFiber d s).descend) = _
  rw [transport_comp]
  exact congrArg (transport h.localArrow) (ofFiber d s).recover

/-- Relative deformation descent is natural on all compatible local arrows. -/
def CocycleDatum.fiberComparison :
    Descent.descentFunctor a A ⋙ family a X ≅ fiberFamily (a := a) (A := A) :=
  NatIso.ofComponents (fun d => (fiberEquivalence d).toIso) (by
    intro d e h
    apply ConcreteCategory.hom_ext
    intro s
    change fiberEquivalence e (transport h.arrow s) =
      fiberEquivalence e (transport h.arrow ((fiberEquivalence d).symm (fiberEquivalence d s)))
    rw [Equiv.symm_apply_apply])

end SquareKit.SmoothQuotientDeformations
