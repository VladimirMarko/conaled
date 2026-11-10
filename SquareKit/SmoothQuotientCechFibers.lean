import SquareKit.SheafActionQuotientCechEquivalence
import SquareKit.SmoothQuotientDeformationDescentMaps

/-! Primitive deformation matching on independent Čech quotient data.
The action is local transport; no global deformation is supplied or used
in defining the matching fiber or its action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations.Cech
open CategoryTheory SheafActionQuotient SmoothOpenSite SplitSheaf.Cech
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}

/-- Local deformations with the actual overlap transport equation. -/
def Fiber (d : SheafActionQuotient.Cech.Datum (a := a) A) :=
  {h : Deformation d.localObject //
    transport d.overlap.hom (restrict (first A) h) = restrict (second A) h}

/-- The overlap equation is equivalent to the pointwise cocycle equation. -/
def fiberEquiv (d : SheafActionQuotient.Cech.Datum (a := a) A) :
    Fiber d ≃ CocycleDatum.Fiber d.toDescent where
  toFun h := ⟨h.val, by
    intro x b c t p
    have he := congrArg (fun k => k.map.hom.app x.obj
      (t, ⟨⟨⟨x.val,b⟩,c⟩,d.toDescent.torsorDatum.transport x b c p⟩)) h.property
    have hi := congrArg (fun k => k.app
      ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩) p)
      d.overlap.hom.torsorArrow.iso.hom_inv_id
    change h.val.map.hom.app x.obj (t, ⟨⟨x.val,b⟩,
      d.overlap.hom.torsorArrow.iso.inv.app
        ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩)
        (d.overlap.hom.torsorArrow.iso.hom.app
          ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩) p)⟩) = _ at he
    change d.overlap.hom.torsorArrow.iso.inv.app
      ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩)
      (d.overlap.hom.torsorArrow.iso.hom.app
        ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩) p) = p at hi
    rw [hi] at he
    exact he.symm⟩
  invFun h := ⟨h.val, by
    apply Deformation.ext
    ext U z
    rcases z with ⟨t, ⟨⟨⟨x,b⟩,c⟩,q⟩⟩
    have he := h.property (X.obj.elementsMk U x) b c t
      (d.overlap.hom.torsorArrow.iso.inv.app
        ((double A).obj.elementsMk U ⟨⟨x,b⟩,c⟩) q)
    have hi := congrArg (fun k => k.app
      ((double A).obj.elementsMk U ⟨⟨x,b⟩,c⟩) q)
      d.overlap.hom.torsorArrow.iso.inv_hom_id
    change d.overlap.hom.torsorArrow.iso.hom.app _
      (d.overlap.hom.torsorArrow.iso.inv.app _ q) = q at hi
    change h.val.map.hom.app U (t, ⟨⟨x,c⟩,
      d.overlap.hom.torsorArrow.iso.hom.app _
        (d.overlap.hom.torsorArrow.iso.inv.app _ q)⟩) = _ at he
    rw [hi] at he
    exact he.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Transport uses the supplied local arrow, independently of effectivity. -/
def map {d e : SheafActionQuotient.Cech.Datum (a := a) A}
    (k : d ⟶ e) (h : Fiber d) : Fiber e := ⟨transport k.localArrow h.val, by
  rw [transport_restrict, ← transport_comp]
  change transport ((k.localArrow.reindex (first A)).comp e.overlap.hom) _ = _
  rw [k.commutes]
  change transport (d.overlap.hom ≫ k.localArrow.reindex (second A)) _ = _
  rw [transport_comp, h.property, ← transport_restrict]⟩

/-- The independent matching fibers form a family on the complete Čech category. -/
def family : SheafActionQuotient.Cech.Datum (a := a) A ⥤ Type where
  obj := Fiber
  map k := ↾(map k)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro h
    apply Subtype.ext
    exact transport_id h.val
  map_comp k l := by
    apply ConcreteCategory.hom_ext
    intro h
    apply Subtype.ext
    exact transport_comp k.localArrow l.localArrow h.val

variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Identification with the existing cocycle family is natural on actual
local arrows, not merely an objectwise bijection. -/
def comparison : family (a := a) (A := A) ≅
    SheafActionQuotient.Cech.toDescent ⋙ CocycleDatum.fiberFamily :=
  NatIso.ofComponents (fun d => (fiberEquiv d).toIso) (by
    intro d e k
    apply ConcreteCategory.hom_ext
    intro h
    apply Subtype.ext
    change transport k.localArrow h.val =
      ((CocycleDatum.fiberFamily.map k.toDescent) (fiberEquiv d h)).val
    rw [CocycleDatum.fiberFamily_map_val]
    rw [show k.toDescent.localArrow = k.localArrow from
      SheafActionQuotient.Cech.mapOfDescent_toDescent_localArrow k]
    rfl)

end SquareKit.SmoothQuotientDeformations.Cech
