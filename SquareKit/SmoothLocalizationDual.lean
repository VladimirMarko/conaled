import SquareKit.SmoothLocalizationBaseChange
import SquareKit.SmoothPresentedDual

/-! Experimental compatibility of formal localization with the actual smooth dual extension.
The all-target construction uses the dual coproduct universal property, including its nilpotent coordinate. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PresentedLocalization
attribute [local instance] DualExtension.smoothStructure
variable {n m : ℕ}
variable {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

def dualBase (r : Fin m → Free n) (p : Free n) :
    Hom (DualNumber (Presentation.Carrier r)) (DualNumber (Carrier r p)) :=
  DualExtension.lift (Hom.comp DualExtension.inclusion (base r p)) DualNumber.eps DualNumber.eps_mul_eps

@[simp] theorem dualBase_inclusion (r : Fin m → Free n) (p : Free n) :
    Hom.comp (dualBase r p) DualExtension.inclusion = Hom.comp DualExtension.inclusion (base r p) :=
  DualExtension.lift_inclusion _ _ _
@[simp] theorem dualBase_eps (r : Fin m → Free n) (p : Free n) : dualBase r p DualNumber.eps = DualNumber.eps :=
  DualExtension.lift_eps _ _ _

theorem dualBase_isUnit (r : Fin m → Free n) (p : Free n) :
    IsUnit (dualBase r p (DualExtension.inclusion (Presentation.projection r p))) := by
  have he := congrArg (fun h : Hom (Presentation.Carrier r) (DualNumber (Carrier r p)) => h (Presentation.projection r p)) (dualBase_inclusion r p)
  change dualBase r p (DualExtension.inclusion (Presentation.projection r p)) = DualExtension.inclusion (base r p (Presentation.projection r p)) at he
  rw [he]
  exact (base_isUnit r p).map DualExtension.inclusion.toAlgHom

/-- Extend a smooth dual map whenever its base element is invertible. -/
def dualLift (r : Fin m → Free n) (p : Free n) (h : Hom (DualNumber (Presentation.Carrier r)) B)
    (hu : IsUnit (h (DualExtension.inclusion (Presentation.projection r p)))) : Hom (DualNumber (Carrier r p)) B :=
  DualExtension.lift (lift r p (Hom.comp h DualExtension.inclusion) hu) (h DualNumber.eps)
    (by change h.toAlgHom DualNumber.eps * h.toAlgHom DualNumber.eps = 0
        rw [← map_mul,DualNumber.eps_mul_eps,map_zero])

@[simp] theorem dualLift_inclusion (r : Fin m → Free n) (p : Free n) (h : Hom (DualNumber (Presentation.Carrier r)) B)
    (hu : IsUnit (h (DualExtension.inclusion (Presentation.projection r p)))) :
    Hom.comp (dualLift r p h hu) DualExtension.inclusion = lift r p (Hom.comp h DualExtension.inclusion) hu :=
  DualExtension.lift_inclusion _ _ _
@[simp] theorem dualLift_eps (r : Fin m → Free n) (p : Free n) (h : Hom (DualNumber (Presentation.Carrier r)) B)
    (hu : IsUnit (h (DualExtension.inclusion (Presentation.projection r p)))) :
    dualLift r p h hu DualNumber.eps = h DualNumber.eps := DualExtension.lift_eps _ _ _

theorem dualLift_base (r : Fin m → Free n) (p : Free n) (h : Hom (DualNumber (Presentation.Carrier r)) B)
    (hu : IsUnit (h (DualExtension.inclusion (Presentation.projection r p)))) :
    Hom.comp (dualLift r p h hu) (dualBase r p) = h := by
  apply DualExtension.unique
  · rw [← Hom.comp_assoc,dualBase_inclusion,Hom.comp_assoc,dualLift_inclusion]
    exact lift_base r p (Hom.comp h DualExtension.inclusion) hu
  · change dualLift r p h hu (dualBase r p DualNumber.eps) = h DualNumber.eps
    rw [dualBase_eps,dualLift_eps]

theorem dual_unique (r : Fin m → Free n) (p : Free n) (h k : Hom (DualNumber (Carrier r p)) B)
    (he : Hom.comp h (dualBase r p) = Hom.comp k (dualBase r p)) : h=k := by
  apply DualExtension.unique
  · apply unique r p
    have hi := congrArg (fun l => Hom.comp l (DualExtension.inclusion : Hom (Presentation.Carrier r) (DualNumber (Presentation.Carrier r)))) he
    rw [← Hom.comp_assoc,← Hom.comp_assoc,dualBase_inclusion,Hom.comp_assoc,Hom.comp_assoc] at hi
    exact hi
  · have hh := congrArg (fun l : Hom (DualNumber (Presentation.Carrier r)) B => l DualNumber.eps) he
    change h (dualBase r p DualNumber.eps) = k (dualBase r p DualNumber.eps) at hh
    simpa only [dualBase_eps] using hh

/-- This is the localization UP for Dual(A{s⁻¹}) over Dual(A), for every smooth target. -/
def dualHomEquiv (r : Fin m → Free n) (p : Free n) :
    Hom (DualNumber (Carrier r p)) B ≃
      {h : Hom (DualNumber (Presentation.Carrier r)) B // IsUnit (h (DualExtension.inclusion (Presentation.projection r p)))} where
  toFun h := ⟨Hom.comp h (dualBase r p),(dualBase_isUnit r p).map h.toAlgHom⟩
  invFun h := dualLift r p h.val h.property
  left_inv h := dual_unique r p _ h (dualLift_base _ _ _ _)
  right_inv h := Subtype.ext (dualLift_base r p h.val h.property)

/-- A finite presentation of Dual(A), localized at its included base element. -/
abbrev DualLocalized (r : Fin m → Free n) (p : Free n) :=
  Carrier (Presentation.relations r (Presentation.dualEquation n)) (Localization.extend (k := 1) p)

def toLocalizedDual (r : Fin m → Free n) (p : Free n) : Hom (DualLocalized r p) (DualNumber (Carrier r p)) :=
  lift _ _ (Hom.comp (dualBase r p) (Presentation.toDual r)) (by
    change IsUnit (dualBase r p (Presentation.toDual r (Presentation.dualInclusion r (Presentation.projection r p))))
    have he := congrArg (fun h : Hom (Presentation.Carrier r) (DualNumber (Presentation.Carrier r)) => h (Presentation.projection r p)) (Presentation.toDual_inclusion r)
    change Presentation.toDual r (Presentation.dualInclusion r (Presentation.projection r p)) = DualExtension.inclusion (Presentation.projection r p) at he
    rw [he]
    exact dualBase_isUnit r p)

def fromLocalizedDual (r : Fin m → Free n) (p : Free n) : Hom (DualNumber (Carrier r p)) (DualLocalized r p) :=
  dualLift r p (Hom.comp (base _ _) (Presentation.fromDual r)) (by
    change IsUnit (base _ _ (Presentation.fromDual r (DualExtension.inclusion (Presentation.projection r p))))
    have he := congrArg (fun h : Hom (Presentation.Carrier r) (Presentation.Dual r) => h (Presentation.projection r p)) (Presentation.fromDual_inclusion r)
    change Presentation.fromDual r (DualExtension.inclusion (Presentation.projection r p)) = Presentation.dualInclusion r (Presentation.projection r p) at he
    rw [he]
    exact base_isUnit _ _)

theorem toLocalizedDual_base (r : Fin m → Free n) (p : Free n) :
    Hom.comp (toLocalizedDual r p) (base _ _) = Hom.comp (dualBase r p) (Presentation.toDual r) := by
  unfold toLocalizedDual
  apply lift_base

theorem fromLocalizedDual_base (r : Fin m → Free n) (p : Free n) :
    Hom.comp (fromLocalizedDual r p) (dualBase r p) = Hom.comp (base _ _) (Presentation.fromDual r) := by
  unfold fromLocalizedDual
  apply dualLift_base

theorem localized_dual_inverse (r : Fin m → Free n) (p : Free n) :
    Hom.comp (fromLocalizedDual r p) (toLocalizedDual r p) = Hom.ident := by
  apply unique _ _
  rw [← Hom.comp_assoc,toLocalizedDual_base,Hom.comp_assoc,fromLocalizedDual_base,
    ← Hom.comp_assoc,Presentation.fromDual_toDual]
  rfl

theorem dual_localized_inverse (r : Fin m → Free n) (p : Free n) :
    Hom.comp (toLocalizedDual r p) (fromLocalizedDual r p) = Hom.ident := by
  apply dual_unique r p
  rw [← Hom.comp_assoc,fromLocalizedDual_base,Hom.comp_assoc,toLocalizedDual_base,
    ← Hom.comp_assoc,Presentation.toDual_fromDual]
  rfl

theorem fromLocalizedDual_eps (r : Fin m → Free n) (p : Free n) :
    fromLocalizedDual r p DualNumber.eps =
      base (Presentation.relations r (Presentation.dualEquation n)) (Localization.extend (k := 1) p) (Presentation.dualEps r) := by
  unfold fromLocalizedDual
  rw [dualLift_eps]
  change base _ _ (Presentation.fromDual r DualNumber.eps) = _
  rw [Presentation.fromDual_eps]

theorem toLocalizedDual_eps (r : Fin m → Free n) (p : Free n) :
    toLocalizedDual r p
      (base (Presentation.relations r (Presentation.dualEquation n)) (Localization.extend (k := 1) p) (Presentation.dualEps r)) = DualNumber.eps := by
  have he := congrArg (fun h : Hom (Presentation.Dual r) (DualNumber (Carrier r p)) => h (Presentation.dualEps r)) (toLocalizedDual_base r p)
  change toLocalizedDual r p (base _ _ (Presentation.dualEps r)) = dualBase r p (Presentation.toDual r (Presentation.dualEps r)) at he
  rw [Presentation.toDual_eps,dualBase_eps] at he
  exact he

end SquareKit.SmoothAlgebra.PresentedLocalization
