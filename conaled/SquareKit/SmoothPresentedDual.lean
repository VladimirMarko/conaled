import SquareKit.SmoothPresentation
import SquareKit.SmoothDualExtension

/-! Experimental finite presentation of the existing smooth dual extension.
This compares actual smooth maps, retaining the nilsquare generator. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.Presentation
attribute [local instance] DualExtension.smoothStructure
variable {n m : ℕ}

-- Preserve the inherited dual structures while avoiding repeated quotient-alias search.
instance (r : Fin m → Free n) : CommRing (DualNumber (Carrier r)) := TrivSqZeroExt.commRing
instance (r : Fin m → Free n) : Monoid (DualNumber (Carrier r)) :=
  (TrivSqZeroExt.commRing : CommRing (DualNumber (Carrier r))).toCommMonoid.toMonoid
instance (r : Fin m → Free n) : Mul (DualNumber (Carrier r)) :=
  (TrivSqZeroExt.commRing : CommRing (DualNumber (Carrier r))).toCommMonoid.toMonoid.toMulOneClass.toMulOne.toMul
instance (r : Fin m → Free n) : Algebra ℝ (DualNumber (Carrier r)) := TrivSqZeroExt.algebra' ℝ (Carrier r) (Carrier r)
instance (r : Fin m → Free n) : Structure (DualNumber (Carrier r)) := DualExtension.smoothStructure

def dualEquation (n : ℕ) : Free (n+1) := (generator (Fin.last n))^2
abbrev Dual (r : Fin m → Free n) := Adjoin r (dualEquation n)
abbrev dualInclusion (r : Fin m → Free n) : Hom (Carrier r) (Dual r) := inclusion r (dualEquation n)
abbrev dualEps (r : Fin m → Free n) : Dual r := coordinate r (dualEquation n)

theorem dualEps_square (r : Fin m → Free n) : dualEps r * dualEps r = 0 := by
  have h := adjoin_relation r (dualEquation n)
  change (projection (relations r (dualEquation n))).toAlgHom ((generator (Fin.last n))^2) = 0 at h
  rw [map_pow,pow_two] at h
  exact h

def toDual (r : Fin m → Free n) : Hom (Dual r) (DualNumber (Carrier r)) :=
  lift r (dualEquation n) DualExtension.inclusion DualNumber.eps (by
    unfold dualEquation
    rw [pow_two,(evaluate (coordinates r DualExtension.inclusion DualNumber.eps)).map_mul,evaluate_generator]
    simp only [coordinates,Fin.snoc_last]
    exact DualNumber.eps_mul_eps)

def fromDual (r : Fin m → Free n) : Hom (DualNumber (Carrier r)) (Dual r) :=
  DualExtension.lift (dualInclusion r) (dualEps r) (dualEps_square r)

@[simp] theorem toDual_inclusion (r : Fin m → Free n) :
    Hom.comp (toDual r) (dualInclusion r) = DualExtension.inclusion := by
  unfold toDual
  apply lift_inclusion
@[simp] theorem toDual_eps (r : Fin m → Free n) : toDual r (dualEps r) = DualNumber.eps := by
  unfold toDual
  apply lift_coordinate
@[simp] theorem fromDual_inclusion (r : Fin m → Free n) :
    Hom.comp (fromDual r) DualExtension.inclusion = dualInclusion r := DualExtension.lift_inclusion _ _ _
@[simp] theorem fromDual_eps (r : Fin m → Free n) : fromDual r DualNumber.eps = dualEps r := DualExtension.lift_eps _ _ _

theorem toDual_fromDual (r : Fin m → Free n) : Hom.comp (toDual r) (fromDual r) = Hom.ident := by
  apply DualExtension.unique
  · rw [← Hom.comp_assoc,fromDual_inclusion,toDual_inclusion]
    rfl
  · change toDual r (fromDual r DualNumber.eps) = DualNumber.eps
    rw [fromDual_eps,toDual_eps]

theorem fromDual_toDual (r : Fin m → Free n) : Hom.comp (fromDual r) (toDual r) = Hom.ident := by
  apply unique r (dualEquation n)
  · rw [← Hom.comp_assoc,toDual_inclusion,fromDual_inclusion]
    rfl
  · change fromDual r (toDual r (dualEps r)) = dualEps r
    rw [toDual_eps,fromDual_eps]

end SquareKit.SmoothAlgebra.Presentation
