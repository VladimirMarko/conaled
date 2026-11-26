import SquareKit.SmoothManifoldCoordinatePullbacks
import SquareKit.SmoothDualCover
import SquareKit.SmoothRealPointCovers

/-! Coordinate fibers retain free parameters and nonzero infinitesimals.
The examples use the public lifts and ordinary restriction comparisons. -/
noncomputable section
namespace Examples.SmoothCoordinatePullbacks
open CategoryTheory CategoryTheory.Limits Opposite SquareKit
open SquareKit.SmoothAlgebra SquareKit.SmoothPresentationSite SquareKit.SmoothGeometricKL
open SquareKit.SmoothOpenSite
local notation "P" => SmoothOpenSite.scalarPower

/-- The free smooth-algebra statement retains two arbitrary, independent inputs. -/
theorem two_freeAlgebra {A : Type*} [CommRing A] [Algebra ℝ A] [Structure A] (a b : A) :
    ∃! w : Hom (freeAlgebra 2) A,
      w.comp (SmoothAlgebra.Coordinates.zeroSection 2 1) =
        evaluate (Fin.addCases ![a,b] (fun _ : Fin 1 => 0)) ∧
      w.comp (SmoothAlgebra.Coordinates.constants 2) = evaluate Fin.elim0 := by
  apply SmoothAlgebra.Coordinates.zeroFiber_universal
  apply hom_ext_generators
  intro i
  change evaluate (Fin.addCases ![a,b] (fun _ : Fin 1 => 0))
    (evaluate (fun j => generator (Fin.natAdd 2 j)) (generator i)) =
      evaluate (Fin.elim0 : Fin 0 → A) (evaluate (fun _ : Fin 1 => (0 : freeAlgebra 0)) (generator i))
  rw [evaluate_generator, evaluate_generator, evaluate_generator, Fin.addCases_right]
  exact (evaluate (Fin.elim0 : Fin 0 → A)).toAlgHom.map_zero.symm

/-- Two independent coordinates survive the last-coordinate zero equation. -/
theorem two_free_coordinates {F : Sheaf SmoothOpenSite.topology Type}
    (a b : F ⟶ SmoothOpenSite.scalar) :
    SmoothOpenSite.Coordinates.fiberLift (SmoothOpenSite.Coordinates.join (SmoothOpenSite.tuple ![a,b])
      (SmoothOpenSite.tuple ![a,b] ≫ SmoothOpenSite.Coordinates.toPoint 2 ≫ SmoothOpenSite.Coordinates.zero 1)) =
      SmoothOpenSite.tuple ![a,b] := SmoothOpenSite.Coordinates.join_first _ _

abbrev stage := dual (free 0)
abbrev d : Carrier stage := (eps (free 0)).val

theorem d_square : d*d = 0 := (eps (free 0)).property

theorem d_nonzero : d ≠ 0 := by
  intro hz
  have hd := congrArg (fun z => (dualToActual (free 0) z).snd) hz
  change (Presentation.toDual _ (Presentation.dualEps _)).snd = _ at hd
  rw [Presentation.toDual_eps] at hd
  have hz₀ : dualToActual (free 0) 0 = 0 := (dualToActual (free 0)).toAlgHom.map_zero
  rw [hz₀] at hd
  have hr := congrArg realEvaluation hd
  change realEvaluation 1 = realEvaluation 0 at hr
  have h₁ : realEvaluation 1 = 1 := realEvaluation.toAlgHom.map_one
  have h₀ : realEvaluation 0 = 0 := realEvaluation.toAlgHom.map_zero
  rw [h₁, h₀] at hr
  exact one_ne_zero hr

/-- This input is a nonzero infinitesimal point of the actual zero fiber. -/
theorem nilpotent_input :
    (SmoothOpenSite.Coordinates.insertZero 1 1).hom.app (atStage stage) (fun _ => d) =
      Fin.addCases (fun _ => d) (fun _ => 0) := SmoothOpenSite.Coordinates.insertZero_apply _ _ _ _

theorem nilpotent_reconstruction :
    (SmoothOpenSite.Coordinates.fiberLift (SmoothOpenSite.Coordinates.insertZero 1 1)).hom.app (atStage stage) (fun _ => d) 0 = d := by
  have h := SmoothOpenSite.Coordinates.fiberLift_unique (SmoothOpenSite.Coordinates.insertZero 1 1) (𝟙 (P 1)) (Category.id_comp _)
  exact (congrArg (fun f : P 1 ⟶ P 1 => f.hom.app (atStage stage) (fun _ => d) 0) h).symm

theorem reconstructed_nonzero :
    (SmoothOpenSite.Coordinates.fiberLift (SmoothOpenSite.Coordinates.insertZero 1 1)).hom.app (atStage stage) (fun _ => d) 0 ≠ 0 := by
  rw [nilpotent_reconstruction]
  exact d_nonzero

def kill : stage ⟶ stage := dualZero (free 0) ≫ inl (free 0)

theorem kill_d : smoothMap kill d = 0 := by
  change smoothMap (inl (free 0)) (smoothMap (dualZero (free 0)) (eps (free 0)).val) = 0
  rw [dualZero, dualLift_eps]
  exact (smoothMap (inl (free 0))).toAlgHom.map_zero

theorem kill_nonidentity : kill ≠ 𝟙 stage := by
  intro h
  have hz := kill_d
  rw [h] at hz
  exact d_nonzero hz

def doubleInfinitesimal : stage ⟶ stage :=
  dualLift (free 0) stage (inl (free 0)) ⟨d+d, by
    simp only [add_mul, mul_add, d_square, zero_add]⟩

theorem doubleInfinitesimal_d : smoothMap doubleInfinitesimal d = d+d :=
  dualLift_eps _ _ _ _

theorem doubleInfinitesimal_nonidentity : doubleInfinitesimal ≠ 𝟙 stage := by
  intro h
  have hd := doubleInfinitesimal_d
  rw [h] at hd
  change d = d+d at hd
  exact d_nonzero (add_left_cancel (hd.symm.trans (add_zero d).symm))

theorem nilpotent_restriction :
    (SmoothOpenSite.Coordinates.fiberLift (SmoothOpenSite.Coordinates.insertZero 1 1)).hom.app (atStage stage)
      ((P 1).obj.map (stageMap kill) (fun _ => d)) 0 = 0 := by
  have h := congrFun (SmoothOpenSite.Coordinates.fiberLift_stage (SmoothOpenSite.Coordinates.insertZero 1 1) kill (fun _ => d)) 0
  rw [nilpotent_reconstruction, kill_d] at h
  exact h

theorem nilpotent_composite_restriction :
    (SmoothOpenSite.Coordinates.fiberLift (SmoothOpenSite.Coordinates.insertZero 1 1)).hom.app (atStage stage)
      ((P 1).obj.map (stageMap (doubleInfinitesimal ≫ kill)) (fun _ => d)) 0 = 0 := by
  have h := congrFun (SmoothOpenSite.Coordinates.fiberLift_stage_comp
    (SmoothOpenSite.Coordinates.insertZero 1 1) doubleInfinitesimal kill (fun _ => d)) 0
  rw [nilpotent_reconstruction, doubleInfinitesimal_d, (smoothMap kill).map_add, kill_d, zero_add] at h
  exact h

open EuclideanOpen Localization

/-- A proper principal open that contains the nilpotent point (d,0). -/
def support : freeAlgebra 2 := 1 + generator 0

def fiberFull : Hom (Principal (1 : freeAlgebra 1)) (Carrier stage) :=
  (fullHomEquiv 1 stage).symm
    ((SmoothOpenSite.Coordinates.fiberLift (SmoothOpenSite.Coordinates.insertZero 1 1)).hom.app
      (atStage stage) (fun _ => d))

theorem fiberFull_coordinate : fiberFull (principalBase 1 (generator 0)) = d := by
  exact (congrFun ((fullHomEquiv 1 stage).apply_symm_apply _) 0).trans nilpotent_reconstruction

def ambientFull : Hom (Principal (1 : freeAlgebra 2)) (Carrier stage) :=
  fiberFull.comp (Localization.pullback (EuclideanOpen.Coordinates.insertZero 1 1))

theorem support_value : ambientFull (principalBase 1 support) = 1+d := by
  rw [support, (principalBase (1 : freeAlgebra 2)).map_add, ambientFull.map_add]
  have h1 : ambientFull (principalBase 1 1) = 1 := by
    exact (congrArg ambientFull (principalBase (1 : freeAlgebra 2)).toAlgHom.map_one).trans
      ambientFull.toAlgHom.map_one
  rw [h1]
  congr 1
  change fiberFull (Localization.pullback (EuclideanOpen.Coordinates.coordinateMap _)
    (principalBase 1 (generator 0))) = d
  rw [EuclideanOpen.Coordinates.coordinateMap_base]
  exact fiberFull_coordinate

theorem support_unit : IsUnit (ambientFull (principalBase 1 support)) := by
  rw [support_value]
  exact (show IsNilpotent d from ⟨2, (pow_two d).trans d_square⟩).isUnit_one_add

def ambientRestricted : Hom (Principal (1 * support)) (Carrier stage) :=
  subLift 1 support ambientFull support_unit

theorem restricted_compatibility :
    fiberFull.comp (Localization.pullback (EuclideanOpen.Coordinates.insertZero 1 1)) =
      ambientRestricted.comp (Localization.pullback (subInclusion (full 2) support)) := by
  rw [nested_pullback]
  exact (subLift_base 1 support ambientFull support_unit).symm

/-- The existing inverse-image universal property lifts the reconstructed
nilpotent coordinate through the actual ordinary support restriction. -/
def restrictedPoint : Hom (Principal (1 *
    inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support)) (Carrier stage) :=
  (inverse_universal (EuclideanOpen.Coordinates.insertZero 1 1) support stage
    fiberFull ambientRestricted restricted_compatibility).choose

theorem restrictedPoint_first :
    restrictedPoint.comp (Localization.pullback (subInclusion (full 1)
      (inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support))) = fiberFull :=
  (inverse_universal (EuclideanOpen.Coordinates.insertZero 1 1) support stage
    fiberFull ambientRestricted restricted_compatibility).choose_spec.1.1

theorem restrictedPoint_second :
    restrictedPoint.comp (Localization.pullback
      (inverseRestriction (EuclideanOpen.Coordinates.insertZero 1 1) support)) = ambientRestricted :=
  (inverse_universal (EuclideanOpen.Coordinates.insertZero 1 1) support stage
    fiberFull ambientRestricted restricted_compatibility).choose_spec.1.2

theorem restrictedPoint_coordinate :
    restrictedPoint (principalBase (1 * inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support)
      (generator 0)) = d := by
  have h := congrArg (fun f : Hom (Principal (1 : freeAlgebra 1)) (Carrier stage) =>
    f (principalBase 1 (generator 0))) restrictedPoint_first
  rw [nested_pullback] at h
  have hb := congrArg (fun f : Hom (freeAlgebra 1) (Principal
      (1 * inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support)) => f (generator 0))
    (nestedMap_base 1 (inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support))
  exact (congrArg restrictedPoint hb).symm.trans (h.trans fiberFull_coordinate)

theorem restrictedPoint_nonzero :
    restrictedPoint (principalBase (1 * inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support)
      (generator 0)) ≠ 0 := by
  rw [restrictedPoint_coordinate]
  exact d_nonzero

/-- A different ambient principal open, with value 1-d at this stage. -/
def otherSupport : freeAlgebra 2 := 1 - generator 0

theorem otherSupport_value : ambientFull (principalBase 1 otherSupport) = 1-d := by
  change (ambientFull.comp (principalBase 1)).toAlgHom (1 - generator 0) = _
  rw [map_sub, map_one]
  congr 1
  change ambientFull (principalBase 1 (generator 0)) = d
  change fiberFull (Localization.pullback (EuclideanOpen.Coordinates.coordinateMap _)
    (principalBase 1 (generator 0))) = d
  rw [EuclideanOpen.Coordinates.coordinateMap_base]
  exact fiberFull_coordinate

theorem otherSupport_unit : IsUnit (ambientFull (principalBase 1 otherSupport)) := by
  rw [otherSupport_value]
  exact (show IsNilpotent d from ⟨2, (pow_two d).trans d_square⟩).isUnit_one_sub

def ambientOther : Hom (Principal (1 * otherSupport)) (Carrier stage) :=
  subLift 1 otherSupport ambientFull otherSupport_unit

theorem overlap_compatibility :
    ambientRestricted.comp (Localization.pullback (subInclusion (full 2) support)) =
      ambientOther.comp (Localization.pullback (subInclusion (full 2) otherSupport)) := by
  rw [nested_pullback, nested_pullback]
  exact (subLift_base 1 support ambientFull support_unit).trans
    (subLift_base 1 otherSupport ambientFull otherSupport_unit).symm

def ambientOverlap : Hom (Principal ((1 * support) * otherSupport)) (Carrier stage) :=
  (overlap_universal (full 2) support otherSupport ambientRestricted ambientOther
    overlap_compatibility).choose

theorem ambientOverlap_left :
    ambientOverlap.comp (Localization.pullback (overlapLeft (full 2) support otherSupport)) =
      ambientRestricted :=
  (overlap_universal (full 2) support otherSupport ambientRestricted ambientOther
    overlap_compatibility).choose_spec.1.1

theorem second_compatibility :
    restrictedPoint.comp (Localization.pullback
      (inverseRestriction (EuclideanOpen.Coordinates.insertZero 1 1) support)) =
    ambientOverlap.comp (Localization.pullback (subInclusion (subdomain (full 2) support) otherSupport)) :=
  restrictedPoint_second.trans ambientOverlap_left.symm

abbrev restrictedFiber := subdomain (full 1)
  (inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support)

abbrev secondDefining := inverseDefining
  (inverseRestriction (EuclideanOpen.Coordinates.insertZero 1 1) support) otherSupport

def twiceRestrictedPoint : Hom (Principal (restrictedFiber.defining * secondDefining)) (Carrier stage) :=
  (inverse_universal (inverseRestriction (EuclideanOpen.Coordinates.insertZero 1 1) support)
    otherSupport stage restrictedPoint ambientOverlap second_compatibility).choose

/-- Composing the two actual inclusions preserves the same nonzero free coordinate. -/
theorem twiceRestrictedPoint_coordinate :
    twiceRestrictedPoint (Localization.pullback (subInclusion restrictedFiber secondDefining)
      (principalBase restrictedFiber.defining (generator 0))) = d := by
  have h := (inverse_universal (inverseRestriction (EuclideanOpen.Coordinates.insertZero 1 1) support)
    otherSupport stage restrictedPoint ambientOverlap second_compatibility).choose_spec.1.1
  exact (congrArg (fun f : Hom (Principal restrictedFiber.defining) (Carrier stage) =>
    f (principalBase restrictedFiber.defining (generator 0))) h).trans restrictedPoint_coordinate

/-- The same twice-restricted ordinary maps give the all-sheaf universal square. -/
example : IsPullback
    (embedding.map (inverseRestriction
      (inverseRestriction (EuclideanOpen.Coordinates.insertZero 1 1) support) otherSupport))
    (embedding.map (subInclusion restrictedFiber secondDefining ≫
      (subInclusion (full 1) (inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) support) ≫
        EuclideanOpen.Coordinates.toPoint 1)))
    (embedding.map (subInclusion (subdomain (full 2) support) otherSupport ≫
      (subInclusion (full 2) support ≫ EuclideanOpen.Coordinates.last 1 1)))
    (embedding.map (EuclideanOpen.Coordinates.zero 1)) :=
  EuclideanOpen.Coordinates.twice_restricted_zeroFiber_isPullback 1 1 support otherSupport

/-- The empty principal ambient open has an initial sheaf realization. -/
example : IsInitial (embedding.obj (subdomain (full 2) 0)) := zeroSubdomainIsInitial _

example : IsInitial (embedding.obj (subdomain (full 1)
    (inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) 0))) :=
  inverseEmptyIsInitial _ _ (isEmpty_points_subdomain_zero (full 2))

/-- The coordinate square still exists over the empty ambient open. -/
example : IsPullback
    (embedding.map (inverseRestriction (EuclideanOpen.Coordinates.insertZero 1 1) 0))
    (embedding.map (subInclusion (full 1)
      (inverseDefining (EuclideanOpen.Coordinates.insertZero 1 1) 0) ≫ EuclideanOpen.Coordinates.toPoint 1))
    (embedding.map (subInclusion (full 2) 0 ≫ EuclideanOpen.Coordinates.last 1 1))
    (embedding.map (EuclideanOpen.Coordinates.zero 1)) :=
  EuclideanOpen.Coordinates.restricted_zeroFiber_isPullback 1 1 0

/-- No free coordinates and no constrained coordinates are both supported. -/
example (k : ℕ) : IsPullback (SmoothOpenSite.Coordinates.insertZero 0 k)
    (SmoothOpenSite.Coordinates.toPoint 0) (SmoothOpenSite.Coordinates.last 0 k)
    (SmoothOpenSite.Coordinates.zero k) := SmoothOpenSite.Coordinates.zeroFiber_isPullback 0 k

example (n : ℕ) : IsPullback (SmoothOpenSite.Coordinates.insertZero n 0)
    (SmoothOpenSite.Coordinates.toPoint n) (SmoothOpenSite.Coordinates.last n 0)
    (SmoothOpenSite.Coordinates.zero 0) := SmoothOpenSite.Coordinates.zeroFiber_isPullback n 0

end Examples.SmoothCoordinatePullbacks
