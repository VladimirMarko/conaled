import SquareKit.SmoothOpenScalar
import SquareKit.SmoothGeometricDual
import Examples.SmoothFormalLocalization
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Experimental countable principal covers with no finite subcover.
The same infinite scope is exercised by analytic scalar gluing and a nonzero
nilpotent on the thickened line, using actual localization overlaps. -/
noncomputable section
namespace Examples.ArbitrarySmoothCovers
open CategoryTheory Opposite SquareKit SmoothAlgebra SmoothPresentationSite
open PresentedLocalization PrincipalCover
open scoped ContDiff

abbrev line := free 1
abbrev relations := noRelations 1

def defining (i : ℕ) : Free 1 :=
  ⟨fun x => expNegInvGlue (((i : ℝ)+1)^2-(x 0)^2),
    expNegInvGlue.contDiff.comp (contDiff_const.sub ((contDiff_apply ℝ _ 0).pow 2))⟩

def opens (i : ℕ) : Carrier line := Presentation.projection relations (defining i)
def point (t : ℝ) : Hom (Carrier line) ℝ := Hom.comp (evaluate (fun _ => t)) (freeValue 1)

theorem covers : OpenCover.Covers opens := by
  apply (OpenCover.covers_iff_zero_locus relations defining).mpr
  intro x _
  obtain ⟨i,hi⟩ := exists_nat_gt |x 0|
  refine ⟨i,ne_of_gt (expNegInvGlue.pos_of_pos ?_)⟩
  have hx := sq_abs (x 0)
  have hn : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith [abs_nonneg (x 0)]

theorem covering : principalSieve line opens ∈ SmoothOpenSite.topology (op line) :=
  SmoothOpenSite.principal_covering line opens covers

/-- No finite choice from the countable smooth defining functions covers ℝ. -/
theorem no_finite_subcover (S : Finset ℕ) : ¬ OpenCover.Covers (fun i : S => opens i.val) := by
  intro hc
  let t : ℝ := ((S.sup id : ℕ) : ℝ)+2
  obtain ⟨i,hi⟩ := hc (point t)
  apply hi
  change expNegInvGlue (((i.val : ℝ)+1)^2-t^2)=0
  apply expNegInvGlue.zero_of_nonpos
  have hn : i.val ≤ S.sup id := Finset.le_sup (f := id) i.property
  have hr : (i.val : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  dsimp [t]
  nlinarith

/-- A family missing the origin does not cover, even when indexed infinitely. -/
theorem missing_point : ¬ OpenCover.Covers
    (fun _ : ℕ => Presentation.projection relations (generator (0 : Fin 1))) := by
  intro hc
  obtain ⟨i,hi⟩ := hc (point 0)
  exact hi (evaluate_generator _ _)

def expSection : Carrier line := Presentation.projection relations SmoothFormalLocalization.exponential

def expMatching : Presieve.FamilyOfElements scalarData (principalSieve line opens).arrows :=
  fun _ f _ => scalarData.map f.op expSection

theorem expMatching_compatible : expMatching.Compatible :=
  Presieve.is_compatible_of_exists_amalgamation _ ⟨expSection,fun _ _ _ => rfl⟩

def gluedExp : Carrier line :=
  (SmoothOpenSite.scalar_isSheaf _ covering).amalgamate expMatching expMatching_compatible

theorem gluedExp_eq : gluedExp=expSection :=
  (SmoothOpenSite.scalar_isSheaf _ covering).isSeparatedFor _ _ _
    ((SmoothOpenSite.scalar_isSheaf _ covering).isAmalgamation expMatching_compatible) (fun _ _ _ => rfl)

theorem gluedExp_value (t : ℝ) : point t gluedExp=Real.exp t := by
  rw [gluedExp_eq]
  rfl

/-- The smooth-operation law is exercised on the countable localized tuple. -/
theorem infinite_exp_operation :
    (OpenCover.atDescentEquiv relations opens covers).symm
      (atSectionAct relations opens SmoothFormalLocalization.exponential
        (fun _ : Fin 1 => (OpenCover.atDescentEquiv relations opens covers)
          (Presentation.projection relations (generator (0 : Fin 1))))) =
      act SmoothFormalLocalization.exponential
        (fun _ : Fin 1 => Presentation.projection relations (generator (0 : Fin 1))) := by
  refine (OpenCover.at_glue_act relations opens covers SmoothFormalLocalization.exponential
    (fun _ : Fin 1 => (OpenCover.atDescentEquiv relations opens covers)
      (Presentation.projection relations (generator (0 : Fin 1))))).trans ?_
  congr 1
  funext i
  exact (OpenCover.atDescentEquiv relations opens covers).symm_apply_apply _

abbrev thickLine := dual line
abbrev thickOpens (i : ℕ) : Carrier thickLine :=
  (smoothMap (SmoothGeometricKL.inl line)) (opens i)
abbrev epsilon : Carrier thickLine := (SmoothGeometricKL.eps line).val

theorem thick_covers : OpenCover.Covers thickOpens :=
  OpenCover.map_covers (SmoothGeometricKL.inl line) opens covers

def zeroSection : Hom (Carrier thickLine) (Carrier line) :=
  SmoothGeometricKL.dualLift line line Hom.ident ⟨0,mul_zero _⟩

theorem thick_no_finite_subcover (S : Finset ℕ) :
    ¬ OpenCover.Covers (fun i : S => thickOpens i.val) := by
  intro hc
  apply no_finite_subcover S
  have hm := OpenCover.map_covers zeroSection _ hc
  have he (i : S) : zeroSection (thickOpens i.val)=opens i.val :=
    congrArg (fun h : Hom (Carrier line) (Carrier line) => h (opens i.val))
      (SmoothGeometricKL.dualLift_inl line line Hom.ident ⟨0,mul_zero _⟩)
  simpa only [he] using hm

def epsilonSections : AtSections thickLine.equations thickOpens :=
  (OpenCover.atDescentEquiv thickLine.equations thickOpens thick_covers) epsilon

def gluedEpsilon : Carrier thickLine :=
  (OpenCover.atDescentEquiv thickLine.equations thickOpens thick_covers).symm epsilonSections

theorem gluedEpsilon_eq : gluedEpsilon=epsilon :=
  (OpenCover.atDescentEquiv thickLine.equations thickOpens thick_covers).symm_apply_apply epsilon

theorem gluedEpsilon_coefficient : (dualToActual line gluedEpsilon).snd=1 := by
  rw [gluedEpsilon_eq]
  exact congrArg TrivSqZeroExt.snd (Presentation.toDual_eps line.equations)

theorem gluedEpsilon_nonzero : gluedEpsilon≠0 := by
  intro he
  have hc := gluedEpsilon_coefficient
  rw [he] at hc
  have hz : dualToActual line 0=0 := map_zero (dualToActual line).toAlgHom
  rw [hz] at hc
  have hh := congrArg (point 0).toAlgHom hc
  exact zero_ne_one (by simpa only [TrivSqZeroExt.snd_zero,map_zero,map_one] using hh)

theorem gluedEpsilon_real_zero (h : Hom (Carrier thickLine) ℝ) : h gluedEpsilon=0 := by
  rw [gluedEpsilon_eq]
  have he := congrArg h.toFun (SmoothGeometricKL.eps line).property
  change h (epsilon*epsilon)=h 0 at he
  rw [h.map_mul] at he
  have hz : h 0=0 := map_zero h.toAlgHom
  rw [hz] at he
  exact mul_self_eq_zero.mp he

end Examples.ArbitrarySmoothCovers
