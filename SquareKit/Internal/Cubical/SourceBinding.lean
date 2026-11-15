import SquareKit.Internal.Cubical.SourceContraction
import SquareKit.Internal.Cubical.DimensionEvaluation
import SquareKit.Internal.Cubical.PathConversion
import Mathlib.Data.Fin.VecNotation

/-! Binding interface for the archived successor body. Cube representations
are compared explicitly with the normalized dependent products interpreted by
the guarded source rules. X remains a fixed external presheaf parameter. -/
namespace SquareKit.Cubical.Presheaf
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u

abbrev contextFamily (Γ X : Context.{u}) : Family Γ := Functor.Elements.π Γ ⋙ X

def normalizedCubeFunction {Γ X : Context.{u}} (p : Γ ⟶ cubes X 1) :
    Term (normalizedPi (interval Γ) (contextFamily (total (interval Γ)) X)) :=
  Term.map (normalizedPiIso (interval Γ) (contextFamily (total (interval Γ)) X)).hom
    (Term.map (cubePi Γ X) (transformationTerm p))

theorem normalizedCubeFunction_app {Γ X : Context.{u}} (p : Γ ⟶ cubes X 1) :
    normalizedApp (normalizedCubeFunction p) = transformationTerm (cubeApp p) := by
  exact (congrArg app (Term.map_iso_roundtrip
    (normalizedPiIso (interval Γ) (contextFamily (total (interval Γ)) X))
    (Term.map (cubePi Γ X) (transformationTerm p)))).trans (cubeApp_pi p)

theorem normalizedCubeFunction_lam {Γ X : Context.{u}} (b : total (interval Γ) ⟶ X) :
    normalizedCubeFunction (cubeLam b) = normalizedLam (transformationTerm b) :=
  congrArg (Term.map (normalizedPiIso (interval Γ) (contextFamily (total (interval Γ)) X)).hom)
    (cubeLam_pi b)

abbrev successorContext (X : Context.{u}) (n : ℕ) := cubes X (n+1)
abbrev pathContext (X : Context.{u}) (n : ℕ) := total (interval (successorContext X n))
abbrev bodyContext (X : Context.{u}) (n : ℕ) := total (interval (pathContext X n))

def boundI (X : Context.{u}) (n : ℕ) : Term (interval (bodyContext X n)) :=
  generic (interval (pathContext X n))

def boundJ (X : Context.{u}) (n : ℕ) : Term (interval (bodyContext X n)) :=
  (generic (interval (successorContext X n))).reindex (projection (interval (pathContext X n)))

noncomputable def boundMeet (X : Context.{u}) (n : ℕ) : Term (interval (bodyContext X n)) :=
  intervalDimension (.meet (.var (0 : Fin 2)) (.var 1)) ![boundI X n,boundJ X n]

theorem boundMeet_eq (X : Context.{u}) (n : ℕ) :
    boundMeet X n = intervalMeet (boundI X n) (boundJ X n) := by
  unfold boundMeet
  rw [intervalDimension_meet,intervalDimension_var,intervalDimension_var]
  rfl

noncomputable def meetArgumentSub (X : Context.{u}) (n : ℕ) :
    bodyContext X n ⟶ total (interval (successorContext X n)) :=
  pair (projection (interval (pathContext X n)) ≫ projection (interval (successorContext X n)))
    (boundMeet X n)

/-- The source subexpression c (i meet j), through actual Π application and
the simultaneous substitution pairing its argument. -/
noncomputable def appliedCube (X : Context.{u}) (n : ℕ) :
    Term (contextFamily (bodyContext X n) (cubes X n)) :=
  (normalizedApp (normalizedCubeFunction (cubeCurry X n))).reindex (meetArgumentSub X n)

theorem appliedCube_value (X : Context.{u}) (n : ℕ) (x : (bodyContext X n).Elements) :
    (appliedCube X n).val x = x.val.1.1.apply (Cube.meet x.val.2.down x.val.1.2.down) := by
  unfold appliedCube
  rw [normalizedCubeFunction_app]
  unfold meetArgumentSub
  rw [boundMeet_eq]
  change (x.val.1.1.restrict (𝟙 x.obj)).apply (Cube.meet x.val.2.down x.val.1.2.down) = _
  have he : x.val.1.1.restrict (𝟙 x.obj) = x.val.1.1 := by
    exact congrArg (fun f => f x.val.1.1) ((cubes X (n+1)).map_id x.obj)
  rw [he]

/-- Forget the ambient context after introducing a presheaf-valued argument. -/
def argumentProjection (Γ Y : Context.{u}) : total (contextFamily Γ Y) ⟶ Y where
  app _ := TypeCat.ofHom (fun z => z.2)
  naturality _ _ _ := rfl

/-- The two arguments of a global method become ordinary bound variables. -/
def methodArguments (Γ Y : Context.{u}) :
    total (interval (total (contextFamily Γ Y))) ⟶ total (interval Y) :=
  pair (projection (interval (total (contextFamily Γ Y))) ≫ argumentProjection Γ Y)
    (generic (interval (total (contextFamily Γ Y))))

def methodBody (Γ Y : Context.{u}) (k : total (interval Y) ⟶ Y) :
    Term (contextFamily (total (interval (total (contextFamily Γ Y)))) Y) :=
  transformationTerm (methodArguments Γ Y ≫ k)

/-- Bind the cube argument and then the interval argument of the recursion parameter. -/
def methodFunction (Γ Y : Context.{u}) (k : total (interval Y) ⟶ Y) :
    Term (normalizedPi (contextFamily Γ Y)
      (normalizedPi (interval (total (contextFamily Γ Y)))
        (contextFamily (total (interval (total (contextFamily Γ Y)))) Y))) :=
  normalizedLam (normalizedLam (methodBody Γ Y k))

/-- First application, including the literal product substitution conversion. -/
def methodFirstApplication (Γ Y : Context.{u}) (k : total (interval Y) ⟶ Y)
    (a : Term (contextFamily Γ Y)) :
    Term (normalizedPi (interval Γ) (contextFamily (total (interval Γ)) Y)) :=
  ((normalizedApp (methodFunction Γ Y k)).reindex (pair (A := contextFamily Γ Y) (𝟙 Γ) a)).convert
    (normalizedPi_reindex _ _ (pair (A := contextFamily Γ Y) (𝟙 Γ) a))

theorem methodFirstApplication_eq (Γ Y : Context.{u}) (k : total (interval Y) ⟶ Y)
    (a : Term (contextFamily Γ Y)) :
    methodFirstApplication Γ Y k a = normalizedLam
      ((methodBody Γ Y k).reindex (liftSub (interval (total (contextFamily Γ Y))) (pair (A := contextFamily Γ Y) (𝟙 Γ) a))) := by
  unfold methodFirstApplication methodFunction
  rw [normalizedApp_lam]
  exact normalizedLam_reindex _ _

/-- Apply the recursion parameter to c(i meet j), and then to j. -/
noncomputable def interpretedStepBody (X : Context.{u}) (n : ℕ) (k : ContractionMethod X n) :
    Term (contextFamily (bodyContext X n) (cubes X n)) :=
  (normalizedApp (methodFirstApplication (bodyContext X n) (cubes X n) k (appliedCube X n))).reindex
    (pair (A := interval (bodyContext X n)) (𝟙 (bodyContext X n)) (boundJ X n))

theorem interpretedStepBody_eq (X : Context.{u}) (n : ℕ) (k : ContractionMethod X n) :
    interpretedStepBody X n k = transformationTerm (sourceStepBody X n k) := by
  unfold interpretedStepBody
  rw [methodFirstApplication_eq, normalizedApp_lam]
  apply Term.ext
  intro x
  change k.app x.obj ⟨(appliedCube X n).val x, x.val.1.2⟩ = _
  rw [appliedCube_value]
  rfl

/-- The successor operation, in the source function representation, is exactly
abstraction over i of the checked two-application body. -/
theorem sourceStep_normalized (X : Context.{u}) (n : ℕ) (k : ContractionMethod X n) :
    normalizedCubeFunction (sourceStep X n k ≫ cubeCurry X n) =
      normalizedLam (interpretedStepBody X n k) := by
  rw [interpretedStepBody_eq]
  unfold sourceStep
  rw [Category.assoc, cubeUncurry_curry, Category.comp_id]
  exact normalizedCubeFunction_lam _

/-- A recursion with these source equations is determined at every natural
index. This connects the bound successor body to the selected coordinate model. -/
theorem source_characterization_unique (X : Context.{u})
    (c : (n : ℕ) → ContractionMethod X n)
    (zero : c 0 = projection (interval (cubes X 0)))
    (successor : ∀ n, c (n+1) = sourceStep X n (c n)) :
    ∀ n, c n = contractCube X n := by
  intro n
  induction n with
  | zero => exact zero.trans (sourceZero_contract X)
  | succ n ih => exact (successor n).trans ((congrArg (sourceStep X n) ih).trans
      (sourceStep_contract X n))

end SquareKit.Cubical.Presheaf
