import SquareKit.Internal.DependentFunctionSheafComparison
import Examples.DependentSource
import Examples.SplitDependentFunctionEdges

/-! Experimental dependent source beta with a function parameter, a bound result
index, and nonidentity negation substitution. The same derivation is interpreted
in a finite dependent family and an E-based natural-function family. -/
noncomputable section
namespace Examples.DependentFunctionSource
open CategoryTheory Limits Opposite SquareKit
open Internal.DependentFunctions Internal.DependentFunctions.SheafSem
open Internal.DependentStructural (Base)
open Internal.DependentStructural.SheafSem (evalBase)
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange Examples.SheafFamilies

abbrev Γ : Ctx 1 := .function (.base .nil) (.var 0)
abbrev parameter : Func Γ := .var .top
abbrev body : Dep (.base Γ) := .app (.var (.base .top)) (.neg (.var 0))
abbrev left : Dep Γ := .app (.lam body) (.neg (.var 0))
abbrev right : Dep Γ := .app parameter (.neg (.neg (.var 0)))

def negSub : Sub Γ Γ where
  base i := .neg (.var i)
  dep | .function (.base v) => nomatch v
  func
    | .top => .var .top
    | .function (.base v) => nomatch v

theorem negSub_typed : negSub.Typed where
  dep | .function (.base v) => nomatch v
  func
    | .top => rfl
    | .function (.base v) => nomatch v

theorem negSub_not_id : negSub ≠ Sub.id Γ := by
  intro h
  have he := congrArg (fun σ : Sub Γ Γ => σ.base 0) h
  cases he

theorem bound_index_preserved : negSub.lift.base 0 = .var 0 := rfl
theorem free_index_shifted : negSub.lift.base 1 = .neg (.var 1) := rfl

def parameterTerm : Tm Γ (.pi (.var 0)) := ⟨parameter, rfl⟩

/-- Repeated nonidentity substitution checks the typed conversion law on a
function parameter, in addition to the beta equation below. -/
abbrev twice_substituted_parameter := Sub.term_composition negSub negSub negSub_typed negSub_typed parameterTerm

/-- This is the generic derived theorem, with a function variable in the body. -/
theorem source_equation : DepEq left right := substituted_beta negSub negSub_typed body (.var 0)

/-- The result family is indexed by the actual (twice negated) argument. -/
theorem dependent_result : left.type = .neg (.neg (.var 0)) := rfl

theorem result_not_zero : left.type ≠ .zero := by intro h; cases h

theorem parameter_eta : FuncEq (.lam (.app ((Ren.weaken Γ).funcMap parameter) (.var 0))) parameter := .eta _

/-- A natural section of the primitive family supplies a legal interpretation
of the free function parameter. No function is inserted into the source tree. -/
def parameterEnv {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (M : Model J) (z : SplitSheaf.Tm M.A) : Env M Γ where
  carrier := M.B
  base _ := 𝟙 M.B
  dep | .function (.base v) => nomatch v
  func
    | .top => SplitSheafPi.lam (baseType M M.B) (SplitSheaf.tmSub z (SplitSheaf.constantValue M.B))
    | .function (.base v) => nomatch v

theorem parameter_application {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (M : Model J) (z : SplitSheaf.Tm M.A) (a : Base 1) :
    evalDep M (parameterEnv M z) (.app parameter a) =
      SplitSheaf.tmSub z (evalBase M (parameterEnv M z).base a) := by
  dsimp only [evalDep, evalFunc, parameterEnv, parameter, applyTerm]
  erw [SplitSheafPi.app_beta]
  rfl

theorem parameter_value {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (M : Model J) (z : SplitSheaf.Tm M.A) (a : Base 1) :
    depValue M (parameterEnv M z) (.app parameter a) =
      evalBase M (parameterEnv M z).base a ≫ SplitSheaf.pair M.A (𝟙 M.B) z := by
  unfold depValue
  erw [parameter_application M z a]
  rfl

theorem left_value {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (M : Model J) (z : SplitSheaf.Tm M.A) :
    depValue M (parameterEnv M z) left = (M.neg ≫ M.neg) ≫ SplitSheaf.pair M.A (𝟙 M.B) z :=
  (value_sound M (parameterEnv M z) source_equation).trans
    (parameter_value M z (.neg (.neg (.var 0))))

/-- The nonidentity source assignment has the actual negation map as its
realization, including the function parameter under split Pi substitution. -/
def negRealization {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (M : Model J) (z : SplitSheaf.Tm M.A) :
    SubRealization M (parameterEnv M z) (parameterEnv M z) negSub where
  map := M.neg
  typed := negSub_typed
  base _ := rfl
  dep | .function (.base v) => nomatch v
  func
    | .top => by
      have h := SplitSheafPi.lam_substitution (baseType M M.B)
        (SplitSheaf.tmSub z (SplitSheaf.constantValue M.B)) M.neg
      exact (heq_of_eq h.symm).trans (transport_heq _ _)
    | .function (.base v) => nomatch v

/-- A finite family with Bool over false and Unit over true, constructed using
the earlier false-point dependent product. It has a chosen natural section. -/
abbrev finiteSection (b : Bool) := SplitSheafPi.lam SplitDependentFunctions.argument (SplitDependentFunctions.body b)

def finiteModel : Model topology where
  B := D
  A := SplitDependentFunctions.functions
  zero := DependentSource.unitIso.hom ≫ falsePoint
  neg := SheafFunctions.negation
  point := SplitSheaf.pair SplitDependentFunctions.functions (DependentSource.unitIso.hom ≫ falsePoint)
    (SplitSheaf.tmSub (finiteSection false) (DependentSource.unitIso.hom ≫ falsePoint))
  point_type := rfl

abbrev finiteEnv (b : Bool) := parameterEnv finiteModel (finiteSection b)

theorem finite_source (b : Bool) : HEq (evalDep finiteModel (finiteEnv b) left)
    (evalDep finiteModel (finiteEnv b) right) := dep_sound finiteModel source_equation _

theorem finite_ordinary (b : Bool) :
    HEq (ordinaryApplication finiteModel (finiteEnv b) (.lam body) (.neg (.var 0)))
      (evalDep finiteModel (finiteEnv b) right) :=
  derived_ordinary finiteModel (finiteEnv b) negSub negSub_typed body (.var 0)

theorem negation_value (U : Diamondᵒᵖ) (b : Bool) (x : D.obj.obj U) :
    (evalBase finiteModel (finiteEnv b).base (.neg (.var 0))).hom.app U x = !x := rfl

/-- Beta is evaluated on an actual finite input. At base false the source
argument is true, its negation is false, and the result is the Boolean fiber. -/
theorem finite_beta_value (b : Bool) :
    (evalDep finiteModel (finiteEnv b) left).val (D.obj.elementsMk (op X) false) =
      (finiteSection b).val (D.obj.elementsMk (op X) false) := by
  have h : evalDep finiteModel (finiteEnv b) left = evalDep finiteModel (finiteEnv b) right :=
    eq_of_heq (finite_source b)
  rw [h]
  exact congrArg (fun t => t.val (D.obj.elementsMk (op X) false))
    (parameter_application finiteModel (finiteSection b) (.neg (.neg (.var 0))))

/-- The Boolean observation is the existing ordinary false-point calculation,
now reached through the source beta proof and its constructed interpretation. -/
theorem finite_beta_boolean (b : Bool)
    (a : SplitDependentFunctions.argument.family.obj (D.obj.elementsMk (op X) false)) :
    (pullback.fst base (SplitSheaf.displayIso falsePoint).hom).hom.app (op X)
      (SplitFunctionDiagram.evaluate SplitDependentFunctions.argument.family SplitDependentFunctions.result.family
        (D.obj.elementsMk (op X) false)
        ((evalDep finiteModel (finiteEnv b) left).val (D.obj.elementsMk (op X) false)) a).val = b := by
  rw [finite_beta_value]
  exact SplitDependentFunctions.lambda_false X b a

abbrev negation_mate (b : Bool) :=
  source_substitution_mate finiteModel (negRealization finiteModel (finiteSection b)).base body.type

/-- Both fibers of the result family have checked ordinary interpretations. -/
abbrev result_false := SplitDependentFunctions.falseFiber
abbrev result_true := SplitDependentFunctions.trueFiber

/-- The extended source still cannot manufacture an inhabitant of the original
false-point family at true, even by adding lambdas and applications. -/
theorem no_closed_true : ¬ Nonempty (Tm Ctx.nil (.family (.neg .zero))) := by
  rintro ⟨t⟩
  let E := nilEnv DependentSource.falseModel
  let k := SplitSheaf.pair DependentSource.falseModel.A
    (evalBase DependentSource.falseModel E.base (.neg .zero))
    (term DependentSource.falseModel E t)
  have h : k ≫ (SplitSheaf.displayIso falsePoint).hom ≫ falsePoint =
      evalBase DependentSource.falseModel E.base (.neg .zero) := by
    erw [SplitSheaf.displayIso_projection]
    rfl
  have hv := congrArg (fun f => f.hom.app (op X) (DependentSource.unitIso.inv.hom.app (op X) ())) h
  change false = true at hv
  exact Bool.noConfusion hv

theorem no_closed_identity_family : ¬ Nonempty (Tm Ctx.nil (.pi (.var 0))) := by
  rintro ⟨f⟩
  apply no_closed_true
  refine ⟨⟨.app f.val (.neg .zero), ?_⟩⟩
  change instantiate f.val.type (.neg .zero) = .neg .zero
  rw [f.property]
  rfl

end Examples.DependentFunctionSource
