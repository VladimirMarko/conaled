import Examples.GuardedJRetestValidation
import Examples.GuardedJAuthorBaseline
import Examples.GuardedJAuthorCandidate
import SquareKit.Internal.DependentJudgments.Sigma.Native

/-! Post-trial coordinator specializations consuming the byte-identical #323
author submissions. Experimental evaluation only. Support reproduces the frozen
private native fixture; no proof repairs are made to either submission. -/
namespace GuardedJRetest.AuthorNativeCases
open SquareKit.Internal SquareKit.Internal.PathTransport Typed Authoring
open SquareKit.Internal.DependentJudgments SquareKit.GuardedTheory
set_option backward.isDefEq.respectTransparency false
abbrev native := NativeType.model Nat (fun n => Fin (n + 1))
abbrev stable := Sigma.Native.stable Nat (fun n => Fin (n + 1))

namespace Baseline
open NamedCaller
abbrev rootLeft := GuardedJRetest.Baseline.workedLeft
  earlier base x.deriv generalized qAtBType qAtB
abbrev rootRight := GuardedJRetest.Baseline.workedRight
  earlier base x.deriv generalized qAtBType qAtB

theorem comparisonSound : interpretTm native rootLeft = interpretTm native rootRight :=
  GuardedJRetest.Baseline.comparisonSound
    earlier base x.deriv generalized qAtBType qAtB
    (GuardedJRetest.Baseline.dependentWeakening earlier base x.deriv generalized qAtBType qAtB)
    native

def retainedSelected := GuardedJRetest.Baseline.extensionSelected
  earlier base x.deriv generalized qAtBType qAtB
  (GuardedJRetest.Baseline.dependentWeakening earlier base x.deriv generalized qAtBType qAtB)
  native stable
end Baseline

/-- Evaluate the concrete caller's annotations without assuming any source
judgment in the candidate. The candidate hypotheses are checked below. -/
structure Inputs where
  context : native.Context
  family : native.Family context
  point : native.Section context family
  length : Nat
  tail : StructuralModel.Telescope native.toStructuralModel
    (native.toStructuralModel.pathContext family point) length
  valueFamily : native.Family tail.total
  value : native.Section tail.total valueFamily

private def inputsOf {Γ : RawCtx} {γ : CtxCode.{1}} {A x : Expr} {a : TyCode γ}
    {ξ : TmCode γ a} {n : Nat} {Ξ : RawCtx} {T : TelCode (pathCode a ξ) n}
    {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
    (_hΓ : CtxDeriv Γ γ) (_hA : TyDeriv Γ γ A a) (_hx : TmDeriv Γ γ A a x ξ)
    (_hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T)
    (_hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q)
    (_hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π) : Inputs :=
  ⟨γ native, a native, ξ native, n, T native, q native, π native⟩

private def inputs := inputsOf NamedCaller.earlier NamedCaller.base NamedCaller.x.deriv
  NamedCaller.generalized NamedCaller.qAtBType NamedCaller.qAtB

theorem tail_length : inputs.length = 3 := rfl

private theorem weaken_value {Γ : RawCtx} {γ : CtxCode.{1}} {A : Expr} {a : TyCode γ}
    (p : BasePoint Γ γ) (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (z : extendCode γ a native) :
    ((p.weaken hΓ hA).code native).down z = (p.code native).down z.1 := by
  have e := eq_of_heq (castCode_eval (baseSub_code (weakenCode γ a))
    (subTmCode p.code (weakenCode γ a)) native)
  exact congrArg (fun t => t.down z) e

private theorem variable_value {Γ : RawCtx} {γ : CtxCode.{1}}
    (hΓ : CtxDeriv Γ γ) (z : extendCode γ (baseCode γ) native) :
    ((BasePoint.variable hΓ).code native).down z = z.2 := by
  have e := eq_of_heq (castCode_eval (baseSub_code (weakenCode γ (baseCode γ)))
    (varCode γ (baseCode γ)) native)
  exact congrArg (fun t => t.down z) e

/-- The full tail is inhabited, including its dependent identity and fiber
binders, in the native model with varying finite fibers. -/
private def populatedTail : inputs.tail.total := by
  let γ : inputs.context := ⟨PUnit.unit, (3 : Nat)⟩
  let chosen := inputs.point.down γ
  refine ⟨⟨⟨⟨⟨γ, chosen⟩, ⟨⟨rfl⟩⟩⟩, chosen⟩, ⟨⟨?_⟩⟩⟩, ?_⟩
  · simp only [NamedCaller.yAtZ, NamedCaller.moving, NamedCaller.z,
      weaken_value, variable_value]
  · change Fin (_ + 1)
    exact ⟨0, Nat.zero_lt_succ _⟩

theorem tail_inhabited : Nonempty inputs.tail.total := ⟨populatedTail⟩

private def populatedRootTail :
    (StructuralModel.Telescope.pullback native.toStructuralModel inputs.tail
      (native.toStructuralModel.rootSub inputs.family inputs.point)).total :=
  (NativeType.telescopeEquiv Nat (fun n => Fin (n + 1)) inputs.tail
    (NativeType.rootEquiv Nat (fun n => Fin (n + 1)) inputs.family inputs.point)).symm populatedTail

private def populatedWeakening : native.extend
    (StructuralModel.Telescope.pullback native.toStructuralModel inputs.tail
      (native.toStructuralModel.rootSub inputs.family inputs.point)).total
    (native.subTy (native.identity inputs.valueFamily inputs.value inputs.value)
      (native.toStructuralModel.rootTail inputs.family inputs.point inputs.tail)) :=
  ⟨populatedRootTail, ⟨⟨rfl⟩⟩⟩

theorem weakening_inhabited : Nonempty (native.extend
    (StructuralModel.Telescope.pullback native.toStructuralModel inputs.tail
      (native.toStructuralModel.rootSub inputs.family inputs.point)).total
    (native.subTy (native.identity inputs.valueFamily inputs.value inputs.value)
      (native.toStructuralModel.rootTail inputs.family inputs.point inputs.tail))) :=
  ⟨populatedWeakening⟩

theorem root_tail_inhabited : Nonempty
    (StructuralModel.Telescope.pullback native.toStructuralModel inputs.tail
      (native.toStructuralModel.rootSub inputs.family inputs.point)).total :=
  ⟨populatedRootTail⟩

namespace Candidate
open Contextual

private abbrev g : Contextual.Expression (Fin 6) := .var 0
private abbrev a : Contextual.Expression (Fin 6) := .var 1
private abbrev x : Contextual.Expression (Fin 6) := .var 2
private abbrev t : Contextual.Expression (Fin 6) := .var 3
private abbrev q : Contextual.Expression (Fin 6) := .var 4
private abbrev p : Contextual.Expression (Fin 6) := .var 5
private def premises : Fin 3 → Contextual.Judgment (Fin 6) :=
  ![term g a x, telescope inputs.length (path a x) t, term (total t) q p]
private abbrev assumptions := List.ofFn premises
private def point : Tm (Ω := assumptions) g a x :=
  .hypothesis (List.mem_ofFn.mpr ⟨0, rfl⟩)
private def tail : Tel (Ω := assumptions) inputs.length (path a x) t :=
  .hypothesis (List.mem_ofFn.mpr ⟨1, rfl⟩)
private def value : Tm (Ω := assumptions) (total t) q p :=
  .hypothesis (List.mem_ofFn.mpr ⟨2, rfl⟩)

private def environment : Fin 6 → Value native.toStructuralModel :=
  ![.context inputs.context, .family inputs.context inputs.family,
    .term inputs.context inputs.family inputs.point,
    .telescope _ inputs.length inputs.tail,
    .family inputs.tail.total inputs.valueFamily,
    .term inputs.tail.total inputs.valueFamily inputs.value]

/-- All hypotheses have actual native values, including the three dependent
tail binders. None is a requested equality or a selected-output assumption. -/
theorem assumptions_valid : ∀ j ∈ assumptions, j.eval (Contextual.algebra native) environment := by
  intro j hj
  rcases List.mem_ofFn.mp hj with ⟨i, rfl⟩
  fin_cases i
  · exact ⟨inputs.context, inputs.family, inputs.point, rfl, rfl, rfl⟩
  · refine ⟨_, inputs.tail, ?_, rfl⟩
    simp [SquareKit.GuardedTheory.Term.eval, Contextual.algebra, Contextual.operation, environment]
  · refine ⟨_, inputs.valueFamily, inputs.value, ?_, rfl, rfl⟩
    simp [SquareKit.GuardedTheory.Term.eval, Contextual.algebra, Contextual.operation, environment]


private abbrev cmd := GuardedJRetest.Candidate.outer point tail value
private abbrev arrow := GuardedJRetest.Candidate.dependentWeakening point tail value

def interpretedLeft := Contextual.interpret
  (GuardedJRetest.Candidate.workedLeft point tail value)
  native environment assumptions_valid

def interpretedRight := Contextual.interpret
  (GuardedJRetest.Candidate.workedRight point tail value)
  native environment assumptions_valid

def comparisonSound := GuardedJRetest.Candidate.comparisonSound
  point tail value arrow native environment assumptions_valid

def retainedSelected := GuardedJRetest.Candidate.extensionSelected
  point tail value arrow native stable environment assumptions_valid

theorem exactRecipe : cmd.expression =
    j a x t (identity (identity q p p)
      (GuardedJRetest.Candidate.calibration point tail value).expression
      (GuardedJRetest.Candidate.calibration point tail value).expression)
      (reflexivity (subTy (identity q p p) (rootTail a x t))
        (subTm (GuardedJRetest.Candidate.calibration point tail value).expression (rootTail a x t))) :=
  GuardedJRetest.Candidate.selectedRecipe point tail value

end Candidate
end GuardedJRetest.AuthorNativeCases

namespace GuardedJRetest.AuthorReferenceComparison
namespace Baseline

open SquareKit.Internal SquareKit.Internal.PathTransport Typed Authoring
universe u
variable {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
  {ξ : TmCode γ a} {n : Nat} {Ξ : RawCtx} {T : TelCode (pathCode a ξ) n}
  {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
variable (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
  (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T)
  (hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q)
  (hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π)


theorem selectedCommand : GuardedJRetest.Baseline.outer hΓ hA hx hT hQ hp =
    GuardedJRetest.BaselineReference.outer hΓ hA hx hT hQ hp := rfl
end Baseline
namespace Candidate

open SquareKit.Internal.DependentJudgments.Contextual SquareKit.GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A x T Q p Δ σ : Expression V} {n : Nat}
variable (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (path A x) T)
  (hp : Tm (Ω := Ω) (total T) Q p)


theorem selectedCommand : GuardedJRetest.Candidate.outer hx hT hp =
    GuardedJRetest.CandidateReference.outer hx hT hp := rfl
end Candidate
end GuardedJRetest.AuthorReferenceComparison
