import SquareKit.Internal.DependentJudgments.Sigma.ReindexAuthoring
import SquareKit.Internal.DependentJudgments.Sigma.SourceMaps
import SquareKit.Internal.DependentJudgments.Sigma.Native

/-! Source clients inherit fresh dependent constructor comparison from admission,
including nonidentity substitutions. No instance of constructor coherence appears
in the source derivation or the model-specific assumptions. -/
namespace Examples.GuardedSigmaReindexing
open SquareKit SquareKit.Internal SquareKit.Internal.DependentJudgments
open SquareKit.GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u

section General
variable (M : PathTransport.Typed.Model.{u}) (S : Sigma.Stable M.toStructuralModel)
variable (Γ Δ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
  (C : M.Family (M.extend Γ (S.sigma A B)))
  (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)))
  (σ : M.Substitution Δ Γ)

def environment : Fin 7 → Value M.toStructuralModel :=
  ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
    .family (M.extend Γ (S.sigma A B)) C,
    .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d,
    .context Δ, .substitution Δ Γ σ]

theorem source_assumptions : ∀ p ∈ List.ofFn Sigma.Reindexing.splitSubRule.premise,
    p.eval (Sigma.algebra M S.toCapability) (environment M S Γ Δ A B C d σ) := by
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  change Fin 5 at i
  fin_cases i
  · exact ⟨Γ, A, rfl, rfl⟩
  · refine ⟨M.extend Γ A, B, ?_, rfl⟩
    simp [Term.eval, Sigma.algebra, Contextual.algebra, operation, environment]
  · refine ⟨M.extend Γ (S.sigma A B), C, ?_, rfl⟩
    simp [Term.eval, Sigma.algebra, Sigma.operation, Contextual.algebra, operation, environment]
  · refine ⟨M.extend (M.extend Γ A) B, M.subTy C (S.pack A B), d, ?_, ?_, rfl⟩ <;>
      simp [Term.eval, Sigma.algebra, Sigma.operation, Contextual.algebra, operation, environment]
  · exact ⟨Δ, Γ, σ, rfl, rfl, rfl⟩

/-- The source proof compares pulled and freshly rebuilt dependent elimination. -/
theorem fresh_split : Sigma.Reindexing.splitSubRule.conclusion.eval (Sigma.algebra M S.toCapability)
    (environment M S Γ Δ A B C d σ) :=
  Sigma.Reindexing.interpret Sigma.Reindexing.splitReindexDerivation M S _
    (source_assumptions M S Γ Δ A B C d σ)

end General

namespace TwoSubstitutions
open Sigma
private abbrev g : Sigma.Expression (Fin 9) := .var 0
private abbrev a : Sigma.Expression (Fin 9) := .var 1
private abbrev b : Sigma.Expression (Fin 9) := .var 2
private abbrev c : Sigma.Expression (Fin 9) := .var 3
private abbrev branch : Sigma.Expression (Fin 9) := .var 4
private abbrev delta : Sigma.Expression (Fin 9) := .var 5
private abbrev sigmaArrow : Sigma.Expression (Fin 9) := .var 6
private abbrev theta : Sigma.Expression (Fin 9) := .var 7
private abbrev tauArrow : Sigma.Expression (Fin 9) := .var 8

def premises : Fin 6 → Sigma.Judgment (Fin 9) :=
  ![Sigma.family g a, Sigma.family (Sigma.extend g a) b,
    Sigma.family (Sigma.extend g (Sigma.sigma a b)) c, Sigma.term (Sigma.branchContext g a b) (Sigma.subTy c (Sigma.pack a b)) branch,
    Sigma.substitution delta g sigmaArrow, Sigma.substitution theta delta tauArrow]
private abbrev Ω := List.ofFn premises
private def hyp (i : Fin 6) : Derivation Reindexing.theory Ω (premises i) :=
  .hypothesis (List.mem_ofFn.mpr ⟨i, rfl⟩)

abbrev first := Sigma.subTy a sigmaArrow
abbrev second := Sigma.subTy b (Sigma.lift delta a sigmaArrow)
abbrev pulledTwice := Sigma.subTm (Sigma.subTm (Sigma.split a b branch) (Sigma.lift delta (Sigma.sigma a b) sigmaArrow))
  (Sigma.lift theta (Sigma.sigma first second) tauArrow)
abbrev pulledComposite := Sigma.subTm (Sigma.split a b branch)
  (Sigma.comp (Sigma.lift delta (Sigma.sigma a b) sigmaArrow) (Sigma.lift theta (Sigma.sigma first second) tauArrow))
abbrev rebuiltTwice := Sigma.split (Sigma.subTy first tauArrow) (Sigma.subTy second (Sigma.lift theta first tauArrow))
  (Sigma.subTm (Sigma.subTm branch (Sigma.lift (Sigma.extend delta first) b (Sigma.lift delta a sigmaArrow)))
    (Sigma.lift (Sigma.extend theta (Sigma.subTy first tauArrow)) second (Sigma.lift theta first tauArrow)))

def twice_derivation : Reindexing.Equal (Ω := Ω) pulledTwice rebuiltTwice :=
  Reindexing.Tm.splitSubComp (hyp 0) (hyp 1) (hyp 2) (hyp 3) (hyp 4) (hyp 5)

def composite_derivation : Reindexing.Equal (Ω := Ω) pulledComposite rebuiltTwice :=
  Reindexing.Tm.splitSubComposite (hyp 0) (hyp 1) (hyp 2) (hyp 3) (hyp 4) (hyp 5)

end TwoSubstitutions

namespace Nonidentity
private abbrev M := NativeType.model Unit (fun _ => Unit)
private abbrev S := Sigma.Native.stable Unit (fun _ => Unit)
private abbrev A : M.Family Nat := fun n => Fin (n + 1)
private abbrev B : M.Family (M.extend Nat A) := fun p => Fin (p.2.val + 1)
private abbrev C : M.Family (M.extend Nat (S.sigma A B)) := fun p => Fin (p.2.1.val + 1)
private def d : M.Section (M.extend (M.extend Nat A) B) (M.subTy C (S.pack A B)) := ⟨fun p => p.2⟩
private def shift : M.Substitution Nat Nat := ⟨fun n => n + 1⟩
private def double : M.Substitution Nat Nat := ⟨fun n => 2 * n⟩

/-- This is the generic source argument instantiated at varying families and a
nonidentity base arrow, not a separate native proof of the output equation. -/
theorem fresh_shift : Sigma.Reindexing.splitSubRule.conclusion.eval (Sigma.algebra M S.toCapability)
    (environment M S Nat Nat A B C d shift) :=
  fresh_split M S Nat Nat A B C d shift

/-- The composite interpretation retains the source order: shift after doubling. -/
theorem fresh_composite : Sigma.Reindexing.splitSubRule.conclusion.eval (Sigma.algebra M S.toCapability)
    (environment M S Nat Nat A B C d (M.compSub shift double)) :=
  fresh_split M S Nat Nat A B C d (M.compSub shift double)

example : (M.compSub shift double).down 1 = 3 := rfl
example : (M.compSub double shift).down 1 = 4 := rfl

private def twiceEnvironment : Fin 9 → Value M.toStructuralModel :=
  ![.context Nat, .family Nat A, .family (M.extend Nat A) B,
    .family (M.extend Nat (S.sigma A B)) C,
    .term (M.extend (M.extend Nat A) B) (M.subTy C (S.pack A B)) d,
    .context Nat, .substitution Nat Nat shift, .context Nat, .substitution Nat Nat double]

theorem twice_assumptions : ∀ p ∈ List.ofFn TwoSubstitutions.premises,
    p.eval (Sigma.algebra M S.toCapability) twiceEnvironment := by
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  fin_cases i
  · exact ⟨Nat, A, rfl, rfl⟩
  · refine ⟨M.extend Nat A, B, ?_, rfl⟩
    simp [ Term.eval, Sigma.algebra, Contextual.algebra, operation, twiceEnvironment]
  · refine ⟨M.extend Nat (S.sigma A B), C, ?_, rfl⟩
    simp [ Term.eval, Sigma.algebra, Sigma.operation, Contextual.algebra, operation, twiceEnvironment]
  · refine ⟨M.extend (M.extend Nat A) B, M.subTy C (S.pack A B), d, ?_, ?_, rfl⟩ <;>
      simp [ Term.eval, Sigma.algebra, Sigma.operation, Contextual.algebra, operation, twiceEnvironment]
  · exact ⟨Nat, Nat, shift, rfl, rfl, rfl⟩
  · exact ⟨Nat, Nat, double, rfl, rfl, rfl⟩

/-- Actual successive source reindexing rebuilds the second family, motive and
branch at each step from the original assumptions. -/
theorem twice_fresh :
    (Atom.eq TwoSubstitutions.pulledTwice TwoSubstitutions.rebuiltTwice).eval
      (Sigma.algebra M S.toCapability) twiceEnvironment :=
  Sigma.Reindexing.interpret TwoSubstitutions.twice_derivation M S _ twice_assumptions

/-- The inherited source composition rule identifies the two pulls with the
composite of their lifted arrows before the fresh result is compared. -/
theorem composite_fresh :
    (Atom.eq TwoSubstitutions.pulledComposite TwoSubstitutions.rebuiltTwice).eval
      (Sigma.algebra M S.toCapability) twiceEnvironment :=
  Sigma.Reindexing.interpret TwoSubstitutions.composite_derivation M S _ twice_assumptions

end Nonidentity
end Examples.GuardedSigmaReindexing
