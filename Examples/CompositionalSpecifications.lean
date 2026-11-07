import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Specification
import Examples.PrimitiveDependentSums

/-! A selected dependent index survives a derived-rule expansion and two
specification changes. The existing native and separating clients remain usable. -/
namespace Examples.CompositionalSpecifications
open SquareKit SquareKit.Internal
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.PathTransport.Typed
open PrimitiveSigma PrimitiveSigma.Specification
set_option backward.isDefEq.respectTransparency false

abbrev M := NativeType.model Unit (fun _ => Unit)
abbrev S := Sigma.Native.stable Unit (fun _ => Unit)
noncomputable abbrev target := strongModel M S
noncomputable abbrev direct := composedView.reduct target
noncomputable abbrev staged := stableView.reduct (etaView.reduct target)

example : direct = staged := RuleInterpretation.reduct_compose etaView stableView target
example : (RuleInterpretation.identity etaTheory).reduct target = target :=
  RuleInterpretation.reduct_identity target

abbrev A : M.Family Unit := fun _ => Nat
abbrev B : M.Family (M.extend Unit A) := fun p => Fin (p.2 + 1)
abbrev C : M.Family (M.extend Unit (S.sigma A B)) := fun p => Fin (p.2.1 + 1)
abbrev branch : M.Section (M.extend (M.extend Unit A) B)
    (M.subTy C (S.pack A B)) := ⟨Sigma.Native.boundedBranch⟩

/-- The chosen index varies with the context, and is not always zero. -/
def selected : M.Substitution Nat (M.extend (M.extend Unit A) B) :=
  ⟨fun n => ⟨⟨(), n + 1⟩, ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩⟩⟩

def valuation : Fin 7 → Value M.toStructuralModel :=
  ![.context Unit, .family Unit A, .family (M.extend Unit A) B,
    .family (M.extend Unit (S.sigma A B)) C,
    .term (M.extend (M.extend Unit A) B) (M.subTy C (S.pack A B)) branch,
    .context Nat, .substitution Nat (M.extend (M.extend Unit A) B) selected]

local macro "eval_simp" : tactic => `(tactic|
  simp [target, strongModel, Term.eval, FinitaryTerm.fold, PrimitiveSigma.algebra, PrimitiveSigma.operation, Contextual.algebra,
    DependentJudgments.operation, valuation, ofStrong])

theorem premises : ∀ i, (reindexedBetaRule.premise i).eval target.toAlgebra valuation := by
  intro i
  fin_cases i
  · exact ⟨Unit, A, rfl, rfl⟩
  · refine ⟨M.extend Unit A, B, ?_, rfl⟩
    eval_simp
  · refine ⟨M.extend Unit (S.sigma A B), C, ?_, rfl⟩
    eval_simp
  · refine ⟨M.extend (M.extend Unit A) B, M.subTy C (S.pack A B), branch, ?_, ?_, rfl⟩ <;>
      eval_simp
  · refine ⟨Nat, M.extend (M.extend Unit A) B, selected, rfl, ?_, rfl⟩
    eval_simp

/-- A client uses only its published rule. Its implementation expands that
rule into beta and congruence and then traverses the two specification views. -/
noncomputable def client : Derivation clientTheory
    (List.ofFn reindexedBetaRule.premise) reindexedBetaRule.conclusion :=
  RuleInterpretation.axiomDerivation clientTheory ()

noncomputable def transported : Derivation etaTheory
    (List.ofFn reindexedBetaRule.premise) reindexedBetaRule.conclusion :=
  (composedView.compose clientView).transport client

theorem selected_computation : reindexedBetaRule.conclusion.eval target.toAlgebra valuation :=
  transported.sound target valuation (by
    intro p hp
    rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
    exact premises i)

abbrev expression : PrimitiveSigma.Expression (Fin 7) :=
  PrimitiveSigma.subTm (PrimitiveSigma.subTm (split (.var 1) (.var 2) (.var 3) (.var 4))
    (pack (.var 1) (.var 2))) (.var 6)

/-- The transported source equality yields this exact section, not existence
of a section with the same type. -/
theorem selected_value : expression.eval target.toAlgebra valuation =
    .term Nat (M.subTy (M.subTy C (S.pack A B)) selected) (M.subTm branch selected) := by
  have h := selected_computation
  change expression.eval target.toAlgebra valuation =
    (PrimitiveSigma.subTm (.var 4) (.var 6)).eval target.toAlgebra valuation at h
  rw [h]
  eval_simp

/-- Both interpretation routes retain the same nonzero selected witness. -/
example : expression.eval staged.toAlgebra valuation =
    .term Nat (fun n => Fin (n + 2)) ⟨fun n => ⟨n, by omega⟩⟩ := selected_value

example : (M.subTm branch selected).down 3 = (⟨3, by omega⟩ : Fin 5) := rfl
example : (M.subTm branch selected).down 3 ≠ (⟨0, by omega⟩ : Fin 5) := by
  intro h
  have hv := congrArg Fin.val h
  change 3 = 0 at hv
  omega

/-- A second nonidentity substitution changes the selected value and its bound. -/
def double : M.Substitution Nat Nat := ⟨fun n => 2 * n⟩

theorem selected_twice : HEq (M.subTm (M.subTm branch selected) double)
    (M.subTm branch (M.compSub selected double)) := M.subTm_comp branch selected double

example : (M.subTm (M.subTm branch selected) double).down 3 = (⟨6, by omega⟩ : Fin 8) := rfl

/-- Decode the transported source result and reindex it again. The selected
index 6 is recovered from that result, rather than from an unrelated native proof. -/
theorem decoded_twice :
    Option.map (fun t : M.Section Nat (M.subTy (M.subTy C (S.pack A B)) selected) =>
      (M.subTm t double).down 3)
      (Value.termAt Nat (M.subTy (M.subTy C (S.pack A B)) selected)
        (expression.eval staged.toAlgebra valuation)) = some (⟨6, by omega⟩ : Fin 8) := by
  have h := congrArg
    (fun v : Value M.toStructuralModel =>
      Option.map (fun t : M.Section Nat (M.subTy (M.subTy C (S.pack A B)) selected) =>
        (M.subTm t double).down 3)
        (Value.termAt Nat (M.subTy (M.subTy C (S.pack A B)) selected) v)) selected_value
  change Option.map (fun t : M.Section Nat (M.subTy (M.subTy C (S.pack A B)) selected) =>
      (M.subTm t double).down 3)
      (Value.termAt Nat (M.subTy (M.subTy C (S.pack A B)) selected)
        (expression.eval target.toAlgebra valuation)) =
    some ((M.subTm (M.subTm branch selected) double).down 3)
  exact h.trans (by rw [Value.termAt_term]; rfl)

/-- This stronger same-syntax theory has no interpretation back into the weak
stable theory, despite that theory supporting the shared dependent computation. -/
example : ¬ Nonempty (RuleInterpretation etaTheory Reindexing.theory) := no_reverse_view

end Examples.CompositionalSpecifications
