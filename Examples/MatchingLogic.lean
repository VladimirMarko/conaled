import Applications.MatchingLogic.ConfigurationModel

/-! Positive and rejecting uses of the bounded fragment. Native sets and labelled
traces remain available independently of symbolic derivations. -/
namespace Examples.MatchingLogic
open _root_.MatchingLogic _root_.MatchingLogic.Configuration

def input (n : Nat) : Valuation model [.nat] := Valuation.extend (t := .nat) emptyVal n

theorem exact_arbitrary (n : Nat) :
    eval model (.app .step (.app .run (.var .here))) (input n) = {.done n,.done (n+1)} :=
  symbolic_exact .here (input n)

theorem terminal_arbitrary (n : Nat) :
    eval model (.app .step (.app .done (.var .here))) (input n) = ∅ :=
  symbolic_terminal .here (input n)

theorem all_terminal :
    eval model (.ex .nat (.app .step (.app .run (.var .here)))) emptyVal = {c | ∃ n, c = .done n} :=
  terminal_family emptyVal

theorem same_safety (n : Nat) (B : Set Cfg) :
    (eval model (.app .step (.app .run (.var .here))) (input n) ⊆ B) ↔ Safe (.run n) B :=
  safety_iff .here (input n) B

theorem excluded_arbitrary (n : Nat) :
    Cfg.done (n+2) ∉ eval model (.app .step (.app .run (.var .here))) (input n) :=
  symbolic_excluded .here (input n)

/-- The public consumer retains actual derivation data, not just its validity. -/
def derivation : Derives Axiom (initialResults.equal .cfg initialStep) := inferenceSymmetry
theorem derivation_sound : eval model (initialResults.equal .cfg initialStep) emptyVal = Set.univ :=
  derivation.sound model axioms_valid emptyVal

/-- Under the C binder, the old N variable is shifted, while the fresh C variable
is used in the negated equality. This tests both sorts and actual binding. -/
def boundBody : Pattern [.cfg,.nat] .cfg :=
  .neg ((Pattern.app .run (.var (.there .here))).equal .cfg (.var .here))
def boundPattern : Pattern [.nat] .cfg := .ex .cfg boundBody

theorem substitution_under_negated_binder :
    eval model (boundPattern.substOne .zero) emptyVal = eval model boundPattern (input 0) :=
  eval_substOne model boundPattern .zero emptyVal 0 rfl

/-- The binder variable changes the body denotation, so it is not vacuous. -/
theorem bound_variable_matters :
    eval model boundBody (Valuation.extend (t := .cfg) (input 0) (.run 0)) = ∅ ∧
    eval model boundBody (Valuation.extend (t := .cfg) (input 0) (.done 0)) = Set.univ := by
  constructor <;> ext d
  · change ¬d ∈ eval model ((Pattern.app .run (.var (.there .here))).equal .cfg (.var .here))
      (Valuation.extend (t := .cfg) (input 0) (.run 0)) ↔ False
    rw [mem_eval_equal]
    simp [eval, model, symbolMeaning, input, Valuation.extend]
  · change ¬d ∈ eval model ((Pattern.app .run (.var (.there .here))).equal .cfg (.var .here))
      (Valuation.extend (t := .cfg) (input 0) (.done 0)) ↔ True
    rw [mem_eval_equal]
    simp [eval, model, symbolMeaning, input, Valuation.extend]

/-- Renaming under binders preserves the result with the pulled-back valuation. -/
theorem weakening_binder (n : Nat) (c : Cfg) :
    eval model (boundPattern.rename Var.there) (Valuation.extend (t := .cfg) (input n) c) = eval model boundPattern (input n) := by
  rw [eval_rename]
  rfl

/-- A context entry not occurring in the pattern is irrelevant to evaluation. -/
theorem unused_cfg_variable (n : Nat) (c d : Cfg) :
    eval model (Pattern.var (.there (.here : Var [.nat] .nat))) (Valuation.extend (t := .cfg) (input n) c) =
      eval model (.var (.there .here)) (Valuation.extend (t := .cfg) (input n) d) := by
  apply eval_agree
  intro t v hv
  cases hv
  rfl

theorem nonempty_unrestricted_failure :
    (eval model initialStep emptyVal).Nonempty ∧
    Valid model ((Pattern.var (.here : Var [.cfg] .cfg)).functional .cfg).all ∧
    eval model (initialStep.functional .cfg) emptyVal = ∅ :=
  ⟨initial_nonempty, unrestricted_substitution_rejected⟩

/-- The rejected conclusion is the actual capture-avoiding substitution of the
non-singleton pattern into the universally quantified premise above. -/
theorem unrestricted_result_is_substitution :
    eval model (((Pattern.var (.here : Var [.cfg] .cfg)).functional .cfg).substOne initialStep)
      emptyVal = ∅ := unrestricted_substitution_rejected.2

theorem step_not_functional : ¬Valid model (initialStep.functional .cfg) := by
  intro h
  have he := h emptyVal
  rw [unrestricted_substitution_rejected.2] at he
  have hm : Cfg.run 0 ∈ (∅ : Set Cfg) := he.symm ▸ Set.mem_univ _
  exact hm

theorem empty_failure_separate (a : Cfg) :
    eval model (.app .step (.app .done .zero)) emptyVal ≠ {a} := terminal_not_singleton a

theorem labels_lost (n : Nat) : keepA n ≠ keepB n ∧ (keepA n).forget = (keepB n).forget :=
  ⟨keep_distinct n, forgotten_equal n⟩

theorem chosen_not_recovered (n : Nat) :
    select (.run n) (.done n) (keepB n).forget = keepA n ∧
      select (.run n) (.done n) (keepB n).forget ≠ keepB n := by
  have h : select (.run n) (.done n) (keepB n).forget = keepA n := select_keep n
  exact ⟨h,h ▸ keep_distinct n⟩

theorem enriched_recovers_outcomes (c : Cfg) : Prod.fst '' enriched c = outcomes c := enriched_forget c

end Examples.MatchingLogic
