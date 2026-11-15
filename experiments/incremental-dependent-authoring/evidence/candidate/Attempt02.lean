import Examples.DependentPairSharedClient
import Examples.IncrementalDependentTrialSpec

namespace IncrementalCompositional
open SquareKit
open DependentTheoryMaps DependentPairTheoryTransport DependentPairComputedTyping
open DependentPairSharedFragment DependentPairSharedTyping DependentPairPresentations
set_option backward.isDefEq.respectTransparency false

-- Only generated arithmetic indices followed by one pair and observation are interpreted.
def stepIndex : Examples.IncrementalDependentTrialSpec.Op → IndexTerm SingleV → IndexTerm SingleV
  | .successor, e => .successor e
  | .double, e => .double e

def schedule : List Examples.IncrementalDependentTrialSpec.Op → IndexTerm SingleV → IndexTerm SingleV
  | [], e => e
  | op :: ops, e => schedule ops (stepIndex op e)

def index (ops : List Examples.IncrementalDependentTrialSpec.Op) := schedule ops (.var m)
def env (n : Nat) : SingleV → Nat := fun _ => n

theorem step_meaning (op) (e) (ρ) :
    (stepIndex op e).meaning ρ = Examples.IncrementalDependentTrialSpec.step op (e.meaning ρ) := by
  cases op <;> rfl

theorem schedule_meaning (ops) (e) (ρ) :
    (schedule ops e).meaning ρ = Examples.IncrementalDependentTrialSpec.run ops (e.meaning ρ) := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    rw [schedule, ih, step_meaning]
    rfl

theorem index_meaning (ops) (n) : (index ops).meaning (env n) = Examples.IncrementalDependentTrialSpec.run ops n :=
  schedule_meaning ops (.var m) (env n)

theorem schedule_append (xs ys) (e) :
    schedule (xs ++ ys) e = schedule ys (schedule xs e) := by
  induction xs generalizing e with
  | nil => rfl
  | cons op xs ih => exact ih (stepIndex op e)

def sourceProof (ops) := secondProof .source (index ops)
def sourceCode (ops) := compileCode (sourceProof ops)
def targetCode (ops) := compileCode
  (translate (q := .target) (translate (q := .extended) (sourceProof ops)))
noncomputable def native (ops) := nativeProof (sourceProof ops)
noncomputable def targetNative (ops) := targetProof
  (translate (q := .target) (translate (q := .extended) (sourceProof ops)))

theorem source_quote (ops) : (sourceCode ops).sourceQuote = secondRaw (index ops) :=
  compiled_source_quote (sourceProof ops)

theorem target_quote (ops) : (targetCode ops).targetQuote = targetTerm (.second (index ops)) :=
  (DependentPairSharedClient.compiled_image (sourceProof ops) (env 0)).2.1

theorem source_execution (ops) (n) : (sourceCode ops).run (env n) = Examples.IncrementalDependentTrialSpec.selected ops n := by
  rw [sourceCode, compileCode_sound, meaning_expected]
  change selected ((index ops).meaning (env n)) = _
  rw [index_meaning]
  rfl

theorem target_execution (ops) (n) : (targetCode ops).run (env n) = Examples.IncrementalDependentTrialSpec.selected ops n := by
  rw [(DependentPairSharedClient.compiled_image (sourceProof ops) (env n)).2.2]
  rw [meaning_expected]
  change selected ((index ops).meaning (env n)) = _
  rw [index_meaning]
  rfl

theorem native_fullG (ops) : targetNative ops = DependentPairJudgments.compile (native ops) :=
  (DependentPairSharedClient.compiled_image (sourceProof ops) (env 0)).1

theorem native_FG (ops) : targetNative ops =
    DependentPairJudgments.Administrative.erase
      (DependentPairJudgments.TypedSubstitution.fullEliminationLocal _)
      (fun _ h => Empty.elim h)
      (DependentPairJudgments.Administrative.pairFG.transport (fun _ h => Empty.elim h)
        (DependentPairJudgments.Administrative.embed (native ops))) :=
  two_stages_native_certificates (sourceProof ops)

theorem code_index_append (xs ys) (n) :
    (Code.index .source (index (xs ++ ys))).run (env n) =
      (Code.index .source (index ys)).run
        (env ((Code.index .source (index xs)).run (env n))) := by
  simp only [Code.index_run]
  rw [index, schedule_append, schedule_meaning]
  rw [index_meaning]

theorem selected_append (xs ys) (n) :
    (targetCode (xs ++ ys)).run (env n) =
      (targetCode ys).run (env ((Code.index .source (index xs)).run (env n))) := by
  rw [target_execution, target_execution, Code.index_run, index_meaning]
  change selected (Examples.IncrementalDependentTrialSpec.run (xs ++ ys) n) = selected (Examples.IncrementalDependentTrialSpec.run ys (Examples.IncrementalDependentTrialSpec.run xs n))
  congr 1
  exact List.foldl_append

theorem empty_execution (n) : (targetCode []).run (env n) =
    (⟨n + 1, ⟨n + 1, by omega⟩⟩ : Examples.IncrementalDependentTrialSpec.Packet) := target_execution [] n

-- Substitution on the bounded arithmetic syntax.
def replace (σ : SingleV → IndexTerm SingleV) : IndexTerm SingleV → IndexTerm SingleV
  | .var v => σ v
  | .successor e => .successor (replace σ e)
  | .double e => .double (replace σ e)

theorem replace_meaning (σ) (e) (ρ) :
    (replace σ e).meaning ρ = e.meaning (fun v => (σ v).meaning ρ) := by
  induction e with
  | var v => rfl
  | successor e ih => exact congrArg (fun n : Nat => n + 1) ih
  | double e ih => exact congrArg (fun n : Nat => 2 * n) ih

theorem replace_schedule (σ) (ops) (e) :
    replace σ (schedule ops e) = schedule ops (replace σ e) := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    rw [schedule, ih, schedule]
    cases op <;> rfl

theorem expression_replace (σ) (e) :
    Expr.subst (fun v => (σ v).expression) e.expression = (replace σ e).expression := by
  induction e with
  | var v => rfl
  | successor e ih =>
    simp [IndexTerm.expression, replace, s, DependentPairDeclarations.Projection.s,
      DependentPairDeclarations.Terms.s, DependentPairDeclarations.projection, Expr.subst, Elimination.subst_zero, ih]
  | double e ih =>
    simp [IndexTerm.expression, replace, d, DependentPairDeclarations.Projection.d,
      DependentPairDeclarations.Terms.d, DependentPairDeclarations.projection, Expr.subst, Elimination.subst_zero, ih]

end IncrementalCompositional
