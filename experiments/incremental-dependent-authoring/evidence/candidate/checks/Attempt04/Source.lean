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
  unfold targetCode
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
  rfl

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
    simp only [IndexTerm.expression, replace, s, DependentPairDeclarations.Projection.s,
      DependentPairDeclarations.Terms.s, DependentPairDeclarations.projection, Expr.subst]
    congr 1
    funext i
    change Fin 1 at i
    fin_cases i
    change Expr.subst (Expr.lift (fun v => (σ v).expression)) (zero e.expression) = zero (replace σ e).expression
    rw [Elimination.subst_zero, ih]
  | double e ih =>
    simp only [IndexTerm.expression, replace, d, DependentPairDeclarations.Projection.d,
      DependentPairDeclarations.Terms.d, DependentPairDeclarations.projection, Expr.subst]
    congr 1
    funext i
    change Fin 1 at i
    fin_cases i
    change Expr.subst (Expr.lift (fun v => (σ v).expression)) (zero e.expression) = zero (replace σ e).expression
    rw [Elimination.subst_zero, ih]


theorem second_replace (σ) (e) :
    Expr.subst (fun v => (σ v).expression) (secondRaw e) = secondRaw (replace σ e) := by
  simp [secondRaw, pairRaw, familyB, N, B, s, t,
    DependentPairDeclarations.Projection.N, DependentPairDeclarations.Projection.B,
    DependentPairDeclarations.Projection.s, DependentPairDeclarations.Projection.t,
    Expr.lift, expression_replace]

def resultType (e : IndexTerm SingleV) :=
  Elimination.instantiate familyB (Projection.fst N familyB (pairRaw e))

theorem type_replace (σ) (e) :
    Expr.subst (fun v => (σ v).expression) (resultType e) = resultType (replace σ e) := by
  simp [resultType, pairRaw, familyB, N, B, s, t,
    DependentPairDeclarations.Projection.N, DependentPairDeclarations.Projection.B,
    DependentPairDeclarations.Projection.s, DependentPairDeclarations.Projection.t,
    Expr.lift, expression_replace]


theorem sigma_expression : (fun v => (sigmaIndex v).expression) = successorSub := by
  funext v
  cases v with
  | inl i => rfl
  | inr e => exact e.elim

theorem tau_expression : (fun v => (tauIndex v).expression) = tauRaw := by
  funext v
  cases v with
  | inl i => rfl
  | inr e => exact e.elim

def afterSigma (ops) := replace sigmaIndex (index ops)
def afterTwice (ops) := replace tauIndex (afterSigma ops)

theorem term_sigma (ops) : Expr.subst successorSub (secondRaw (index ops)) =
    secondRaw (afterSigma ops) := by
  rw [← sigma_expression]
  exact second_replace _ _

theorem type_sigma (ops) : Expr.subst successorSub (resultType (index ops)) =
    resultType (afterSigma ops) := by
  rw [← sigma_expression]
  exact type_replace _ _

theorem term_twice (ops) : Expr.subst tauRaw
    (Expr.subst successorSub (secondRaw (index ops))) = secondRaw (afterTwice ops) := by
  rw [term_sigma, ← tau_expression]
  exact second_replace _ _

theorem type_twice (ops) : Expr.subst tauRaw
    (Expr.subst successorSub (resultType (index ops))) = resultType (afterTwice ops) := by
  rw [type_sigma, ← tau_expression]
  exact type_replace _ _

noncomputable def nativeSigma (ops) : DependentPairTypedClient.Proof
    (Judgment.term DependentPairTypedClient.Γn (secondRaw (afterSigma ops))
      (resultType (afterSigma ops))) := by
  have h := secondSigma (index ops)
  change DependentPairTypedClient.Proof
    (Judgment.term DependentPairTypedClient.Γn
      (Expr.subst successorSub (secondRaw (index ops)))
      (Expr.subst successorSub (resultType (index ops)))) at h
  rw [term_sigma, type_sigma] at h
  exact h

noncomputable def nativeTwice (ops) : DependentPairTypedClient.Proof
    (Judgment.term DependentPairTypedClient.Γn (secondRaw (afterTwice ops))
      (resultType (afterTwice ops))) := by
  have h := secondTwice (index ops)
  change DependentPairTypedClient.Proof
    (Judgment.term DependentPairTypedClient.Γn
      (Expr.subst tauRaw (Expr.subst successorSub (secondRaw (index ops))))
      (Expr.subst tauRaw (Expr.subst successorSub (resultType (index ops))))) at h
  rw [term_twice, type_twice] at h
  exact h

noncomputable def targetNativeTwice (ops) := DependentPairJudgments.compile (nativeTwice ops)

def substitutedSourceCode (ops) := compileCode (secondProof .source (afterTwice ops))
def substitutedTargetCode (ops) := compileCode
  (translate (q := .target) (translate (q := .extended) (secondProof .source (afterTwice ops))))

theorem twice_meaning (ops) (n) : (afterTwice ops).meaning (env n) =
    Examples.IncrementalDependentTrialSpec.run ops
      (Examples.IncrementalDependentTrialSpec.sigma (Examples.IncrementalDependentTrialSpec.tau n)) := by
  unfold afterTwice afterSigma
  rw [replace_meaning, replace_meaning]
  exact schedule_meaning ops (.var m) _

theorem substituted_execution (ops) (n) : (substitutedTargetCode ops).run (env n) =
    Examples.IncrementalDependentTrialSpec.selected ops
      (Examples.IncrementalDependentTrialSpec.sigma (Examples.IncrementalDependentTrialSpec.tau n)) := by
  unfold substitutedTargetCode
  rw [(DependentPairSharedClient.compiled_image (secondProof .source (afterTwice ops)) (env n)).2.2,
    meaning_expected]
  change selected ((afterTwice ops).meaning (env n)) = _
  rw [twice_meaning]
  rfl

theorem substituted_source_quote (ops) : (substitutedSourceCode ops).sourceQuote =
    Expr.subst tauRaw (Expr.subst successorSub (secondRaw (index ops))) := by
  rw [term_twice]
  exact compiled_source_quote _

theorem substituted_target_quote (ops) : (substitutedTargetCode ops).targetQuote =
    Expr.subst (fun v => G.act (tauRaw v))
      (Expr.subst (fun v => G.act (successorSub v)) (targetTerm (.second (index ops)))) := by
  unfold substitutedTargetCode
  rw [compiled_target_quote]
  unfold targetTerm sourceTerm
  rw [← G.substitution, ← G.substitution, term_twice]

-- Numerical cases consume the arbitrary-schedule preservation theorems.
theorem demo_execution : (targetCode Examples.IncrementalDependentTrialSpec.demo).run (env 3) =
    Examples.IncrementalDependentTrialSpec.demoAnswer := by
  rw [target_execution]
  rfl

theorem demo_substituted : (substitutedTargetCode Examples.IncrementalDependentTrialSpec.demo).run (env 3) =
    Examples.IncrementalDependentTrialSpec.substitutedAnswer := by
  rw [substituted_execution]
  rfl

theorem reject_wrong : (substitutedTargetCode Examples.IncrementalDependentTrialSpec.demo).run (env 3) ≠
    Examples.IncrementalDependentTrialSpec.wrongAnswer := by
  rw [demo_substituted]
  intro h
  have hv := congrArg (fun p : Examples.IncrementalDependentTrialSpec.Packet => p.2.val) h
  change 34 = 0 at hv
  omega

end IncrementalCompositional
