import Lean
import Examples.ConversionTrial.DirectReference
import Examples.ConversionTrial.ServiceReference
import Examples.ConversionTrial.SeparatingModel
import ProofAudit

/-! Preparation-only validation and metrics. Never release this oracle module to authors. -/
namespace Examples.ConversionTrial.Validate
open SquareKit.Internal.DependentFunctions

theorem both_initial : Initial.Task ∧ Initial.Task :=
  ⟨DirectReference.initial, ServiceReference.initial⟩
theorem both_composition : Scale.CompositionTask ∧ Scale.CompositionTask :=
  ⟨DirectReference.composition, ServiceReference.composition⟩
theorem both_contexts : Scale.ContextTask ∧ Scale.ContextTask :=
  ⟨DirectReference.contexts, ServiceReference.contexts⟩
theorem both_substitutions : Scale.SubstitutionTask ∧ Scale.SubstitutionTask :=
  ⟨DirectReference.substitutions, ServiceReference.substitutions⟩
theorem both_repair : Repair.Task ∧ Repair.Task :=
  ⟨DirectReference.repair, ServiceReference.repair⟩
theorem both_held_out : HeldOut.Task ∧ HeldOut.Task :=
  ⟨DirectReference.held_out, ServiceReference.held_out⟩
theorem independent_head_control : Negative.HeadTask := SeparatingModel.head_negative

-- Every substitution used by the fixtures changes the surviving original variable.
example : liftedNegate 1 ≠ Sub.id (widen 1) := by
  intro h
  have he := congrArg (fun s : Sub (widen 1) (widen 1) => s.base 1) h
  cases he

example : liftedNegate 2 ≠ Sub.id (widen 2) := by
  intro h
  have he := congrArg (fun s : Sub (widen 2) (widen 2) => s.base 2) h
  cases he

example : liftedNegate 3 ≠ Sub.id (widen 3) := by
  intro h
  have he := congrArg (fun s : Sub (widen 3) (widen 3) => s.base 3) h
  cases he

example : liftedNegate 7 ≠ Sub.id (widen 7) := by
  intro h
  have he := congrArg (fun s : Sub (widen 7) (widen 7) => s.base 7) h
  cases he

def termMetrics {n : Nat} {Δ : Ctx n} (t u : Dep Δ) (substitutions : Nat) : List Nat :=
  [contextWidth Δ, depNodes t, depNodes u, depRedexDepth t, substitutions,
   baseNodes t.type, indexDepth t.type]

def metricRows : List (String × List Nat) :=
  [("initial", metrics 1 1 2),
   ("composition-1", metrics 1 1 2), ("composition-4", metrics 1 4 2), ("composition-8", metrics 1 8 2),
   ("context-2", metrics 1 1 2), ("context-4", metrics 3 1 2), ("context-8", metrics 7 1 2),
   ("substitution-1", metrics 1 1 1), ("substitution-2", metrics 1 1 2), ("substitution-4", metrics 1 1 4),
   ("repair-before", termMetrics Repair.before Repair.beforeTarget 1),
   ("repair-after", termMetrics Repair.after Repair.afterTarget 1),
   ("held-out", metrics 2 2 3),
   ("negative-index", termMetrics Initial.lhs Negative.bad 2)]

-- Measurements evaluate the instantiated object syntax. Native evaluation is
-- used only for data reporting, never as a mathematical proof certificate.
#eval IO.println ("TRIAL_METRICS " ++ (Lean.toJson metricRows).compress)

run_cmd do
  let env ← Lean.getEnv
  Lean.logInfo ("TRIAL_IMPORTS " ++ (Lean.toJson (env.header.moduleNames.map toString)).compress)

end Examples.ConversionTrial.Validate
#audit_project_axioms
