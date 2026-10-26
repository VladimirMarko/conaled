import Applications.Resources.SymmetricCosts
import Applications.Sequences.Symmetric.Observation

/-! One measured trajectory with charge/work projections and a composed endpoint consumer.
Provenance and statement review: `docs/research/adwh-potential-accounting.md`. -/
namespace Resources.SymmetricCosts
open Sequences.Symmetric Relational
universe u
variable {α : Type u}

/-- Both resource observations are emitted by one actual transition. -/
def measuredStep (op : Operation α) (s : SymList α) : Measured (SymList α) (Nat × Nat) :=
  let r := execute op s
  (r.state, (r.charge, r.work))

def measuredRun (ops : List (Operation α)) (s : SymList α) := run measuredStep ops s

theorem measuredRun_charge (ops : List (Operation α)) (s : SymList α) :
    reweight (AddMonoidHom.fst Nat Nat) (measuredRun ops s) = run chargeStep ops s :=
  reweight_run (AddMonoidHom.fst Nat Nat) measuredStep ops s

theorem measuredRun_work (ops : List (Operation α)) (s : SymList α) :
    reweight (AddMonoidHom.snd Nat Nat) (measuredRun ops s) = run workStep ops s :=
  reweight_run (AddMonoidHom.snd Nat Nat) measuredStep ops s

theorem measuredRun_inv (ops : List (Operation α)) (s : SymList α) (h : Inv s) :
    Inv (measuredRun ops s).1 :=
  run_invariant measuredStep Inv execute_inv ops s h

theorem measuredRun_abstraction (ops : List (Operation α)) (s : SymList α) (h : Inv s) :
    fromSL (measuredRun ops s).1 = ops.foldl (fun xs op => listStep op xs) (fromSL s) :=
  run_value_fusion measuredStep listStep fromSL Inv execute_inv execute_abstraction ops s h

theorem measuredRun_bounds (ops : List (Operation α)) (s : SymList α) :
    (measuredRun ops s).2.1 + potential (measuredRun ops s).1 ≤ potential s + 2 * ops.length ∧
    (measuredRun ops s).2.2 + 2 * potential (measuredRun ops s).1 ≤ 2 * potential s + 8 * ops.length := by
  have hc := measuredRun_charge ops s
  have hw := measuredRun_work ops s
  have h₁ := run_charge_potential ops s
  have h₂ := run_work_potential ops s
  rw [← hc] at h₁
  rw [← hw] at h₂
  exact ⟨h₁, h₂⟩

def measuredRepresentation (α : Type u) : RelRep where
  R := Measured (SymList α) (Nat × Nat)
  S := List α
  Rel r xs := Inv r.1 ∧ fromSL r.1 = xs

def workloadSquare (ops : List (Operation α)) :
    RelSquare (representation α) (measuredRepresentation α) where
  impl := measuredRun ops
  spec := fun xs => ops.foldl (fun xs op => listStep op xs) xs
  preserves := by
    rintro s xs ⟨h, rfl⟩
    exact ⟨measuredRun_inv ops s h, measuredRun_abstraction ops s h⟩

def measuredEndpointRepresentation (α : Type u) : RelRep where
  R := Measured (Option α) (Nat × Nat)
  S := Option α
  Rel r x := r.1 = x

/-- Observe the final head and retain both accumulated resource measures. -/
def endpointSquare : RelSquare (measuredRepresentation α) (measuredEndpointRepresentation α) where
  impl r := (headSL r.1, r.2)
  spec := List.head?
  preserves := by
    rintro r xs ⟨h, rfl⟩
    exact headSL_eq_head _ h

def observedWorkload (ops : List (Operation α)) :=
  Relational.compose endpointSquare (workloadSquare ops)

theorem observedWorkload_value (ops : List (Operation α)) (s : SymList α) (h : Inv s) :
    ((observedWorkload ops).impl s).1 =
      (ops.foldl (fun xs op => listStep op xs) (fromSL s)).head? :=
  (observedWorkload ops).preserves ⟨h, rfl⟩

theorem observedWorkload_resources (ops : List (Operation α)) (s : SymList α) :
    ((observedWorkload ops).impl s).2 = (measuredRun ops s).2 := rfl

end Resources.SymmetricCosts
