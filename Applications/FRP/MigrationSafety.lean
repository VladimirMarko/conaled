import Applications.FRP.MigrationResources

/-! Reachable phase discipline and conditional completion for explicit migration. -/
set_option autoImplicit false
set_option warningAsError true
namespace FRPSpec.Migration

/-- A prepared target exists only at a quiescent boundary for the latched request. -/
def Safe (s : Session) : Prop := match s.prepared with
  | none => True
  | some p => s.flight = .idle ∧ s.request = some p.target.kind

@[simp] theorem initial_safe (k : Kind) : Safe (initial k) := trivial

set_option maxHeartbeats 800000 in
theorem step_safe (s : Session) (c : Command) (h : Safe s) : Safe (step s c).session := by
  rcases s with ⟨active,flight,last,request,prepared⟩
  cases prepared with
  | none =>
    cases c <;> cases flight <;> cases request <;> simp only [step, reject]
    all_goals try split_ifs
    all_goals simp_all [Safe]
  | some p =>
    change flight = .idle ∧ request = some p.target.kind at h
    rcases h with ⟨rfl,rfl⟩
    cases c <;> simp only [step, reject]
    all_goals try split_ifs
    all_goals simp_all [Safe]

theorem execute_safe (s : Session) (cs : List Command) (h : Safe s) : Safe (execute s cs).1 := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih (step s c).session (step_safe s c h)

theorem wrong_owner_preserves (s : Session) (owner : Kind) (h : owner ≠ s.active.kind) :
    (step s (.evaluate (some owner))).session = s := by simp [step, h, reject]

/-- The fixed protocol reserves at most 87 slots during migration preparation;
128 is the adapter's declared logical transfer budget. -/
theorem migration_from_idle (old : Backend) (last : Option Bool) (target : Kind) :
    let s : Session := ⟨old,.idle,last,some target,none⟩
    (execute s [.prepare 128 true true,.ownershipCommit]).1.active = realize target old.logical ∧
    (execute s [.prepare 128 true true,.ownershipCommit]).2 = ([],[]) := by
  cases old with
  | delay b => cases b <;> cases target <;> exact ⟨rfl,rfl⟩
  | redundant p =>
    rcases p with ⟨b,c,h⟩
    subst c
    cases b <;> cases target <;> exact ⟨rfl,rfl⟩

theorem drain_state (s : Session) : (execute s (drain s)).1.active.logical = future s := by
  rcases s with ⟨active,flight,last,request,prepared⟩
  cases flight with
  | idle => rfl
  | accepted x => exact (evaluate active x).state_eq
  | pending x r => exact r.state_eq
  | published x r => exact r.state_eq

/-- A latched migration with no prepared storage commits after the old tick is
retired and the explicit successful preparation/commit commands are scheduled. -/
theorem drain_then_migrate (old : Backend) (flight : Flight old) (last : Option Bool)
    (target : Kind) :
    let s : Session := ⟨old,flight,last,some target,none⟩
    let drained := (execute s (drain s)).1
    (execute drained [.prepare 128 true true,.ownershipCommit]).1.active =
      realize target (future s) := by
  cases flight with
  | idle => exact (migration_from_idle old last target).1
  | accepted x =>
    change (execute ⟨(evaluate old x).candidate,.idle,some (evaluate old x).output,
      some target,none⟩ [.prepare 128 true true,.ownershipCommit]).1.active = realize target x
    have h := (migration_from_idle (evaluate old x).candidate
      (some (evaluate old x).output) target).1
    simpa only [TickResult.state_eq] using h
  | pending x r =>
    change (execute ⟨r.candidate,.idle,some r.output,some target,none⟩
      [.prepare 128 true true,.ownershipCommit]).1.active = realize target x
    have h := (migration_from_idle r.candidate (some r.output) target).1
    simpa only [TickResult.state_eq] using h
  | published x r =>
    change (execute ⟨r.candidate,.idle,last,some target,none⟩
      [.prepare 128 true true,.ownershipCommit]).1.active = realize target x
    have h := (migration_from_idle r.candidate last target).1
    simpa only [TickResult.state_eq] using h

/-- Arbitrary finite sink refusal waits preserve the complete session. Their
length is not bounded by the implementation; cancellation remains available. -/
theorem refusal_wait (s : Session) (n : Nat) :
    (execute s (List.replicate n (.sink false))).1 = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, execute, refusal_preserves, ih]

end FRPSpec.Migration
