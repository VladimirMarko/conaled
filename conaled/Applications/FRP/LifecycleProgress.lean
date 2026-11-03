import Applications.FRP.LifecycleSafety

/-! Conditional delivery for an accepted pending ID. The result does not exclude
future accepted begins; only its contradiction proof temporarily assumes silence. -/
namespace FRPSpec.Frontier.Lifecycle
open Trace
variable {T α : Type} [LinearOrder T]

/-- A synthetic registration initializes a one-shot reference from the actual
retained sources. Later commands are the fixed-session projection. -/
def sessionCommands (id : Nat) (time : T) (commands : Nat → Command T α) :
    Nat → Engine.Command T α
  | 0 => .register time
  | n+1 => project id (commands n)

/-- Only a matching-ID processing command witnesses enabled processing fairness. -/
def ProcessingFair (s : State T α) (commands : Nat → Command T α) (id : Nat) : Prop :=
  ∀ n time, (state s commands n).last = some id →
    (state s commands n).engine.request = .pending time →
    (∃ out, observe (state s commands n).engine.sources time = some out) →
    ∃ m, n ≤ m ∧ commands m = .process id

private theorem pending_initialized (s : State T α) (time : T)
    (h : s.engine.request = .pending time) :
    s.engine = (Engine.step (Engine.init s.engine.sources) (.register time)).1 := by
  cases s with
  | mk e last =>
    cases e with
    | mk left right request =>
      cases request <;> simp_all [Engine.step,Engine.init,Engine.pack,Engine.MachineState.sources,
        Engine.Command.action,Engine.update,Demand.next]

/-- Under temporary silence, no-loss keeps this session pending, so no accepted
begin can disturb its one-shot simulation. This is not a delivery premise. -/
private theorem silent_simulation (s : State T α) (commands : Nat → Command T α)
    (id : Nat) (time : T) (hl : s.last = some id) (hq : s.engine.request = .pending time)
    (silent : ∀ n out, (event s commands n).response ≠ some ⟨id,time,out⟩) :
    ∀ n, (state s commands n).last = some id ∧
      (state s commands n).engine.request = .pending time ∧
      (state s commands n).engine =
        Engine.state (Engine.init s.engine.sources) (sessionCommands id time commands) (n+1) := by
  have hp : ∀ n, (state s commands n).last = some id ∧
      (state s commands n).engine.request = .pending time := by
    intro n
    rcases pending_or_emitted s commands (Nat.zero_le n) id time hl hq with h | ⟨k,out,_,_,he⟩
    · exact h
    · exact (silent k out he).elim
  have he : ∀ n, (state s commands n).engine =
      Engine.state (Engine.init s.engine.sources) (sessionCommands id time commands) (n+1) := by
    intro n
    induction n with
    | zero => exact pending_initialized s time hq
    | succ n ih =>
      obtain ⟨hs,_,_⟩ := session_step (state s commands n) id (commands n) (hp n).1
        (pending_no_accept _ _ time (hp n).2)
      change (step (state s commands n) (commands n)).1.engine =
        (Engine.step (Engine.state _ _ (n+1)) (project id (commands n))).1
      rw [← ih]
      exact hs
  exact fun n => ⟨(hp n).1,(hp n).2,he n⟩

/-- Delivery uses the existing engine theorem. Source streams/availability describe
future packets from the retained state, and fairness describes actual commands.
Later begins after completion are unrestricted. -/
theorem eventual_response (s : State T α) (commands : Nat → Command T α)
    (id : Nat) (time : T) (hl : s.last = some id) (hq : s.engine.request = .pending time)
    (ms : Streams T α) (actions : Nat → Demand.Action T)
    (aligned : Engine.Aligned ms actions (sessionCommands id time commands))
    (d : Delivery (Demand.sourceSchedule actions)) (fair : d.Fair)
    (processing : ProcessingFair s commands id)
    (progress : ∀ source, ∃ k n, k ≤ d.available source n ∧
      time < (sourcePrefix (s.engine.sources source) (ms source) k).frontier) :
    ∃ n out, (event s commands n).response = some ⟨id,time,out⟩ := by
  by_contra h
  have silent : ∀ n out, (event s commands n).response ≠ some ⟨id,time,out⟩ := by
    intro n out he
    exact h ⟨n,out,he⟩
  have sim := silent_simulation s commands id time hl hq silent
  have pf : Engine.ProcessingFair (Engine.init s.engine.sources) (sessionCommands id time commands) := by
    intro n t hp he
    cases n with
    | zero => simp [Engine.state,Engine.init,Engine.pack] at hp
    | succ n =>
      have ep := (sim n).2.2
      obtain ⟨m,hm,hc⟩ := processing n t (sim n).1 (by simpa [ep] using hp)
        (by simpa [ep] using he)
      refine ⟨m+1,Nat.add_le_add_right hm 1,?_⟩
      simp [sessionCommands,hc,project]
  obtain ⟨n,out,hn,he⟩ := Engine.eventual_response s.engine.sources ms actions
    (sessionCommands id time commands) aligned d fair pf time 1 (by rfl) progress
  cases n with
  | zero => omega
  | succ n =>
    have ep := (sim n).2.2
    obtain ⟨_,_,hr⟩ := session_step (state s commands n) id (commands n) (sim n).1
      (pending_no_accept _ _ time (sim n).2.1)
    have raw : (Engine.step (state s commands n).engine (project id (commands n))).2 =
        some (time,out) := by simpa [Engine.emission,sessionCommands,ep] using he
    apply silent n out
    change (step (state s commands n) (commands n)).2.response = _
    rw [hr,raw]
    rfl

end FRPSpec.Frontier.Lifecycle
