import Applications.FRP.Exclusive

/-! Occurrence provenance and conditional progress for exclusive requests. -/
namespace FRPSpec.Frontier.Exclusive
open Trace
variable {T α : Type} [LinearOrder T]

theorem emitted {s : State T α} {c : Command T α} {t : T} {xs : List α}
    (h : (step s c).2.response = some (t,xs)) :
    c = .process ∧ s.request = .pending t ∧ observe s.sources t = some xs ∧
      (step s c).1.request = .done := by
  have hr : (Lifecycle.step (reference s 0) (labelCommand 0 c)).2.response =
      some ⟨0,t,xs⟩ := by simp [step_refines,h,Lifecycle.tag]
  obtain ⟨hc,_,hp,ho,_,hd⟩ := Lifecycle.emitted hr
  have cp : c = .process := by cases c <;> simp_all [labelCommand]
  change (Lifecycle.step (reference s 0) (labelCommand 0 c)).1.engine.request = .done at hd
  rw [step_refines] at hd
  exact ⟨cp,hp,ho,hd⟩

theorem no_lost_work (s : State T α) (c : Command T α) (t : T)
    (h : s.request = .pending t) :
    (step s c).1.request = .pending t ∨ ∃ xs, (step s c).2.response = some (t,xs) := by
  rcases Lifecycle.no_lost_work (reference s 0) (labelCommand 0 c) 0 t rfl h with hp | ⟨xs,he⟩
  · have hh := hp.2
    change (Lifecycle.step (reference s 0) (labelCommand 0 c)).1.engine.request = .pending t at hh
    rw [step_refines] at hh
    exact .inl hh
  · right; refine ⟨xs,?_⟩
    simpa [step_refines,Lifecycle.tag] using he

theorem pending_no_accept (s : State T α) (c : Command T α) (t : T)
    (h : s.request = .pending t) : (step s c).2.status ≠ some .accepted := by
  cases c <;> simp [step,h]

/-- Provenance names the accepted occurrence by its post-begin proof label.
The initial state is absent, so a reserved initial label cannot emit. -/
theorem pending_provenance (sources : Inputs T α) (commands : Nat → Command T α)
    (n : Nat) (t : T) (hp : (state (init sources) commands n).request = .pending t) :
    ∃ k, k < n ∧ commands k = .begin t ∧
      (event (init sources) commands k).status = some .accepted ∧
      label (init sources) commands (k+1) = label (init sources) commands n := by
  induction n with
  | zero => simp [state,init,Engine.init,Engine.pack] at hp
  | succ n ih =>
    let s := state (init sources) commands n
    let l := label (init sources) commands n
    have hh : (Lifecycle.step (reference s l) (labelCommand l (commands n))).1.last =
        some (label (init sources) commands (n+1)) := by rw [step_refines]; rfl
    have hq : (Lifecycle.step (reference s l) (labelCommand l (commands n))).1.engine.request =
        .pending t := by rw [step_refines]; exact hp
    rcases Lifecycle.pending_pre_or_begin _ _ _ t hh hq with ⟨hl,hpre⟩ | ⟨hc,ha⟩
    · have eqLabel : label (init sources) commands (n+1) = l := (Option.some.inj hl).symm
      obtain ⟨k,hk,hc,ha,he⟩ := ih hpre
      exact ⟨k,Nat.lt_succ_of_lt hk,hc,ha,he.trans eqLabel.symm⟩
    · have cmd : commands n = .begin t := by
        cases hh : commands n <;> simp_all [labelCommand]
      refine ⟨n,Nat.lt_succ_self _,cmd,?_,rfl⟩
      rw [step_refines] at ha
      change ((event (init sources) commands n).status.map _) = some Lifecycle.BeginStatus.accepted at ha
      cases hs : (event (init sources) commands n).status with
      | none => simp [hs] at ha
      | some k => cases k <;> simp_all

theorem response_provenance (sources : Inputs T α) (commands : Nat → Command T α)
    (n : Nat) (t : T) (xs : List α)
    (h : (event (init sources) commands n).response = some (t,xs)) :
    ∃ k, k < n ∧ commands k = .begin t ∧
      (event (init sources) commands k).status = some .accepted ∧
      label (init sources) commands (k+1) = label (init sources) commands n :=
  pending_provenance sources commands n t (emitted h).2.1

/-- Source packets and generic process commands projected onto a single session. -/
def sessionCommands (time : T) (commands : Nat → Command T α) : Nat → Engine.Command T α
  | 0 => .register time
  | n+1 => project (commands n)

def ProcessingFair (s : State T α) (commands : Nat → Command T α) : Prop :=
  ∀ n t, (state s commands n).request = .pending t →
    (∃ out, observe (state s commands n).sources t = some out) →
    ∃ m, n ≤ m ∧ commands m = .process

theorem session_step (s : State T α) (c : Command T α)
    (h : (step s c).2.status ≠ some .accepted) :
    (step s c).1 = (Engine.step s (project c)).1 ∧
    (step s c).2.response = (Engine.step s (project c)).2 := by
  cases c with
  | begin t =>
    cases s with | mk l r q =>
      cases q <;> simp_all [step,project,Engine.step,Engine.update,Engine.pack,
        Engine.MachineState.sources,Engine.Command.action,Demand.next,Demand.emit]
  | source r m => exact ⟨rfl,rfl⟩
  | process => exact ⟨rfl,rfl⟩
  | idle => exact ⟨rfl,rfl⟩

private theorem pending_initialized (s : State T α) (t : T) (h : s.request = .pending t) :
    s = (Engine.step (Engine.init s.sources) (.register t)).1 := by
  cases s with | mk l r q =>
    cases q <;> simp_all [Engine.step,Engine.init,Engine.pack,Engine.MachineState.sources,
      Engine.Command.action,Engine.update,Demand.next]

/-- Fair processing and finite closing prefixes imply delivery. Prefix length
zero is permitted: retained knowledge need not be delivered a second time. -/
theorem eventual_response (s : State T α) (commands : Nat → Command T α) (time : T)
    (pending : s.request = .pending time)
    (ms : Streams T α) (actions : Nat → Demand.Action T)
    (aligned : Engine.Aligned ms actions (sessionCommands time commands))
    (d : Delivery (Demand.sourceSchedule actions)) (fair : d.Fair)
    (processing : ProcessingFair s commands)
    (progress : ∀ source, ∃ k n, k ≤ d.available source n ∧
      time < (sourcePrefix (s.sources source) (ms source) k).frontier) :
    ∃ n out, (event s commands n).response = some (time,out) := by
  by_contra h
  have silent : ∀ n out, (event s commands n).response ≠ some (time,out) := by
    intro n out he; exact h ⟨n,out,he⟩
  have hp : ∀ n, (state s commands n).request = .pending time := by
    intro n; induction n with
    | zero => exact pending
    | succ n ih =>
      rcases no_lost_work _ _ time ih with hp | ⟨out,he⟩
      · exact hp
      · exact (silent n out he).elim
  have sim : ∀ n, state s commands n =
      Engine.state (Engine.init s.sources) (sessionCommands time commands) (n+1) := by
    intro n; induction n with
    | zero => exact pending_initialized s time pending
    | succ n ih =>
      have hs := (session_step (state s commands n) (commands n)
        (pending_no_accept _ _ time (hp n))).1
      change (step (state s commands n) (commands n)).1 =
        (Engine.step (Engine.state _ _ (n+1)) (project (commands n))).1
      rw [← ih]; exact hs
  have pf : Engine.ProcessingFair (Engine.init s.sources) (sessionCommands time commands) := by
    intro n t hp' ho
    cases n with
    | zero => simp [Engine.state,Engine.init,Engine.pack] at hp'
    | succ n =>
      obtain ⟨m,hm,hc⟩ := processing n t (by simpa [sim n] using hp') (by simpa [sim n] using ho)
      exact ⟨m+1,Nat.add_le_add_right hm 1,by simp [sessionCommands,hc,project]⟩
  obtain ⟨n,out,hn,he⟩ := Engine.eventual_response s.sources ms actions
    (sessionCommands time commands) aligned d fair pf time 1 (by rfl) progress
  cases n with
  | zero => omega
  | succ n =>
    apply silent n out
    change (step (state s commands n) (commands n)).2.response = _
    rw [(session_step _ _ (pending_no_accept _ _ time (hp n))).2]
    simpa [Engine.emission,sessionCommands,sim n] using he

end FRPSpec.Frontier.Exclusive
