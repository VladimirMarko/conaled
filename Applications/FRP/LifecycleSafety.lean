import Applications.FRP.Lifecycle

/-! Global lifecycle invariants, including arbitrary later accepted sessions. -/
namespace FRPSpec.Frontier.Lifecycle
open Trace
variable {T α : Type} [LinearOrder T]

omit [LinearOrder T] in
theorem tag_eq_some (last : Option Nat) (out : Option (T × List α)) (r : Response T α) :
    tag last out = some r ↔ last = some r.id ∧ out = some (r.time,r.batch) := by
  cases last <;> cases out <;> cases r <;> simp [tag,Prod.ext_iff]

/-- Emission identifies both the matching command and the pre/post request cells. -/
theorem emitted {s : State T α} {c : Command T α} {r : Response T α}
    (h : (step s c).2.response = some r) :
    c = .process r.id ∧ s.last = some r.id ∧ s.engine.request = .pending r.time ∧
      observe s.engine.sources r.time = some r.batch ∧
      (step s c).1.last = some r.id ∧ (step s c).1.engine.request = .done := by
  cases c with
  | begin id t => simp [step] at h
  | source k m => simp [step,active,Engine.step,Engine.Command.action,Demand.emit,tag] at h
  | idle => simp [step,active,Engine.step,Engine.Command.action,Demand.emit,tag] at h
  | process k =>
    have ht := (tag_eq_some s.last _ r).mp h
    by_cases hm : s.last = some k
    · have hk : k = r.id := Option.some.inj (hm.symm.trans ht.1)
      subst k
      have he : Demand.emit s.engine.sources .process s.engine.request = some (r.time,r.batch) := by
        simpa [Engine.step,active,hm,Engine.Command.action] using ht.2
      have hp := Demand.emit_iff.mp he
      refine ⟨rfl,ht.1,hp.2.1,hp.2.2,ht.1,?_⟩
      simpa [step,active,hm,Engine.step,Engine.Command.action] using Demand.emit_done he
    · simp [Engine.step,active,hm,Engine.Command.action,Demand.emit] at ht

theorem response_sound {s : State T α} {c : Command T α} {r : Response T α}
    (h : (step s c).2.response = some r) (left right : T → List α)
    (hl : (s.engine.sources .left).Completes left)
    (hr : (s.engine.sources .right).Completes right) :
    r.batch = left r.time ++ right r.time :=
  observeMerge_sound (emitted h).2.2.2.1 left right hl hr

theorem pending_no_accept (s : State T α) (c : Command T α) (t : T)
    (h : s.engine.request = .pending t) : (step s c).2.status ≠ some .accepted := by
  cases c <;> simp [step,classify,h]

theorem no_lost_work (s : State T α) (c : Command T α) (id : Nat) (t : T)
    (hl : s.last = some id) (hq : s.engine.request = .pending t) :
    ((step s c).1.last = some id ∧ (step s c).1.engine.request = .pending t) ∨
      ∃ out, (step s c).2.response = some ⟨id,t,out⟩ := by
  obtain ⟨he,hm,hr⟩ := session_step s id c hl (pending_no_accept s c t hq)
  rcases Engine.no_lost_work s.engine (project id c) t hq with hp | ⟨out,ho⟩
  · exact .inl ⟨hm,by rw [he]; exact hp⟩
  · exact .inr ⟨out,by rw [hr,ho]; rfl⟩

/-- None is below every accepted ID; successor distinguishes accepted ID0. -/
def mark (s : State T α) : Nat := s.last.elim 0 Nat.succ

theorem step_mark (s : State T α) (c : Command T α) : mark s ≤ mark (step s c).1 := by
  rcases step_last (s := s) c with h | ⟨id,t,_,ha,hs⟩
  · simp [mark,h]
  · rw [hs]
    have hf := accepted_fresh ha
    cases hl : s.last <;> simp_all [mark,registered,Fresh]
    omega

theorem marks_monotone (s : State T α) (commands : Nat → Command T α) :
    Monotone (fun n => mark (state s commands n)) :=
  monotone_nat_of_le_succ (fun n => step_mark (state s commands n) (commands n))

/-- Every accepted begin is fresh relative to the previous accepted ID. -/
theorem accepted_increases (s : State T α) (id : Nat) (time : T) (old : Nat)
    (hl : s.last = some old) (ha : (step s (.begin id time)).2.status = some .accepted) :
    old < id := by
  have hc : classify s id = .accepted := by simpa [step] using ha
  simpa [Fresh,hl] using accepted_fresh hc

/-- After a response of IDk, later transitions keep k done or move strictly above
k. This invariant is closed even under accepted resets. -/
def Finished (id : Nat) (s : State T α) : Prop :=
  ∃ current, s.last = some current ∧ id ≤ current ∧
    (current = id → s.engine.request = .done)

theorem finished_step (id : Nat) (s : State T α) (c : Command T α) (h : Finished id s) :
    Finished id (step s c).1 := by
  obtain ⟨k,hk,hik,hd⟩ := h
  cases c with
  | begin j t =>
    by_cases ha : classify s j = .accepted
    · have hj : k < j := by simpa [Fresh,hk] using accepted_fresh ha
      refine ⟨j,by simp [step,ha,registered],by omega,?_⟩
      intro he; omega
    · simpa [step,ha] using (show Finished id s from ⟨k,hk,hik,hd⟩)
  | source r m =>
    refine ⟨k,hk,hik,?_⟩
    intro he
    simpa [step,Engine.step,hd he] using Demand.next_done s.engine.sources (active s.last (.source r m)).action
  | process j =>
    refine ⟨k,hk,hik,?_⟩
    intro he
    simpa [step,Engine.step,hd he] using Demand.next_done s.engine.sources (active s.last (.process j)).action
  | idle =>
    refine ⟨k,hk,hik,?_⟩
    intro he
    simpa [step,Engine.step,hd he] using Demand.next_done s.engine.sources (active s.last .idle).action

theorem finished_persists (s : State T α) (commands : Nat → Command T α)
    {i j : Nat} (hij : i ≤ j) {id : Nat} (h : Finished id (state s commands i)) :
    Finished id (state s commands j) := by
  induction j,hij using Nat.le_induction with
  | base => exact h
  | succ j hij ih => exact finished_step id _ _ ih

theorem at_most_once (s : State T α) (commands : Nat → Command T α) {i j : Nat}
    (hij : i < j) {r r' : Response T α}
    (hi : (event s commands i).response = some r)
    (hj : (event s commands j).response = some r') : r'.id ≠ r.id := by
  obtain ⟨_,_,_,_,hmark,hd⟩ := emitted hi
  have hf : Finished r.id (state s commands (i+1)) := ⟨r.id,hmark,le_rfl,fun _ => hd⟩
  obtain ⟨k,hk,_,hdone⟩ := finished_persists s commands hij hf
  have ej := emitted hj
  intro he
  have hki : k = r.id := by simpa [he] using Option.some.inj (hk.symm.trans ej.2.1)
  have := hdone hki
  rw [ej.2.2.1] at this
  contradiction

private theorem engine_pending_pre (s : Engine.MachineState T α) (c : Engine.Command T α)
    (t : T) (hc : ∀ u, c ≠ .register u)
    (h : (Engine.step s c).1.request = .pending t) : s.request = .pending t := by
  cases c <;> cases hq : s.request <;>
    simp_all [Engine.step,Engine.Command.action,Demand.next]
  split at h <;> simp_all

omit [LinearOrder T] in
private theorem active_not_register (last : Option Nat) (c : Command T α) (t : T) :
    active last c ≠ .register t := by
  cases c <;> simp [active]
  split <;> simp

theorem pending_pre_or_begin (s : State T α) (c : Command T α) (id : Nat) (t : T)
    (hl : (step s c).1.last = some id) (hq : (step s c).1.engine.request = .pending t) :
    (s.last = some id ∧ s.engine.request = .pending t) ∨
      (c = .begin id t ∧ (step s c).2.status = some .accepted) := by
  cases c with
  | begin k u =>
    by_cases ha : classify s k = .accepted
    · simp [step,ha,registered] at hl hq
      subst k; subst u
      exact .inr ⟨rfl,by simp [step,ha]⟩
    · exact .inl ⟨by simpa [step,ha] using hl,by simpa [step,ha] using hq⟩
  | source k m => exact .inl ⟨hl,engine_pending_pre _ _ t (active_not_register _ _) hq⟩
  | process k => exact .inl ⟨hl,engine_pending_pre _ _ t (active_not_register _ _) hq⟩
  | idle => exact .inl ⟨hl,engine_pending_pre _ _ t (active_not_register _ _) hq⟩

theorem pending_provenance (sources : Inputs T α) (commands : Nat → Command T α)
    (n : Nat) (id : Nat) (t : T) (hl : (state (init sources) commands n).last = some id)
    (hq : (state (init sources) commands n).engine.request = .pending t) :
    ∃ k, k < n ∧ commands k = .begin id t ∧
      (event (init sources) commands k).status = some .accepted := by
  induction n with
  | zero => simp [state,init] at hl
  | succ n ih =>
    rcases pending_pre_or_begin _ _ id t hl hq with ⟨hm,hp⟩ | ⟨hc,ha⟩
    · obtain ⟨k,hk,hc,ha⟩ := ih hm hp
      exact ⟨k,Nat.lt_succ_of_lt hk,hc,ha⟩
    · exact ⟨n,Nat.lt_succ_self _,hc,ha⟩

theorem response_provenance (sources : Inputs T α) (commands : Nat → Command T α)
    (n : Nat) (r : Response T α)
    (h : (event (init sources) commands n).response = some r) :
    ∃ k, k < n ∧ commands k = .begin r.id r.time ∧
      (event (init sources) commands k).status = some .accepted :=
  pending_provenance sources commands n r.id r.time (emitted h).2.1 (emitted h).2.2.1

theorem pending_or_emitted (s : State T α) (commands : Nat → Command T α)
    {i j : Nat} (hij : i ≤ j) (id : Nat) (t : T)
    (hl : (state s commands i).last = some id)
    (hq : (state s commands i).engine.request = .pending t) :
    ((state s commands j).last = some id ∧ (state s commands j).engine.request = .pending t) ∨
      ∃ k out, i ≤ k ∧ k < j ∧ (event s commands k).response = some ⟨id,t,out⟩ := by
  induction j,hij using Nat.le_induction with
  | base => exact .inl ⟨hl,hq⟩
  | succ j hij ih =>
    rcases ih with ⟨hm,hp⟩ | ⟨k,out,hik,hkj,he⟩
    · rcases no_lost_work (state s commands j) (commands j) id t hm hp with hn | ⟨out,he⟩
      · exact .inl hn
      · exact .inr ⟨j,out,hij,Nat.lt_succ_self _,he⟩
    · exact .inr ⟨k,out,hik,Nat.lt_succ_of_lt hkj,he⟩

theorem state_valid (s : State T α) (commands : Nat → Command T α)
    (h : s.engine.Valid) (n : Nat) : (state s commands n).engine.Valid := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_valid ih _

end FRPSpec.Frontier.Lifecycle
