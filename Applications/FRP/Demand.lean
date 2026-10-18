import Applications.FRP.Trace

/-! Experimental one-shot demand delivery (#30). Atomic actions retain a pending
request until a processing action emits its answer. Duplicate registrations are
ignored, including after delivery. See `docs/research/frp-demand.md`. -/
namespace FRPSpec.Frontier.Demand
open Trace
variable {T α : Type} [LinearOrder T]

inductive Action (T : Type)
  | register (time : T)
  | source (which : Source)
  | process
  | idle
  deriving DecidableEq, Repr

inductive Request (T : Type)
  | absent
  | pending (time : T)
  | done
  deriving DecidableEq, Repr

/-- Erasing consumer actions recovers the existing ordered source trace. -/
def sourceSchedule (actions : Nat → Action T) : Schedule := fun n =>
  match actions n with
  | .source source => some source
  | _ => none

/-- The returned option is an emission at this transition, not a stored answer. -/
def emit (s : Inputs T α) (a : Action T) (q : Request T) : Option (T × List α) :=
  match a, q with
  | .process, .pending t => (observe s t).map (t, ·)
  | _, _ => none

def next (s : Inputs T α) (a : Action T) (q : Request T) : Request T :=
  match q, a with
  | .absent, .register t => .pending t
  | .pending t, .process => if (observe s t).isSome then .done else .pending t
  | _, _ => q

/-- The request cell is the pending-work representation; source actions never clear it. -/
def request (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T) :
    Nat → Request T
  | 0 => .absent
  | n + 1 => next (run s ms (sourceSchedule actions) n) (actions n) (request s ms actions n)

def response (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T) (n : Nat) :=
  emit (run s ms (sourceSchedule actions) n) (actions n) (request s ms actions n)

theorem emit_iff {s : Inputs T α} {a : Action T} {q : Request T} {t : T} {out : List α} :
    emit s a q = some (t, out) ↔
      a = .process ∧ q = .pending t ∧ observe s t = some out := by
  cases a <;> cases q <;> simp [emit]
  rename_i u
  cases h : observe s u <;> simp_all
  · intro he; subst u; simp_all
  · constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, h⟩
    · rintro ⟨rfl, he⟩; simp_all

theorem next_done (s : Inputs T α) (a : Action T) : next s a .done = .done := by
  cases a <;> rfl

/-- Enabled work survives every non-emitting transition, including duplicate registration. -/
theorem no_lost_work (s : Inputs T α) (a : Action T) (t : T) :
    next s a (.pending t) = .pending t ∨
      ∃ out, emit s a (.pending t) = some (t, out) := by
  cases a <;> simp [next, emit]
  cases h : observe s t <;> simp

theorem emit_done {s : Inputs T α} {a : Action T} {q : Request T} {t : T} {out : List α}
    (h : emit s a q = some (t, out)) : next s a q = .done := by
  obtain ⟨rfl, rfl, ho⟩ := emit_iff.mp h
  simp [next, ho]

/-- Registration after readiness leaves work that the next processing step emits. -/
theorem register_ready (s : Inputs T α) (t : T) (out : List α)
    (h : observe s t = some out) :
    emit s .process (next s (.register t) .absent) = some (t, out) := by
  simp [next, emit, h]

/-- Readiness after registration also enables an actual emission transition. -/
theorem process_ready (s : Inputs T α) (t : T) (out : List α)
    (h : observe s t = some out) : emit s .process (.pending t) = some (t, out) := by
  simp [emit, h]

theorem done_persists (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    {i j : Nat} (hij : i ≤ j) (h : request s ms actions i = .done) :
    request s ms actions j = .done := by
  have hd : Monotone (fun n => request s ms actions n = .done) :=
    monotone_nat_of_le_succ (fun n hn => by simp [request, hn, next_done])
  exact hd hij h

theorem at_most_once (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    {i j : Nat} {t : T} {out : List α} (hij : i < j)
    (h : response s ms actions i = some (t, out)) : response s ms actions j = none := by
  have hd : request s ms actions (i + 1) = .done := emit_done h
  have hj := done_persists s ms actions hij hd
  simp [response, hj, emit]

/-- A pending request either remains stored or has emitted at an intervening step. -/
theorem pending_or_emitted (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    {i j : Nat} {t : T} (hij : i ≤ j) (h : request s ms actions i = .pending t) :
    request s ms actions j = .pending t ∨
      ∃ k out, i ≤ k ∧ k < j ∧ response s ms actions k = some (t, out) := by
  induction j, hij using Nat.le_induction with
  | base => exact Or.inl h
  | succ j hij ih =>
    rcases ih with hj | ⟨k, out, hk, hkj, he⟩
    · rcases no_lost_work (run s ms (sourceSchedule actions) j) (actions j) t with hn | ⟨out, he⟩
      · exact Or.inl (by simpa [request, hj] using hn)
      · exact Or.inr ⟨j, out, hij, Nat.lt_succ_self _, by simpa [response, hj] using he⟩
    · exact Or.inr ⟨k, out, hk, Nat.lt_succ_of_lt hkj, he⟩

/-- Ready work remains enabled at every later state unless its response has
already been emitted. Source updates cannot turn readiness off. -/
theorem enabled_persists_or_emitted (s : Inputs T α) (ms : Streams T α)
    (actions : Nat → Action T) {i j : Nat} {t : T} {out : List α}
    (hij : i ≤ j) (hq : request s ms actions i = .pending t)
    (ho : observe (run s ms (sourceSchedule actions) i) t = some out) :
    (request s ms actions j = .pending t ∧
      emit (run s ms (sourceSchedule actions) j) .process (.pending t) = some (t, out)) ∨
      ∃ k xs, i ≤ k ∧ k < j ∧ response s ms actions k = some (t, xs) := by
  rcases pending_or_emitted s ms actions hij hq with h | h
  · exact Or.inl ⟨h, process_ready _ _ _ (run_persists s ms _ hij ho)⟩
  · exact Or.inr h

/-- Emission requires a registration at a strictly earlier transition. -/
theorem pending_registered (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    {n : Nat} {t : T} (h : request s ms actions n = .pending t) :
    ∃ k, k < n ∧ actions k = .register t := by
  induction n with
  | zero => cases h
  | succ n ih =>
    simp only [request] at h
    cases hq : request s ms actions n with
    | absent =>
      cases ha : actions n <;> simp_all [next]
      exact ⟨n, le_rfl, ha⟩
    | pending u =>
      have hu : u = t := by
        cases ha : actions n <;> simp_all [next]
        split at h <;> simp_all
      subst u
      obtain ⟨k, hk, he⟩ := ih hq
      exact ⟨k, Nat.lt_succ_of_lt hk, he⟩
    | done => simp [hq, next_done] at h

theorem response_sound (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    (n : Nat) {t : T} {out : List α} (h : response s ms actions n = some (t, out)) :
    ∀ left right,
      (run s ms (sourceSchedule actions) n .left).Completes left →
      (run s ms (sourceSchedule actions) n .right).Completes right →
      out = left t ++ right t :=
  observeMerge_sound (emit_iff.mp h).2.2

/-- Select the emission for one timestamp, preserving known-empty answers. -/
def responseFor (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    (n : Nat) (t : T) : Option (List α) :=
  match response s ms actions n with
  | none => none
  | some (u, out) => if u = t then some out else none

theorem responseFor_iff (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    (n : Nat) (t : T) (out : List α) :
    responseFor s ms actions n t = some out ↔ response s ms actions n = some (t, out) := by
  unfold responseFor
  cases h : response s ms actions n with
  | none => simp
  | some p =>
    rcases p with ⟨u, xs⟩
    by_cases ht : u = t <;> simp [ht]

/-- The delivery observation retains the trace adapter obligations. Its semantic
side is the merged source batch; absence of an emission makes no progress claim. -/
def responseSquare (ms : Streams T α) (actions : Nat → Action T) (n : Nat) (t : T) :
    Relational.RelSquare (traceRep ms) (observationRep α) where
  impl s := responseFor s ms actions n t
  spec truth := truth .left t ++ truth .right t
  preserves := by
    intro s truth h out ho
    have he := (responseFor_iff s ms actions n t out).mp ho
    exact (Relational.compose (mergeObservation t)
      (executionSquare ms (sourceSchedule actions) n)).preserves h out (emit_iff.mp he).2.2

/-- Registration times and consumed prefix lengths may differ. -/
theorem registration_order_agrees (s : Inputs T α) (ms : Streams T α)
    (a b : Nat → Action T) (i j : Nat) {t : T} {x y : List α}
    (ha : response s ms a i = some (t, x)) (hb : response s ms b j = some (t, y)) : x = y :=
  interleavings_agree s ms (sourceSchedule a) (sourceSchedule b) i j
    (emit_iff.mp ha).2.2 (emit_iff.mp hb).2.2

/-- Enabled consumer work eventually receives a processing action. This assumption
mentions scheduling, not the existence of a response. -/
def ProcessingFair (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T) : Prop :=
  ∀ n t, request s ms actions n = .pending t →
    (∃ out, observe (run s ms (sourceSchedule actions) n) t = some out) →
    ∃ m, n ≤ m ∧ actions m = .process

/-- Available closing prefixes, fair source consumption, and fair enabled processing
suffice for an emission after a registered, unanswered request. Honesty is separate. -/
theorem eventual_response (s : Inputs T α) (ms : Streams T α) (actions : Nat → Action T)
    (d : Delivery (sourceSchedule actions)) (fair : d.Fair)
    (processing : ProcessingFair s ms actions) (t : T) (i : Nat)
    (registered : request s ms actions i = .pending t)
    (progress : ∀ source, ∃ k n, k ≤ d.available source n ∧
      t < (sourcePrefix (s source) (ms source) k).frontier) :
    ∃ n out, i ≤ n ∧ response s ms actions n = some (t, out) := by
  obtain ⟨r, out, hr⟩ := eventual_observation s ms (sourceSchedule actions) d fair t progress
  let j := max i r
  rcases pending_or_emitted s ms actions (Nat.le_max_left i r) registered with hj | ⟨k, xs, hk, _, he⟩
  · obtain ⟨m, hm, hp⟩ := processing j t hj ⟨out, hr j (Nat.le_max_right i r)⟩
    rcases pending_or_emitted s ms actions hm hj with hq | ⟨k, xs, hk, _, he⟩
    · exact ⟨m, out, (Nat.le_max_left i r).trans hm,
        emit_iff.mpr ⟨hp, hq, hr m ((Nat.le_max_right i r).trans hm)⟩⟩
    · exact ⟨k, xs, (Nat.le_max_left i r).trans hk, he⟩
  · exact ⟨k, xs, hk, he⟩

end FRPSpec.Frontier.Demand
