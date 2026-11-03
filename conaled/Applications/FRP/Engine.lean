import Applications.FRP.Demand

/-! Experimental incremental implementation of the one-shot demand protocol.
Commands carry packets directly; reference streams occur only in refinement
statements. See `docs/research/frp-engine.md`. -/
namespace FRPSpec.Frontier.Engine
open Trace
variable {T α : Type} [LinearOrder T]

structure MachineState (T α : Type) where
  left : State T α
  right : State T α
  request : Demand.Request T
  deriving DecidableEq, Repr

def MachineState.sources (s : MachineState T α) : Inputs T α
  | .left => s.left
  | .right => s.right

/-- Evaluate the two source projections once when constructing retained state. -/
def pack (sources : Inputs T α) (request : Demand.Request T) : MachineState T α :=
  ⟨sources .left, sources .right, request⟩

omit [LinearOrder T] in
@[simp] theorem sources_pack (sources : Inputs T α) (request : Demand.Request T) :
    (pack sources request).sources = sources := by
  funext r; cases r <;> rfl

omit [LinearOrder T] in
@[simp] theorem pack_request (sources : Inputs T α) (request : Demand.Request T) :
    (pack sources request).request = request := rfl

inductive Command (T α : Type)
  | register (time : T)
  | source (which : Source) (message : Message T α)
  | process
  | idle
  deriving DecidableEq, Repr

def Command.action : Command T α → Demand.Action T
  | .register t => .register t
  | .source r _ => .source r
  | .process => .process
  | .idle => .idle

def init (s : Inputs T α) : MachineState T α := pack s .absent

/-- Only the packet's selected source changes. Rejected packets stutter. -/
def update (s : Inputs T α) : Command T α → Inputs T α
  | .source r m => fun k => if k = r then Trace.process (s k) m else s k
  | _ => s

/-- Emission and the request transition both use the pre-command state. -/
def step (s : MachineState T α) (c : Command T α) :
    MachineState T α × Option (T × List α) :=
  (pack (update s.sources c) (Demand.next s.sources c.action s.request),
    Demand.emit s.sources c.action s.request)

/-- One event position per command, including silent transitions. -/
def run (s : MachineState T α) : List (Command T α) →
    MachineState T α × List (Option (T × List α))
  | [] => (s, [])
  | c :: cs =>
    let (s', out) := step s c
    let (s'', outs) := run s' cs
    (s'', out :: outs)

def MachineState.Valid (s : MachineState T α) : Prop := ∀ r, (s.sources r).Valid

theorem init_valid {s : Inputs T α} (h : ∀ r, (s r).Valid) :
    (init s).Valid := by
  simpa [MachineState.Valid, init] using h

/-- Initial absence is a conditional assertion about the source, not a fact
about every possible completion. -/
theorem initial_completes (w : T) (truth : T → List α)
    (h : ∀ t, t < w → truth t = []) : (initial w).Completes truth := by
  intro t ht
  simpa [initial, batch] using (h t ht).symm

theorem step_valid {s : MachineState T α} (h : s.Valid) (c : Command T α) :
    (step s c).1.Valid := by
  change ∀ r, ((pack (update s.sources c) _).sources r).Valid
  rw [sources_pack]
  intro r
  cases c with
  | source k m =>
    change (if r = k then Trace.process (s.sources r) m else s.sources r).Valid
    split
    · exact process_valid (h r) m
    · exact h r
  | register t => exact h r
  | process => exact h r
  | idle => exact h r

theorem run_valid {s : MachineState T α} (h : s.Valid) (cs : List (Command T α)) :
    (run s cs).1.Valid := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih (step_valid h c)

/-- Proof-only reference state at the boundary before action n. -/
def reference (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T)
    (n : Nat) : MachineState T α :=
  pack (Trace.run s ms (Demand.sourceSchedule a) n) (Demand.request s ms a n)

/-- The cursor counts consumed messages, including rejected ones. -/
def commandAt (ms : Streams T α) (a : Nat → Demand.Action T) (n : Nat) : Command T α :=
  match a n with
  | .register t => .register t
  | .source r => .source r (ms r (count (Demand.sourceSchedule a) r n))
  | .process => .process
  | .idle => .idle

omit [LinearOrder T] in
@[simp] theorem commandAt_action (ms : Streams T α) (a : Nat → Demand.Action T) (n : Nat) :
    (commandAt ms a n).action = a n := by
  unfold commandAt
  cases a n <;> rfl

@[simp] theorem reference_zero (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T) :
    reference s ms a 0 = init s := rfl

theorem step_refines (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T) (n : Nat) :
    step (reference s ms a n) (commandAt ms a n) =
      (reference s ms a (n + 1), Demand.response s ms a n) := by
  have hs : update (Trace.run s ms (Demand.sourceSchedule a) n) (commandAt ms a n) =
      Trace.run s ms (Demand.sourceSchedule a) (n + 1) := by
    funext r
    rw [Trace.run_step]
    unfold commandAt
    cases h : a n <;> simp [update, Demand.sourceSchedule, h, eq_comm]
    split <;> simp_all
  simp [step, reference, Demand.request, Demand.response, hs]

/-- Finite alignment constrains commands and packets only, never their outputs. -/
def Corresponds (ms : Streams T α) (a : Nat → Demand.Action T) :
    Nat → List (Command T α) → Prop
  | _, [] => True
  | n, c :: cs => c = commandAt ms a n ∧ Corresponds ms a (n + 1) cs

def referenceEvents (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T) :
    Nat → Nat → List (Option (T × List α))
  | _, 0 => []
  | n, k + 1 => Demand.response s ms a n :: referenceEvents s ms a (n + 1) k

theorem run_refines (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T)
    (cs : List (Command T α)) (n : Nat) (h : Corresponds ms a n cs) :
    run (reference s ms a n) cs =
      (reference s ms a (n + cs.length), referenceEvents s ms a n cs.length) := by
  induction cs generalizing n with
  | nil => simp [run, referenceEvents]
  | cons c cs ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [run, step_refines]
    rw [ih (n + 1) h]
    simp only [List.length_cons, referenceEvents]
    congr 2; omega

/-- Retained-state iteration for infinite-execution theorems. The finite API
above does not require a caller to supply such a stream. -/
def state (s : MachineState T α) (commands : Nat → Command T α) : Nat → MachineState T α
  | 0 => s
  | n + 1 => (step (state s commands n) (commands n)).1

def emission (s : MachineState T α) (commands : Nat → Command T α) (n : Nat) :=
  (step (state s commands n) (commands n)).2

def Aligned (ms : Streams T α) (a : Nat → Demand.Action T) (commands : Nat → Command T α) : Prop :=
  ∀ n, commands n = commandAt ms a n

theorem state_refines (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T)
    (commands : Nat → Command T α) (h : Aligned ms a commands) (n : Nat) :
    state (init s) commands n = reference s ms a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [state, ih, h n, step_refines]

theorem emission_refines (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T)
    (commands : Nat → Command T α) (h : Aligned ms a commands) (n : Nat) :
    emission (init s) commands n = Demand.response s ms a n := by
  unfold emission
  rw [state_refines s ms a commands h n, h n, step_refines]

/-- Enabled work remains pending unless this very transition emits. -/
theorem no_lost_work (s : MachineState T α) (c : Command T α) (t : T)
    (h : s.request = .pending t) :
    (step s c).1.request = .pending t ∨ ∃ out, (step s c).2 = some (t, out) := by
  simpa [step, h] using Demand.no_lost_work s.sources c.action t

/-- Fairness mentions enabled state and scheduled commands, not eventual output. -/
def ProcessingFair (s : MachineState T α) (commands : Nat → Command T α) : Prop :=
  ∀ n t, (state s commands n).request = .pending t →
    (∃ out, observe (state s commands n).sources t = some out) →
    ∃ m, n ≤ m ∧ commands m = .process

section Transfer
variable (s : Inputs T α) (ms : Streams T α) (a : Nat → Demand.Action T)
  (commands : Nat → Command T α) (aligned : Aligned ms a commands)
include aligned

/-- Quantifies over every completion of the current source knowledge. Validation
alone does not assert that an external source is one of these completions. -/
theorem response_sound (n : Nat) {t : T} {out : List α}
    (h : emission (init s) commands n = some (t, out)) :
    ∀ left right,
      ((state (init s) commands n).sources .left).Completes left →
      ((state (init s) commands n).sources .right).Completes right →
      out = left t ++ right t := by
  rw [emission_refines s ms a commands aligned] at h
  simpa [state_refines s ms a commands aligned, reference] using
    Demand.response_sound s ms a n h

/-- Initial completion and honest accepted windows connect output to an external
truth through the existing relational square. -/
theorem response_honest (truth : Source → T → List α)
    (honest : (traceRep ms).Rel s truth) (n : Nat) {t : T} {out : List α}
    (h : emission (init s) commands n = some (t, out)) :
    out = truth .left t ++ truth .right t := by
  have hr := (emission_refines s ms a commands aligned n).symm.trans h
  exact (Demand.responseSquare ms a n t).preserves honest out
    ((Demand.responseFor_iff s ms a n t out).mpr hr)

theorem registration_order_agrees (b : Nat → Demand.Action T)
    (other : Nat → Command T α) (ho : Aligned ms b other) (i j : Nat)
    {t : T} {x y : List α}
    (hx : emission (init s) commands i = some (t, x))
    (hy : emission (init s) other j = some (t, y)) : x = y := by
  rw [emission_refines s ms a commands aligned] at hx
  rw [emission_refines s ms b other ho] at hy
  exact Demand.registration_order_agrees s ms a b i j hx hy

theorem pending_or_emitted {i j : Nat} {t : T} (hij : i ≤ j)
    (h : (state (init s) commands i).request = .pending t) :
    (state (init s) commands j).request = .pending t ∨
      ∃ k out, i ≤ k ∧ k < j ∧ emission (init s) commands k = some (t, out) := by
  simpa only [state_refines s ms a commands aligned, reference, pack_request,
    emission_refines s ms a commands aligned] using
    Demand.pending_or_emitted s ms a hij
      (by simpa [state_refines s ms a commands aligned, reference] using h)

theorem response_registered (n : Nat) {t : T} {out : List α}
    (h : emission (init s) commands n = some (t, out)) :
    ∃ k, k < n ∧ commands k = .register t := by
  rw [emission_refines s ms a commands aligned] at h
  obtain ⟨k, hk, ha⟩ := Demand.pending_registered s ms a (Demand.emit_iff.mp h).2.1
  exact ⟨k, hk, by rw [aligned k]; simp [commandAt, ha]⟩

theorem at_most_once {i j : Nat} {t : T} {out : List α} (hij : i < j)
    (h : emission (init s) commands i = some (t, out)) :
    emission (init s) commands j = none := by
  rw [emission_refines s ms a commands aligned] at h ⊢
  exact Demand.at_most_once s ms a hij h

theorem processing_fair_refines (h : ProcessingFair (init s) commands) :
    Demand.ProcessingFair s ms a := by
  intro n t hq he
  obtain ⟨m, hm, hc⟩ := h n t
    (by simpa [state_refines s ms a commands aligned, reference] using hq)
    (by simpa [state_refines s ms a commands aligned, reference] using he)
  refine ⟨m, hm, ?_⟩
  calc
    a m = (commands m).action := by rw [aligned m, commandAt_action]
    _ = .process := by rw [hc]; rfl

/-- Command fairness induces reference fairness. Source availability, fair
consumption and advancing prefixes remain explicit environmental obligations. -/
theorem eventual_response (d : Delivery (Demand.sourceSchedule a)) (fair : d.Fair)
    (processing : ProcessingFair (init s) commands) (t : T) (i : Nat)
    (registered : (state (init s) commands i).request = .pending t)
    (progress : ∀ source, ∃ k n, k ≤ d.available source n ∧
      t < (sourcePrefix (s source) (ms source) k).frontier) :
    ∃ n out, i ≤ n ∧ emission (init s) commands n = some (t, out) := by
  obtain ⟨n, out, hi, he⟩ := Demand.eventual_response s ms a d fair
    (processing_fair_refines s ms a commands aligned processing) t i
    (by simpa [state_refines s ms a commands aligned, reference] using registered) progress
  exact ⟨n, out, hi, (emission_refines s ms a commands aligned n).trans he⟩
end Transfer

end FRPSpec.Frontier.Engine
