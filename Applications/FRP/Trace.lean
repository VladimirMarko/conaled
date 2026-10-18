import Applications.FRP.Frontier

/-! Experimental two-source traces (#29). Rejections consume a message but leave
its source state unchanged. Scheduling preserves each source's stream order.
See `docs/research/frp-traces.md` for progress assumptions and statement review. -/
namespace FRPSpec.Frontier.Trace
variable {T α : Type} [LinearOrder T]

structure Message (T α : Type) where
  frontier : T
  packet : Log T α
  deriving DecidableEq, Repr

/-- The acceptance result remains available through `advance`; rejection stutters. -/
def process (s : State T α) (m : Message T α) : State T α :=
  (advance s m.frontier m.packet).getD s

/-- Knowledge order, independent of validity and source honesty. -/
def Refines (s q : State T α) : Prop :=
  s.frontier ≤ q.frontier ∧ ∀ t, t < s.frontier → batch q.log t = batch s.log t

theorem Refines.refl (s : State T α) : Refines s s := ⟨le_rfl, fun _ _ => rfl⟩
theorem Refines.trans {s q r : State T α} (h : Refines s q) (k : Refines q r) :
    Refines s r :=
  ⟨h.1.trans k.1, fun t ht => (k.2 t (lt_of_lt_of_le ht h.1)).trans (h.2 t ht)⟩

/-- Expose knowledge refinement to Mathlib's generic relation-preservation results. -/
instance : Std.Refl (Refines (T := T) (α := α)) := ⟨Refines.refl⟩
instance : IsTrans (State T α) Refines := ⟨fun _ _ _ => Refines.trans⟩

theorem process_refines (s : State T α) (m : Message T α) : Refines s (process s m) := by
  unfold process
  cases h : advance s m.frontier m.packet with
  | none => exact Refines.refl s
  | some q => exact advance_refines h

theorem process_valid {s : State T α} (hs : s.Valid) (m : Message T α) :
    (process s m).Valid := by
  unfold process
  cases h : advance s m.frontier m.packet with
  | none => exact hs
  | some q => exact advance_valid hs h

theorem Refines.completion {s q : State T α} (h : Refines s q)
    {truth : T → List α} (hq : q.Completes truth) : s.Completes truth := by
  intro t ht
  exact (h.2 t ht).symm.trans (hq t (lt_of_lt_of_le ht h.1))

/-- Honesty is required only for accepted windows, and includes omitted times. -/
def Honest (s : State T α) (m : Message T α) (truth : T → List α) : Prop :=
  windowValid s m.frontier m.packet →
    ∀ t, s.frontier ≤ t → t < m.frontier → batch m.packet t = truth t

theorem process_sound {s : State T α} {truth : T → List α} (m : Message T α)
    (hs : s.Valid) (old : s.Completes truth) (fresh : Honest s m truth) :
    (process s m).Completes truth := by
  unfold process advance
  split
  next hw => exact advance_sound hs old (by simp [advance, hw]) (fresh hw)
  next => exact old

/-- Canonical state after consuming a prefix of one ordered stream. -/
def sourcePrefix (s : State T α) (messages : Nat → Message T α) : Nat → State T α
  | 0 => s
  | n + 1 => process (sourcePrefix s messages n) (messages n)

theorem prefix_valid {s : State T α} (hs : s.Valid) (messages : Nat → Message T α)
    (n : Nat) : (sourcePrefix s messages n).Valid := by
  induction n with
  | zero => exact hs
  | succ n ih => exact process_valid ih _

theorem prefix_refines (s : State T α) (messages : Nat → Message T α)
    {i j : Nat} (h : i ≤ j) : Refines (sourcePrefix s messages i) (sourcePrefix s messages j) := by
  exact Nat.rel_of_forall_rel_succ_of_le Refines
    (fun n => process_refines (sourcePrefix s messages n) (messages n)) h

theorem prefix_sound {s : State T α} {truth : T → List α}
    (messages : Nat → Message T α) (hs : s.Valid) (old : s.Completes truth)
    (honest : ∀ n, Honest (sourcePrefix s messages n) (messages n) truth) (n : Nat) :
    (sourcePrefix s messages n).Completes truth := by
  induction n with
  | zero => exact old
  | succ n ih => exact process_sound _ (prefix_valid hs messages n) ih (honest n)

inductive Source | left | right deriving DecidableEq, Repr
abbrev Inputs (T α : Type) := Source → State T α
abbrev Streams (T α : Type) := Source → Nat → Message T α
abbrev Schedule := Nat → Option Source

/-- Number of messages consumed from this source before global step n. -/
def count (schedule : Schedule) (source : Source) : Nat → Nat
  | 0 => 0
  | n + 1 => count schedule source n + if schedule n = some source then 1 else 0

theorem count_mono (schedule : Schedule) (source : Source) :
    Monotone (count schedule source) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [count]
  omega

/-- Pure state at a global step, factored through the consumed source prefixes. -/
def run (s : Inputs T α) (messages : Streams T α) (schedule : Schedule) (n : Nat) :
    Inputs T α := fun source => sourcePrefix (s source) (messages source) (count schedule source n)

theorem run_step (s : Inputs T α) (messages : Streams T α) (schedule : Schedule)
    (n : Nat) (source : Source) :
    run s messages schedule (n + 1) source =
      if schedule n = some source then
        process (run s messages schedule n source) (messages source (count schedule source n))
      else run s messages schedule n source := by
  by_cases h : schedule n = some source <;> simp [run, count, h, sourcePrefix]

theorem run_valid {s : Inputs T α} (hs : ∀ source, (s source).Valid)
    (messages : Streams T α) (schedule : Schedule) (n : Nat) (source : Source) :
    (run s messages schedule n source).Valid := prefix_valid (hs source) _ _

theorem run_sound {s : Inputs T α} {truth : Source → T → List α}
    (messages : Streams T α) (schedule : Schedule)
    (hs : ∀ source, (s source).Valid) (old : ∀ source, (s source).Completes (truth source))
    (honest : ∀ source n, Honest (sourcePrefix (s source) (messages source) n)
      (messages source n) (truth source)) (n : Nat) (source : Source) :
    (run s messages schedule n source).Completes (truth source) :=
  prefix_sound _ (hs source) (old source) (honest source) _

def observe (s : Inputs T α) (t : T) := observeMerge (s .left) (s .right) t

theorem observe_ready (s : Inputs T α) (t : T) :
    (∃ out, observe s t = some out) ↔ t < (s .left).frontier ∧ t < (s .right).frontier := by
  unfold observe observeMerge
  split <;> simp_all

theorem observe_persists {s q : Inputs T α} (h : ∀ source, Refines (s source) (q source))
    {t : T} {out : List α} (ho : observe s t = some out) : observe q t = some out := by
  unfold observe observeMerge at *
  split at ho
  next ht =>
    rw [ite_eq_left ⟨lt_of_lt_of_le ht.1 (h .left).1, lt_of_lt_of_le ht.2 (h .right).1⟩,
      (h .left).2 t ht.1, (h .right).2 t ht.2]
    exact ho
  next => simp at ho

theorem run_persists (s : Inputs T α) (messages : Streams T α) (schedule : Schedule)
    {i j : Nat} (h : i ≤ j) {t : T} {out : List α}
    (ho : observe (run s messages schedule i) t = some out) :
    observe (run s messages schedule j) t = some out :=
  observe_persists (fun source => prefix_refines _ _ (count_mono _ source h)) ho

/-- Different global lengths are permitted; identical consumed prefixes give identical states. -/
theorem run_eq (s : Inputs T α) (messages : Streams T α) (a b : Schedule) (i j : Nat)
    (h : ∀ source, count a source i = count b source j) :
    run s messages a i = run s messages b j := by
  funext source
  simp only [run, h source]

/-- Even different prefix lengths agree once both executions return a result.
No shared-truth or honesty assumption is needed for the same streams. -/
theorem interleavings_agree (s : Inputs T α) (messages : Streams T α)
    (a b : Schedule) (i j : Nat) {t : T} {x y : List α}
    (ha : observe (run s messages a i) t = some x)
    (hb : observe (run s messages b j) t = some y) : x = y := by
  let q : Inputs T α := fun source => sourcePrefix (s source) (messages source)
    (max (count a source i) (count b source j))
  have hx : observe q t = some x := observe_persists
    (fun source => prefix_refines _ _ (Nat.le_max_left _ _)) ha
  have hy : observe q t = some y := observe_persists
    (fun source => prefix_refines _ _ (Nat.le_max_right _ _)) hb
  exact Option.some.inj (hx.symm.trans hy)

/-- Available messages form a monotonically growing prefix at each source.
A legal step consumes only an already available message. -/
structure Delivery (schedule : Schedule) where
  available : Source → Nat → Nat
  monotone : ∀ source, Monotone (available source)
  legal : ∀ n source, schedule n = some source → count schedule source n < available source n

/-- Every available finite prefix is eventually processed, even after an arbitrary step.
This speaks only about message counts, not observations or frontiers. -/
def Delivery.Fair {schedule : Schedule} (d : Delivery schedule) : Prop :=
  ∀ source n k, k ≤ d.available source n →
    ∃ m, n ≤ m ∧ k ≤ count schedule source m

/-- Source progress supplies a finite closing prefix that becomes available.
Fair processing then yields an observation which persists at every later step. -/
theorem eventual_observation (s : Inputs T α) (messages : Streams T α)
    (schedule : Schedule) (d : Delivery schedule) (fair : d.Fair) (t : T)
    (progress : ∀ source, ∃ k n, k ≤ d.available source n ∧
      t < (sourcePrefix (s source) (messages source) k).frontier) :
    ∃ n out, ∀ m, n ≤ m → observe (run s messages schedule m) t = some out := by
  have ready : ∀ source, ∃ n, t < (run s messages schedule n source).frontier := by
    intro source
    obtain ⟨k, n, hk, ht⟩ := progress source
    obtain ⟨m, _, hm⟩ := fair source n k hk
    exact ⟨m, lt_of_lt_of_le ht (prefix_refines _ _ hm).1⟩
  obtain ⟨l, hl⟩ := ready .left
  obtain ⟨r, hr⟩ := ready .right
  let n := max l r
  have hl' := lt_of_lt_of_le hl
    (prefix_refines (s .left) (messages .left) (count_mono schedule .left (Nat.le_max_left l r))).1
  have hr' := lt_of_lt_of_le hr
    (prefix_refines (s .right) (messages .right) (count_mono schedule .right (Nat.le_max_right l r))).1
  have ho : ∃ out, observe (run s messages schedule n) t = some out := by
    unfold observe observeMerge
    rw [ite_eq_left ⟨hl', hr'⟩]
    exact ⟨_, rfl⟩
  obtain ⟨out, ho⟩ := ho
  exact ⟨n, out, fun m hm => run_persists s messages schedule hm ho⟩

/-- Initial states carry the adapter obligations for the fixed streams. -/
def traceRep (messages : Streams T α) : Relational.RelRep where
  R := Inputs T α
  S := Source → T → List α
  Rel s truth := (∀ source, (s source).Valid) ∧
    (∀ source, (s source).Completes (truth source)) ∧
    ∀ source n, Honest (sourcePrefix (s source) (messages source) n)
      (messages source n) (truth source)

/-- Trace safety feeds the existing merge and mapped-consumer squares. -/
def executionSquare (messages : Streams T α) (schedule : Schedule) (n : Nat) :
    Relational.RelSquare (traceRep messages)
      (Relational.product (sourceRep T α) (sourceRep T α)) where
  impl s := (run s messages schedule n .left, run s messages schedule n .right)
  spec truth := (truth .left, truth .right)
  preserves h := ⟨run_sound messages schedule h.1 h.2.1 h.2.2 n .left,
    run_sound messages schedule h.1 h.2.1 h.2.2 n .right⟩

end FRPSpec.Frontier.Trace
