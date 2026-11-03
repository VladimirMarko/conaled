import Applications.FRP.Trace
import Examples.FRPFrontier

/-! Rational-time cases for the experimental trace model. The first left packet
contains ordered fragments [3, 4, 3]; the right source certifies silence. -/
namespace Examples.FRPTrace
open FRPSpec.Frontier FRPSpec.Frontier.Trace

def start : Inputs ℚ Nat := fun _ => initial 2

def packets : Streams ℚ Nat
  | .left, 0 => ⟨3, [(2, [3, 4]), (2, [3])]⟩
  | .left, _ + 1 => ⟨4, [(2, [9])]⟩ -- rejected late packet
  | .right, _ => ⟨3, []⟩

def leftFirst : Schedule
  | 0 => some .left
  | 1 => some .left
  | 2 => some .right
  | _ => none

def rightFirst : Schedule
  | 0 => some .right
  | 1 => some .left
  | _ => none

example : observe (run start packets leftFirst 2) 2 = none := by decide
example : observe (run start packets rightFirst 2) 2 = some [3, 4, 3] := by decide

/-- Equal global step counts need not mean equal processed prefixes. -/
example : observe (run start packets leftFirst 2) 2 ≠
    observe (run start packets rightFirst 2) 2 := by decide

/-- Inserting an idle step changes global length, but not the consumed prefixes. -/
example : run start packets (fun n => if n = 0 then none else rightFirst (n - 1)) 3 =
    run start packets rightFirst 2 := by
  apply run_eq
  intro source
  cases source <;> decide

/-- The extra rejected packet cannot affect an already returned observation. -/
theorem ordered_interleavings {x y : List Nat}
    (hx : observe (run start packets leftFirst 3) 2 = some x)
    (hy : observe (run start packets rightFirst 2) 2 = some y) : x = y :=
  interleavings_agree start packets leftFirst rightFirst 3 2 hx hy

example : observe (run start packets leftFirst 3) 2 = some [3, 4, 3] := by
  obtain ⟨out, ho⟩ := (observe_ready (run start packets leftFirst 3) 2).mpr (by decide)
  have he := ordered_interleavings ho (show observe (run start packets rightFirst 2) 2 =
    some [3, 4, 3] from by decide)
  simpa [he] using ho

example : process (sourcePrefix (start .left) (packets .left) 1) (packets .left 1) =
    sourcePrefix (start .left) (packets .left) 1 := by decide

example (n : Nat) (h : 3 ≤ n) :
    observe (run start packets leftFirst n) 2 = some [3, 4, 3] :=
  run_persists start packets leftFirst h (by decide)

example (n : Nat) (source : Source) : (run start packets leftFirst n source).Valid :=
  run_valid (by intro source; simp [start, initial, State.Valid]) packets leftFirst n source

/-- At its frontier even the completed trace still returns unknown. -/
example : observe (run start packets leftFirst 3) 3 = none := by decide

/-- Only the first message of each stream is delivered. Later messages need not arrive. -/
def delivered : Delivery rightFirst where
  available _ _ := 1
  monotone _ _ _ _ := le_rfl
  legal n source h := by
    cases n with
    | zero => cases source <;> simp_all [rightFirst, count]
    | succ n =>
      cases n with
      | zero => cases source <;> simp_all [rightFirst, count]
      | succ n => simp [rightFirst] at h

theorem delivered_fair : delivered.Fair := by
  intro source n k hk
  refine ⟨max n 2, Nat.le_max_left _ _, ?_⟩
  have hc : 1 ≤ count rightFirst source 2 := by cases source <;> decide
  exact hk.trans (hc.trans (count_mono _ _ (Nat.le_max_right _ _)))

/-- A silent right source and ordered left duplicates satisfy progress. -/
example : ∃ n out, ∀ m, n ≤ m → observe (run start packets rightFirst m) 2 = some out := by
  apply eventual_observation start packets rightFirst delivered delivered_fair 2
  intro source
  refine ⟨1, 0, by exact le_rfl, ?_⟩
  cases source <;> decide

/-- Fair processing cannot make a source advance if every delivered window is empty
and ends at the initial frontier. -/
def stalled : Streams ℚ Nat := fun _ _ => ⟨2, []⟩

theorem stalled_prefix (source : Source) (n : Nat) :
    sourcePrefix (start source) (stalled source) n = initial 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sourcePrefix, ih, stalled, process, advance, windowValid, initial]

example (n : Nat) : observe (run start stalled rightFirst n) 2 = none := by
  simp [observe, run, stalled_prefix, observeMerge, initial]

/-- Conversely, available closing packets do not help a scheduler that always idles. -/
def idleDelivery : Delivery (fun _ => none) where
  available _ _ := 1
  monotone _ _ _ _ := le_rfl
  legal _ _ h := by cases h

theorem idle_count (source : Source) (n : Nat) : count (fun _ => none) source n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [count, ih]

example : ¬ idleDelivery.Fair := by
  intro h
  obtain ⟨m, _, hm⟩ := h .left 0 1 (by decide)
  simp [idle_count] at hm

example (n : Nat) : observe (run start packets (fun _ => none) n) 2 = none := by
  simp [observe, run, idle_count, sourcePrefix, start, observeMerge, initial]

def truth : Source → ℚ → List Nat
  | .left, t => if t = 2 then [3, 4, 3] else []
  | .right, _ => []

theorem left_prefix (n : Nat) : sourcePrefix (start .left) (packets .left) (n + 1) =
    ⟨3, [(2, [3, 4]), (2, [3])]⟩ := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [sourcePrefix, ih]
    change process (⟨3, [(2, [3, 4]), (2, [3])]⟩ : State ℚ Nat) ⟨4, [(2, [9])]⟩ = _
    decide

theorem packets_honest : ∀ source n, Honest (sourcePrefix (start source) (packets source) n)
    (packets source n) (truth source) := by
  intro source n hv t _ _
  cases source with
  | left =>
    cases n with
    | zero => by_cases h : t = 2 <;> simp [packets, batch, truth, eq_comm, h]
    | succ n =>
      have bad : ¬ windowValid (sourcePrefix (start .left) (packets .left) (n + 1))
          (packets .left (n + 1)).frontier (packets .left (n + 1)).packet := by
        rw [left_prefix]
        change ¬ windowValid (⟨3, [(2, [3, 4]), (2, [3])]⟩ : State ℚ Nat) 4 [(2, [9])]
        decide
      exact (bad hv).elim
  | right => rfl

/-- Nonempty honest traces connect their actual returned batch to external truth. -/
example : truth .left 2 ++ truth .right 2 = [3, 4, 3] := by
  have sound := run_sound packets rightFirst
    (s := start) (truth := truth)
    (by intro source; simp [start, initial, State.Valid])
    (by
      intro source t ht
      cases source with
      | left =>
        change t < (2 : ℚ) at ht
        simp [start, initial, batch, truth, ne_of_lt ht]
      | right => rfl)
    packets_honest 2
  exact (observeMerge_sound (l := run start packets rightFirst 2 .left)
    (r := run start packets rightFirst 2 .right) (t := 2) (out := [3, 4, 3])
    (by decide) _ _ (sound .left) (sound .right)).symm

/-- Trace safety composes with the existing mapped observation for any honest adapters. -/
example (s : Inputs ℚ Nat) (ms : Streams ℚ Nat) (schedule : Schedule) (n : Nat)
    (truth : Source → ℚ → List Nat) (h : (traceRep ms).Rel s truth)
    (out : List Nat)
    (ho : (observe (run s ms schedule n) 2).map (List.map (· + 1)) = some out) :
    out = (truth .left 2 ++ truth .right 2).map (· + 1) := by
  exact (Relational.compose (mappedMergeObservation (fun x : Nat => x + 1) (2 : ℚ))
    (executionSquare ms schedule n)).preserves h out ho

/-- Honest silent windows instantiate trace soundness without assuming the output. -/
example (n : Nat) (source : Source) :
    (run start stalled rightFirst n source).Completes (fun _ => []) := by
  apply run_sound stalled rightFirst
  · intro source; simp [start, initial, State.Valid]
  · intro source t _; rfl
  · intro source k _ t _ _
    rfl

example : (∃ out, observe (run start packets rightFirst 2) 2 = some out) := by
  apply (observe_ready _ _).mpr
  decide

/-- Future completions restrict to earlier states even without source honesty. -/
example (truth : ℚ → List Nat)
    (h : (sourcePrefix (start .left) (packets .left) 2).Completes truth) :
    (start .left).Completes truth :=
  (prefix_refines (start .left) (packets .left) (Nat.zero_le 2)).completion h

end Examples.FRPTrace
