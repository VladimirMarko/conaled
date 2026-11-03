import Applications.FRP.Demand
import Examples.FRPTrace

/-! Rational-time uses of atomic one-shot delivery. The ordered answer [3,4,3]
comes from the left packet; the advancing right source certifies silence. -/
namespace Examples.FRPDemand
open FRPSpec.Frontier FRPSpec.Frontier.Trace FRPSpec.Frontier.Demand
open Examples.FRPTrace

def early : Nat → Action ℚ
  | 0 => .register 2
  | 1 => .source .left
  | 2 => .process
  | 3 => .register 3 -- ignored duplicate
  | 4 => .source .right
  | 5 => .process
  | 6 => .source .left -- rejected late packet
  | _ => .process

def late : Nat → Action ℚ
  | 0 => .source .right
  | 1 => .source .left
  | 2 => .register 2
  | _ => .process

example : response start packets early 2 = none := by decide
example : request start packets early 4 = .pending 2 := by decide
example : response start packets early 5 = some (2, [3, 4, 3]) := by
  apply emit_iff.mpr
  exact ⟨rfl, by decide, by decide⟩

example : response start packets late 3 = some (2, [3, 4, 3]) := by
  apply emit_iff.mpr
  exact ⟨rfl, by decide, by decide⟩

example {x y : List Nat}
    (hx : response start packets early 5 = some (2, x))
    (hy : response start packets late 3 = some (2, y)) : x = y :=
  registration_order_agrees start packets early late 5 3 hx hy

example (n : Nat) (h : 5 < n) : response start packets early n = none :=
  at_most_once start packets early (t := 2) (out := [3,4,3]) h (by decide)

example : next (run start packets rightFirst 2) (.register 3) (.pending 2) = .pending 2 := by
  decide
example : next (run start packets rightFirst 2) (.register 2) .done = .done :=
  next_done _ _

example : emit (run start packets rightFirst 2) .process .absent = none := by decide
example : emit (run start packets rightFirst 2) .process (.pending 3) = none := by decide
example : emit (run start packets rightFirst 2) .process (.pending (1 : ℚ)) = some (1, []) := by
  apply process_ready
  decide

example : emit (run start packets rightFirst 2) .process
    (next (run start packets rightFirst 2) (.register 2) .absent) = some (2, [3, 4, 3]) :=
  register_ready _ _ _ (by decide)

/-- Closing both sources before registration supplies a nonvacuous progress witness. -/
def available : Delivery (sourceSchedule late) where
  available _ _ := 1
  monotone _ _ _ _ := le_rfl
  legal n source h := by
    cases n with
    | zero => cases source <;> simp_all [sourceSchedule, late, count]
    | succ n =>
      cases n with
      | zero => cases source <;> simp_all [sourceSchedule, late, count]
      | succ n => cases n <;> simp_all [sourceSchedule, late]

theorem available_fair : available.Fair := by
  intro source n k hk
  refine ⟨max n 2, Nat.le_max_left _ _, ?_⟩
  have hc : 1 ≤ count (sourceSchedule late) source 2 := by cases source <;> decide
  exact hk.trans (hc.trans (count_mono _ _ (Nat.le_max_right _ _)))

theorem processing_fair (ms : Streams ℚ Nat) : ProcessingFair start ms late := by
  intro n t _ _
  refine ⟨max n 3, Nat.le_max_left _ _, ?_⟩
  have h : 3 ≤ max n 3 := Nat.le_max_right _ _
  match he : max n 3 with
  | 0 | 1 | 2 => omega
  | k + 3 => rfl

example : ∃ n out, 3 ≤ n ∧ response start packets late n = some (2, out) := by
  apply eventual_response start packets late available available_fair (processing_fair packets) 2 3
  · decide
  · intro source
    refine ⟨1, 0, le_rfl, ?_⟩
    cases source <;> decide

/-- Fair processing of stalled sources never closes the timestamp. -/
example (n : Nat) : response start stalled late n = none := by
  unfold response emit
  split <;> try rfl
  rename_i t ha hq
  have ht : t = 2 := by
    obtain ⟨k, _, hk⟩ := pending_registered start stalled late hq
    cases k with
    | zero => simp [late] at hk
    | succ k =>
      cases k with
      | zero => simp [late] at hk
      | succ k => cases k <;> simp_all [late]
  subst t
  simp [observe, run, stalled_prefix, observeMerge, initial]

/-- Source progress and source fairness alone cannot schedule the consumer. -/
def starved : Nat → Action ℚ
  | 0 => .source .right
  | 1 => .source .left
  | 2 => .register 2
  | _ => .idle

theorem starved_no_process (n : Nat) : starved n ≠ .process := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n => cases n <;> simp [starved]

example (n : Nat) : response start packets starved n = none := by
  unfold response emit
  split <;> try rfl
  exact (starved_no_process n (by assumption)).elim

example : ¬ ProcessingFair start packets starved := by
  intro h
  obtain ⟨m, _, hm⟩ := h 3 2 (by decide) ⟨[3,4,3], by decide⟩
  exact starved_no_process m hm

example (n : Nat) {t : ℚ} {out : List Nat}
    (h : response start packets early n = some (t, out)) :
    ∃ k, k < n ∧ early k = .register t :=
  pending_registered start packets early (emit_iff.mp h).2.1

example (n : Nat) (h : 5 ≤ n) :
    (request start packets early n = .pending 2 ∧
      emit (run start packets (sourceSchedule early) n) .process (.pending 2) =
        some (2, [3,4,3])) ∨
    ∃ k xs, 5 ≤ k ∧ k < n ∧ response start packets early k = some (2, xs) :=
  enabled_persists_or_emitted start packets early h (by decide) (by decide)

/-- Both counterexamples retain the assumptions they are meant to distinguish. -/
example : ¬ (∀ source, ∃ k n, k ≤ available.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (stalled source) k).frontier) := by
  intro h
  obtain ⟨k, _, _, hk⟩ := h .left
  simp [stalled_prefix, initial] at hk

theorem starved_schedule : sourceSchedule starved = sourceSchedule late := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

def starvedAvailable : Delivery (sourceSchedule starved) where
  available _ _ := 1
  monotone _ _ _ _ := le_rfl
  legal n source h := by
    rw [starved_schedule] at h ⊢
    exact available.legal n source h

example : starvedAvailable.Fair := by
  intro source n k hk
  have hk' : k ≤ available.available source n := hk
  obtain ⟨m, hm, hc⟩ := available_fair source n k hk'
  exact ⟨m, hm, by simpa [starved_schedule] using hc⟩

example : ∀ source, ∃ k n, k ≤ starvedAvailable.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (packets source) k).frontier := by
  intro source
  refine ⟨1, 0, le_rfl, ?_⟩
  cases source <;> decide

/-- Known absence is emitted as an empty batch, then cannot be emitted again. -/
def emptyQuery : Nat → Action ℚ
  | 0 => .register 1
  | _ => .process

example : response start packets emptyQuery 1 = some (1, []) := by
  apply emit_iff.mpr
  exact ⟨rfl, rfl, by decide⟩

example (n : Nat) (h : 1 < n) : response start packets emptyQuery n = none :=
  at_most_once start packets emptyQuery (t := 1) (out := []) h (by decide)

/-- Delivery composes with a mapped consumer under the same honest-source relation. -/
example (s : Inputs ℚ Nat) (ms : Streams ℚ Nat) (actions : Nat → Action ℚ)
    (n : Nat) (truth : Source → ℚ → List Nat) (h : (traceRep ms).Rel s truth)
    (out : List Nat)
    (ho : (responseFor s ms actions n 2).map (List.map (· + 1)) = some out) :
    out = (truth .left 2 ++ truth .right 2).map (· + 1) :=
  (Relational.compose (mapObservation (fun x : Nat => x + 1))
    (responseSquare ms actions n 2)).preserves h out ho

/-- Every compatible completion, including futures not fixed by the packets, agrees. -/
example (left right : ℚ → List Nat)
    (hl : (run start packets (sourceSchedule early) 5 .left).Completes left)
    (hr : (run start packets (sourceSchedule early) 5 .right).Completes right) :
    [3,4,3] = left 2 ++ right 2 :=
  response_sound start packets early 5 (by decide) left right hl hr

end Examples.FRPDemand
