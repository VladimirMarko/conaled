import Applications.FRP.Monitor
import Examples.FRPDemand

/-! Bounded verdicts over actual demand frames, with processing-clock boundaries. -/
namespace Examples.TemporalMonitor
open FRPSpec.Frontier FRPSpec.Frontier.Trace FRPSpec.Frontier.Demand
open FRPSpec.Frontier.Demand.Monitor
open Examples.FRPTrace Examples.FRPDemand
open _root_.Temporal.Monitor

abbrev Obs := Observation ℚ Nat

def earlyFrames (n : Nat) : Obs := frames start packets early 2 (n+1)
def arrives (h : Nat) : Formula Obs := .untilWithin h (pending 2) emitted

def check (p : Formula Obs) (x : Nat → Obs) (k : Nat) : Verdict :=
  verdict p (run p (initial p) (observePrefix x k))

example : check (arrives 4) earlyFrames 4 = .pending := by decide
example : check (arrives 4) earlyFrames 5 = .satisfied := by decide
example : check (arrives 3) earlyFrames 4 = .violated := by decide
example : check (arrives 4) earlyFrames 0 = .pending := by decide
example : (arrives 4).Sat earlyFrames 0 :=
  ((run_complete (arrives 4) (observePrefix earlyFrames 5) earlyFrames
    (prefix_observed _ _) (by decide)).1).mp (by decide)
example : ¬ (arrives 3).Sat earlyFrames 0 :=
  ((run_complete (arrives 3) (observePrefix earlyFrames 4) earlyFrames
    (prefix_observed _ _) (by decide)).2).mp (by decide)

/-- The terminal subformula contributes its own lookahead beyond the until bound. -/
example : check (.untilWithin 3 (pending 2) (.next emitted)) earlyFrames 4 = .pending := by decide
example : check (.untilWithin 3 (pending 2) (.next emitted)) earlyFrames 5 = .satisfied := by decide
example : check (arrives 0) (fun n => frames start packets late 2 (n+3)) 1 = .satisfied := by decide
example : check (arrives 0) earlyFrames 1 = .violated := by decide

/-- Unknown source knowledge is a decidable observation, not a claim of no event. -/
example : check (.not ready) earlyFrames 1 = .satisfied := by decide
example : (earlyFrames 0).observed = none ∧ truth .left 2 = [3,4,3] := by decide
example : check (.next ready) earlyFrames 2 = .violated := by decide
example : check (.and (pending 2) (.not emitted)) earlyFrames 1 = .satisfied := by decide

def emptyFrames (n : Nat) : Obs := frames start packets emptyQuery 1 (n+1)
example : check (answer 1 []) emptyFrames 1 = .satisfied := by decide
example : check (.next (answer 1 [])) emptyFrames 2 = .violated := by decide
example : check (.next ready) emptyFrames 2 = .satisfied := by decide

/-- Insert one idle processing position before the remaining early actions. -/
def paused (n : Nat) : Action ℚ :=
  if n < 2 then early n else if n = 2 then .idle else early (n-1)
def pausedFrames (n : Nat) : Obs := frames start packets paused 2 (n+1)
example : (frames start packets early 2 2).observed = (frames start packets paused 2 3).observed := by decide
example : check (arrives 4) pausedFrames 5 = .violated := by decide
example : check (arrives 5) pausedFrames 6 = .satisfied := by decide

/-- A rejected packet leaves knowledge unchanged but uses a processing position. -/
def rejected (n : Nat) : Action ℚ :=
  if n < 5 then early n else if n = 5 then .source .left else early (n-1)
def rejectedFrames (n : Nat) : Obs := frames start packets rejected 2 (n+1)
example : run start packets (sourceSchedule rejected) 5 =
    run start packets (sourceSchedule rejected) 6 := by
  funext source
  cases source <;> decide
example : check (arrives 4) rejectedFrames 5 = .violated := by decide
example : check (arrives 5) rejectedFrames 6 = .satisfied := by decide
example (n : Nat) (h : 5 ≤ n) : (frames start packets rejected 2 n).observed = some [3,4,3] :=
  observed_persists start packets rejected 2 h (by decide)

/-- Exact finite windows are preserved by concatenated processing and absorption. -/
example (xs ys : List Obs) :
    run (arrives 4) (initial _) (xs++ys) = run (arrives 4) (run (arrives 4) (initial _) xs) ys :=
  run_append _ _ _ _
example (x : Obs) : verdict (arrives 4)
    (step (arrives 4) (run (arrives 4) (initial _) (observePrefix earlyFrames 5)) x) = .satisfied := by
  rw [terminal_absorbing _ _ (by decide)]
  decide
example (xs : List Obs) : (run (arrives 4) (initial _) xs).val.length ≤ 5 := retention _ _ _
example (x : Nat → Obs) (same : ∀ j, j ≤ 4 → earlyFrames j = x j) : (arrives 4).Sat x 0 :=
  ((arrives 4).sat_prefix earlyFrames x 0 (by simpa [arrives, pending, emitted, Formula.horizon] using same)).mp
    (((run_complete (arrives 4) (observePrefix earlyFrames 5) earlyFrames
      (prefix_observed _ _) (by decide)).1).mp (by decide))

/-- Every silent finite prefix admits incompatible eventual futures. -/
example (k : Nat) : ∃ x y : Nat → Bool, observePrefix x k = observePrefix y k ∧
    (¬ ∃ n, x n = true) ∧ (∃ n, y n = true) := unbounded_undetermined k

/-- Future-reading specifications have complete solutions without causal implementations. -/
example : ∃ f : (Nat → Bool) → Nat → Bool, ∀ x n, f x n = x (n+1) := ⟨Progress.shift, fun _ _ => rfl⟩
theorem future_not_causal : ¬ ∃ f : (Nat → Bool) → Nat → Bool,
    _root_.Temporal.Synchronous f ∧ (∀ x n, f x n = x (n+1)) := by
  rintro ⟨f,hc,hf⟩
  have h := hc (fun _ => false) (fun n => decide (n ≠ 0)) 1 rfl
  simp [Progress.prefixOf, hf] at h

end Examples.TemporalMonitor
