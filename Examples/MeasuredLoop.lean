import Applications.Resources.MeasuredLoop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Two finite-loop clients with independently specified finite sums. The native
and compiled routes use the same arithmetic graph and declared tariff. -/
namespace Examples.MeasuredLoop
open Resources Resources.MeasuredLoop FirstOrderCompiler Iteration
open scoped BigOperators

abbrev State := Nat × (Nat × Nat)
private abbrev ST : Ty := .prod .base (.prod .base .base)
private abbrev IN : Ty := .prod .base .base

/-- An independent prefix sum, selecting exactly counters above the threshold. -/
def visited (w : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => visited w t n + if t < n+1 then w (n+1) else 0

theorem visited_sum (w : Nat → Nat) (t n : Nat) :
    visited w t n = ∑ i ∈ Finset.range n, if t < i+1 then w (i+1) else 0 := by
  induction n with
  | zero => simp [visited]
  | succ n ih => simp [visited, Finset.sum_range_succ, ih]

theorem visited_zero (w : Nat → Nat) (t n : Nat) (h : n ≤ t) : visited w t n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [visited, ih (by omega), show ¬t < n+1 by omega]

def done (s : State) : Bool := decide (s.1 ≤ s.2.2)
def step (w : Nat → Nat) (s : State) : State := (s.1-1, (s.2.1+w s.1, s.2.2))

theorem decreases (w : Nat → Nat) (s : State) (h : done s = false) :
    (step w s).1 < s.1 := by
  simp only [done, decide_eq_false_iff_not] at h
  simp only [step]
  omega

/-- Source correctness and the number of continuing transitions are established
without referring to syntax, compilation, or the measured runner. -/
theorem source_steps (w : Nat → Nat) (n a t : Nat) :
    Steps done (step w) (n-t) (n,(a,t)) (min n t,(a+visited w t n,t)) := by
  induction n generalizing a with
  | zero => simpa [visited] using (Steps.stop (p := done) (f := step w) (x := (0,(a,t))) rfl)
  | succ n ih =>
    by_cases h : n+1 ≤ t
    · simpa [Nat.min_eq_left h, visited_zero w t (n+1) h, Nat.sub_eq_zero_of_le h] using
        (Steps.stop (p := done) (f := step w) (x := (n+1,(a,t))) (by simp [done, h]))
    · have ht : t ≤ n := by omega
      have hp : done (n+1,(a,t)) = false := by simp [done, h]
      have hs := Steps.step hp (ih (a+w (n+1)))
      have hn : n+1-t = (n-t)+1 := by omega
      simpa [step, hn, visited, show t < n+1 by omega, Nat.min_eq_right ht,
        Nat.min_eq_right (by omega : t ≤ n+1), Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs

/-- One comparison plus one control visit per guard; three arithmetic primitives
per continuing body (weight, addition, decrement). Wiring is uncharged. -/
def nativeGuard (s : State) : Measured Bool Nat := (done s,1)
def nativeBody (w : Nat → Nat) (s : State) : Measured State Nat :=
  Resources.bind (s.1-1,1) fun n =>
  Resources.bind (w s.1,1) fun weight =>
  Resources.bind (s.2.1+weight,1) fun a => Resources.pure (n,(a,s.2.2))
def native (w : Nat → Nat) (setup : Nat) (s : State) : Measured State Nat :=
  bind (s,setup) fun initial =>
  bind (run nativeGuard (nativeBody w) Prod.fst (decreases w) initial) pure

theorem native_result (w : Nat → Nat) (setup n a t : Nat) :
    native w setup (n,(a,t)) =
      ((min n t,(a+visited w t n,t)), setup+(n-t+1)*2+(n-t)*3) := by
  have h := run_of_steps nativeGuard (nativeBody w) Prod.fst (decreases w) 1 3
    (fun _ => rfl) (fun _ => rfl) (source_steps w n a t)
  simp [native, Resources.bind, Resources.pure, h, Nat.add_assoc]

inductive Prim : Ty → Ty → Type
  | literal : Nat → Prim .unit .base
  | add : Prim (.prod .base .base) .base
  | mul : Prim (.prod .base .base) .base
  | pred : Prim .base .base

def meaning : {a b : Ty} → Prim a b → Val Nat a → Val Nat b
  | _, _, .literal n, _ => n
  | _, _, .add, (x,y) => x+y
  | _, _, .mul, (x,y) => x*y
  | _, _, .pred, x => x-1

def charge : {a b : Ty} → Prim a b → Nat := fun _ => 1
private def state : Term Prim [ST] ST := .var .here
private def counter : Term Prim [ST] .base := .fst state
private def accum : Term Prim [ST] .base := .fst (.snd state)
private def threshold : Term Prim [ST] .base := .snd (.snd state)
private def squareTerm : Term Prim [ST] .base := .prim .mul (.pair counter counter)
private def doubleTerm : Term Prim [ST] .base := .prim .add (.pair counter counter)
private def body (weight : Term Prim [ST] .base) : Term Prim [ST] ST :=
  .pair (.prim .pred counter) (.pair (.prim .add (.pair accum weight)) threshold)
private def test : Test Prim [ST] := ⟨counter,threshold⟩
private def post : Term Prim [ST] ST := .pair counter (.pair accum threshold)

def squares : Program Prim IN ST ST where
  seed := .pair (.fst (.var .here)) (.pair (.snd (.var .here)) (.prim (.literal 0) .unit))
  test := test
  body := body squareTerm
  post := post

def thresholded : Program Prim ST ST ST where
  seed := .var .here
  test := test
  body := body doubleTerm
  post := post

@[simp] theorem squares_done (s : State) : squares.done meaning s = done s := rfl
@[simp] theorem squares_step (s : State) : squares.step meaning s = step (fun n => n*n) s := rfl
@[simp] theorem thresholded_done (s : State) : thresholded.done meaning s = done s := rfl
@[simp] theorem thresholded_step (s : State) : thresholded.step meaning s = step (fun n => n+n) s := rfl

def compiledSquares (x : Nat × Nat) := squares.execute meaning charge Prod.fst (decreases (fun n => n*n)) x
def compiledThreshold (x : State) := thresholded.execute meaning charge Prod.fst (decreases (fun n => n+n)) x

theorem squares_result (n a : Nat) : compiledSquares (n,a) =
    ((0,(a+visited (fun i => i*i) 0 n,0)), 1+(n+1)*2+n*3) := by
  have h := Program.execute_of_steps meaning charge squares Prod.fst (decreases (fun n => n*n))
    (n,a) (source_steps (fun n => n*n) n a 0)
  simpa [compiledSquares, Program.finish, squares, test, post, body, squareTerm, counter,
    accum, threshold, state, Test.cost, FoldCompiler.bodyCost, charge, FirstOrderCompiler.eval,
    FirstOrderCompiler.lookup, Nat.add_assoc] using h

theorem threshold_result (n a t : Nat) : compiledThreshold (n,(a,t)) =
    ((min n t,(a+visited (fun i => i+i) t n,t)), (n-t+1)*2+(n-t)*3) := by
  have h := Program.execute_of_steps meaning charge thresholded Prod.fst (decreases (fun n => n+n))
    (n,(a,t)) (source_steps (fun n => n+n) n a t)
  simpa [compiledThreshold, Program.finish, thresholded, test, post, body, doubleTerm, counter,
    accum, threshold, state, Test.cost, FoldCompiler.bodyCost, charge, FirstOrderCompiler.eval,
    FirstOrderCompiler.lookup, Nat.add_assoc] using h

theorem squares_native (n a : Nat) : compiledSquares (n,a) = native (fun i => i*i) 1 (n,(a,0)) := by
  rw [squares_result, native_result]; simp

theorem threshold_native (n a t : Nat) : compiledThreshold (n,(a,t)) = native (fun i => i+i) 0 (n,(a,t)) := by
  rw [threshold_result, native_result]; simp

theorem square_sample : compiledSquares (3,5) = ((0,(19,0)),18) := by
  rw [squares_result]; decide

theorem threshold_sample : compiledThreshold (5,(7,2)) = ((2,(31,2)),17) := by
  rw [threshold_result]; decide

theorem initial_stop (n a t : Nat) (h : n ≤ t) :
    compiledThreshold (n,(a,t)) = ((n,(a,t)),2) := by
  rw [threshold_result, visited_zero _ _ _ h]
  simp [Nat.min_eq_left h, Nat.sub_eq_zero_of_le h]

theorem zero_square (a : Nat) : compiledSquares (0,a) = ((0,(a,0)),3) := by
  rw [squares_result]; simp [visited]
/-- A second tariff changes actual compiled primitive bills, not scalar values. -/
def expensiveSquares (x : Nat × Nat) := squares.execute meaning (fun _ => 2)
  Prod.fst (decreases (fun n => n*n)) x

theorem expensive_result (n a : Nat) : expensiveSquares (n,a) =
    ((0,(a+visited (fun i => i*i) 0 n,0)), 2+(n+1)*2+n*6) := by
  have h := Program.execute_of_steps meaning (fun _ => 2) squares Prod.fst
    (decreases (fun n => n*n)) (n,a) (source_steps (fun n => n*n) n a 0)
  simpa [expensiveSquares, Program.finish, squares, test, post, body, squareTerm, counter,
    accum, threshold, state, Test.cost, FoldCompiler.bodyCost, FirstOrderCompiler.eval,
    FirstOrderCompiler.lookup, Nat.add_assoc] using h

theorem equal_values_different_costs (n a : Nat) :
    (compiledSquares (n,a)).1 = (expensiveSquares (n,a)).1 ∧
    (compiledSquares (n,a)).2 < (expensiveSquares (n,a)).2 := by
  rw [squares_result, expensive_result]
  constructor
  · rfl
  · simp only
    omega

/-- The native measured baseline also recovers the existing ranked executor. -/
theorem native_value_until (w : Nat → Nat) (setup : Nat) (s : State) :
    (native w setup s).1 = runUntil done (step w) Prod.fst (decreases w) s := by
  exact run_value nativeGuard (nativeBody w) Prod.fst (decreases w) s

end Examples.MeasuredLoop
