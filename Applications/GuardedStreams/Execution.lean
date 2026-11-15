import SquareKit.GuardedStreamExecution
import Examples.GuardedStreamCompiler
import Applications.Resources.Workload

namespace Applications.GuardedStreams
open SquareKit.GuardedStreamCompiler
open SquareKit.GuardedStreamCompiler.Execution
open SquareKit.GuardedStreamCompiler.Examples

/-- These inputs expose the indexed parameter read in addLeft. -/
def inputs [AddMonoidWithOne R] (p r : Nat → R) : Execution Bool Unit Unit Unit Unit R where
  constant b := if b then 1 else 0
  parameter _ := p
  reference _ := r
  operation _ n a := p n + a
  binary _ := (· + ·)

theorem inputs_realize [AddMonoidWithOne R] (p r : Nat → R) : (inputs p r).Realizes (model p r) where
  constant := rfl
  parameter := rfl
  reference := rfl
  operation := fun _ _ _ => rfl
  binary := rfl

/-- Three prefixes, in definition order. Each reference in this client is under
one delay, so the preceding definition's retained prefix is sufficient. -/
structure State where
  ones : List Nat
  sums : List Nat
  triangular : List Nat
  deriving DecidableEq, Repr

def empty : State := ⟨[], [], []⟩

def tick (s : State) : State :=
  ⟨((inputs (fun _ => 0) (fun _ => 0)).step onesBody 0 s.ones).2,
   ((inputs (fun _ => 0) (history 0 s.ones)).step sumsSource 0 s.sums).2,
   ((inputs (fun _ => 0) (history 0 s.sums)).step triangularBody 0 s.triangular).2⟩

structure Valid (s : State) : Prop where
  ones : Agrees s.ones (fun _ => 1)
  sums : Agrees s.sums (fun n => n + 1)
  triangular : Agrees s.triangular Examples.triangular
  lengths₁ : s.ones.length = s.triangular.length
  lengths₂ : s.sums.length = s.triangular.length

theorem empty_valid : Valid empty := by
  constructor <;> simp [empty, Agrees]

theorem history_agrees {xs : List Nat} {f : Nat → Nat} (h : Agrees xs f)
    {i : Nat} (hi : i < xs.length) : history 0 xs i = f i := by
  simp [history, h i hi]

theorem tick_equation (s : State) (h : Valid s) :
    tick s = ⟨s.ones ++ [1], s.sums ++ [s.triangular.length + 1],
      s.triangular ++ [Examples.triangular s.triangular.length]⟩ := by
  have h₁ := h.lengths₁
  have h₂ := h.lengths₂
  have ho : (inputs (fun _ => 0) (fun _ => 0)).eval onesBody (history 0 s.ones) s.ones.length = 1 := by
    cases hn : s.ones.length with
    | zero => rfl
    | succ n =>
      change history 0 s.ones n = 1
      exact history_agrees h.ones (by omega)
  have hs : (inputs (fun _ => 0) (history 0 s.ones)).eval sumsSource
      (history 0 s.sums) s.sums.length = s.triangular.length + 1 := by
    cases hn : s.sums.length with
    | zero => simp [eval, sumsSource, inputs, ← h.lengths₂, hn]
    | succ n =>
      change history 0 s.ones n + history 0 s.sums n = s.triangular.length + 1
      rw [history_agrees h.ones (by omega), history_agrees h.sums (by omega)]
      omega
  have ht : (inputs (fun _ => 0) (history 0 s.sums)).eval triangularBody
      (history 0 s.triangular) s.triangular.length = Examples.triangular s.triangular.length := by
    cases hn : s.triangular.length with
    | zero => rfl
    | succ n =>
      change history 0 s.sums n + history 0 s.triangular n = Examples.triangular (n + 1)
      rw [history_agrees h.sums (by omega), history_agrees h.triangular (by omega)]
      rfl
  simp only [tick, step, ho, hs, ht]

theorem tick_valid (s : State) (h : Valid s) : Valid (tick s) := by
  rw [tick_equation s h]
  constructor
  · exact agrees_append h.ones
  · simpa [h.lengths₂] using agrees_append h.sums
  · exact agrees_append h.triangular
  · simpa using h.lengths₁
  · simpa using h.lengths₂

def extend : Nat → State → State
  | 0, s => s
  | n + 1, s => extend n (tick s)

theorem extend_valid (n : Nat) (s : State) (h : Valid s) : Valid (extend n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (tick_valid s h)

theorem extend_length (n : Nat) (s : State) :
    (extend n s).triangular.length = s.triangular.length + n := by
  induction n generalizing s with
  | zero => simp [extend]
  | succ n ih => simp [extend, ih, tick, step, Nat.add_comm, Nat.add_left_comm]

/-- A stored prefix determines all finite observations without a solver call. -/
theorem prefix_eq {xs : List Nat} {f : Nat → Nat} (h : Agrees xs f) :
    xs = (List.range xs.length).map f := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < xs.length
  · rw [h i hi]; simp [hi]
  · simp [hi]

theorem computed_prefix (n : Nat) :
    (extend n empty).triangular = (List.range n).map Examples.triangular := by
  have hv := (extend_valid n empty empty_valid).triangular
  simpa [extend_length, empty] using prefix_eq hv

/-- The independently specified triangular stream is also the accepted compiler
solution, so this is a comparison with that solution, not a replacement spec. -/
theorem compiled_prefix (n : Nat) :
    (extend n empty).triangular = (List.range n).map compiledTriangular := by
  rw [compiledTriangular_eq]
  exact computed_prefix n


/-- Output is the syntax evaluator's next triangular coefficient. -/
def producer (s : State) : Nat × State :=
  ((inputs (fun _ => 0) (history 0 s.sums)).eval triangularBody
    (history 0 s.triangular) s.triangular.length, tick s)

theorem producer_value (s : State) (h : Valid s) :
    (producer s).1 = Examples.triangular s.triangular.length := by
  have h₂ := h.lengths₂
  change (inputs (fun _ => 0) (history 0 s.sums)).eval triangularBody
    (history 0 s.triangular) s.triangular.length = _
  cases hn : s.triangular.length with
  | zero => rfl
  | succ n =>
    change history 0 s.sums n + history 0 s.triangular n = Examples.triangular (n + 1)
    rw [history_agrees h.sums (by omega), history_agrees h.triangular (by omega)]
    rfl

theorem producer_prefix (n : Nat) (s : State) (h : Valid s) :
    Progress.unfold producer s n =
      (List.range n).map (fun i => Examples.triangular (s.triangular.length + i)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Progress.unfold, producer_value s h, ih _ (show Valid (producer s).2 from tick_valid s h)]
    simp [List.range_succ_eq_map, producer, tick, step, Nat.add_comm, Nat.add_left_comm]

theorem producer_delivery (n : Nat) :
    Progress.Delivers (Progress.guarded producer) empty
      ((List.range n).map Examples.triangular) (Progress.advance producer empty n) n := by
  have hd := Progress.guarded_delivery producer empty n
  rw [producer_prefix n empty empty_valid] at hd
  simpa [empty] using hd

/-- Semantic streams alone do not guarantee that a chosen machine emits. -/
theorem silent_control (n k : Nat) :
    ¬ Progress.Evaluates (fun s : State => .inr (tick s) : Progress.Machine State Nat)
      empty n k := Progress.silent_no_evaluation tick

end Applications.GuardedStreams
