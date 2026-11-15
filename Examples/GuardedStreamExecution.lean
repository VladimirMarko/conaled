import Applications.GuardedStreams.Measured

namespace Applications.GuardedStreams.Examples
open SquareKit.GuardedStreamCompiler
open SquareKit.GuardedStreamCompiler.Execution
open SquareKit.GuardedStreamCompiler.Examples

/-- Repeating the input head is causal, but cannot be implemented by an indexed
operation that receives only the current coefficient. It needs more state/input. -/
def repeatHead (s : Nat → Nat) (_ : Nat) : Nat := s 0

theorem repeatHead_causal : SquareKit.GuardedStreams.Causal repeatHead := by
  intro n s t h
  exact h 0 (Nat.zero_le n)

theorem repeatHead_not_indexed :
    ¬ ∃ op : Nat → Nat → Nat, ∀ s : Nat → Nat, ∀ n, op n (s n) = repeatHead s n := by
  rintro ⟨op, h⟩
  have hz := h (fun _ => 0) 1
  have ho := h (fun i => if i = 0 then 1 else 0) 1
  simp [repeatHead] at hz ho
  omega

/-- Finite execution agrees with the existing compiler, for available primitive
inputs. This statement is not a code generator for arbitrary Lean functions. -/
theorem emitted_run [AddMonoidWithOne R] (p r : Nat → R) (t : Program)
    (ht : guarded t = true) (n : Nat) :
    Progress.unfold ((inputs p r).step t 0) [] n =
      (List.range n).map (run p r t ht) := by
  have he := (inputs p r).emitted_correct (model p r) (inputs_realize p r)
    t ht 0 (run p r t ht) (solution_fixed _ _ _ _ _ _) n [] (by simp [Agrees])
  simpa using he

theorem finite_interpretation [AddMonoidWithOne R] [AddMonoidWithOne S]
    (f : R →+ S) (h1 : f 1 = 1) (p r : Nat → R)
    (t : Program) (ht : guarded t = true) (n : Nat) :
    (Progress.unfold ((inputs p r).step t 0) [] n).map f =
      Progress.unfold ((inputs (f ∘ p) (f ∘ r)).step t 0) [] n := by
  rw [emitted_run, emitted_run, List.map_map]
  congr 1
  exact run_interpretation f h1 p r (f ∘ p) (f ∘ r) rfl rfl t ht

example (n : Nat) :
    (Progress.unfold ((inputs (fun _ : Nat => (0 : Nat)) compiledOnes).step sumsSource 0) [] n).map
      SquareKit.GuardedStreams.Examples.parity =
    Progress.unfold ((inputs (fun _ : Nat => (0 : ZMod 2)) compiledOnes).step sumsSource 0) [] n := by
  have h := finite_interpretation SquareKit.GuardedStreams.Examples.parity (by decide)
    (fun _ : Nat => (0 : Nat)) compiledOnes sumsSource rfl n
  simpa [Function.comp_def, compiledOnes_eq, SquareKit.GuardedStreams.Examples.parity] using h

example : (recompute 6).1 = [0, 1, 3, 6, 10, 15] := by decide
example : (retain 3 (retain 6 empty).1.2).1.1 = [0, 1, 3] := by decide
example : (retain 6 (retain 6 empty).1.2).1.2 = (retain 6 empty).1.2 := by decide
example : (retain 0 empty).1 = ([], empty) := by decide

/-- Hand-counted operation workload: 3 initial constants and two additions at
coordinates 1, 2, 3 give nine coefficient operations for a fresh prefix of four. -/
example : (recomputedWorkload [4, 4]).2 = (18, 140, 78) := by decide
example : (retainedWorkload [4, 4]).2 = (9, 78, 43) := by decide
example : (retainedWorkload [4, 4]).2.1 < (recomputedWorkload [4, 4]).2.1 ∧
    (retainedWorkload [4, 4]).2.2.1 < (recomputedWorkload [4, 4]).2.2.1 ∧
    (retainedWorkload [4, 4]).2.2.2 < (recomputedWorkload [4, 4]).2.2.2 := by decide

/-- Setup prevents a universal speedup; a single positive request merely ties. -/
example : (retainedWorkload [0]).2 = (0, 0, 1) := by decide
example : (recomputedWorkload [0]).2 = (0, 0, 0) := by decide
example : (retainedWorkload [1]).2 = (recomputedWorkload [1]).2 := by decide
example : live (retainedWorkload [4, 2, 6]).1 = 19 := by decide

example (n : Nat) : Progress.Delivers (Progress.guarded producer) empty
    ((List.range n).map triangular) (Progress.advance producer empty n) n := producer_delivery n
example : guarded (Body.recur : Program) = false := rfl
example (n k : Nat) :
    ¬ Progress.Evaluates (fun s : State => .inr (tick s) : Progress.Machine State Nat)
      empty n k := silent_control n k

end Applications.GuardedStreams.Examples
