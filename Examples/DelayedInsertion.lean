import Applications.Resources.DelayedInsertion
import SquareKit.PartialSpine.DifferenceConcat

/-! Finite delayed insertion and native retained requests. These examples exercise
source-operation counts, not host allocation or elapsed-time claims. -/
set_option autoImplicit false
set_option warningAsError true
namespace DelayedInsertionExamples
open Resources Resources.DelayedInsertion Applications.Memoization

/-- Universal readout uses the native insertion theorem without label equality. -/
theorem ordinary_spec {α β : Type} (x : α) (xs : List α) (f : List α → Measured β Nat) :
    (forceAll f (ordinary x xs).1).1 =
      (List.permutations'Aux x xs).map (fun ys => (f ys).1) := by
  rw [ordinary_values, Sequences.Permutations.insertsWith_eq_map]

theorem accumulating_tail_spec {α : Type} (x : α) (xs tail : List α) :
    readout (accumulating (fun ys => (ys ++ tail, 0)) x xs).1 =
      (List.permutations'Aux x xs).map (fun ys => ys ++ tail) :=
  accumulating_tail x xs tail

theorem insertion_output_length {α : Type} (x : α) (xs : List α) (i : Nat)
    (h : i < (ordinary x xs).1.length) :
    ((((ordinary x xs).1[i]) ()).1).length = xs.length+1 := by
  rw [ordinary_position]
  apply insertAt_length
  rw [ordinary_length] at h
  omega

theorem three_position_counts :
    outerCells (ordinary (1 : Nat) [2,3]).2 = 6 ∧
    outerCells (accumulating (fun ys : List Nat => (ys,7)) 1 [2,3]).2 = 3 ∧
    payloadCells (forceAll (fun ys : List Nat => (ys,7)) (ordinary 1 [2,3]).1).2 = 6 := by
  rw [ordinary_outerCells, accumulating, accumulate_outerCells, ordinary_all_payloadCells]
  decide

theorem three_position_values :
    (complete 1 [2,3] (fun ys : List Nat => (ys,7))).1 =
      [[1,2,3],[2,1,3],[2,3,1]] := by
  rw [complete_values]
  rfl

example : (completeAccumulating 1 [] (fun ys : List Nat => (ys,7))).1 = [[1]] := by
  rw [completeAccumulating_values]
  rfl

example : observe (([[]] : List (List Nat)), ([] : Trace)) = (([[]] : List (List Nat)), [.innerObserve 4]) := by
  rw [observe_eq]
  rfl

example : observe (([] : List (List Nat)), ([] : Trace)) = (([] : List (List Nat)), [.innerObserve 1]) := by
  rw [observe_eq]
  rfl

example : callbackBills (countOuter (ordinary (1 : Nat) [2,3])).2 = [] := by
  rw [countOuter_callback, ordinary_no_callback]

example : callbackBills (forceAll (fun ys : List Nat => (ys,ys.headD 0))
    (ordinary 1 [2,3]).1).2 = [1,2,2] := by
  rw [ordinary_all_callbacks]
  rfl

/-- Function-valued labels need no decidable equality. -/
example (x : Nat → Nat) (xs tail : List (Nat → Nat)) :
    readout (accumulating (fun ys => (ys ++ tail, 3)) x xs).1 =
      (List.permutations'Aux x xs).map (fun ys => ys ++ tail) := by
  exact (accumulate_readout _ x xs).trans (Sequences.Permutations.insertsWith_eq_map _ _ _)

abbrev equalTable := (prepare (ordinary (1 : Nat) [1])).1
abbrev charge (n : Nat) : List Nat → Measured (List Nat) Nat := fun ys => (ys,n)
abbrev zeroKey : Fin equalTable.size := ⟨0,by decide⟩
abbrev oneKey : Fin equalTable.size := ⟨1,by decide⟩
abbrev initialCache : Cache equalTable.size (List Nat) := (setup equalTable).1

example : zeroKey ≠ oneKey ∧
    (delayedBody equalTable (charge 9) zeroKey).1 =
      (delayedBody equalTable (charge 9) oneKey).1 := by decide

/-- Full validity retains the measured trace, not just the returned value. -/
theorem stale_bill_rejected :
    ¬ Valid equalTable (charge 10) (nativeCall equalTable (charge 9) zeroKey initialCache).1.2 := by
  intro h
  have wrong := h zeroKey ([1,1], [.selection 1,.payloadCons,.callback 9]) rfl
  cases wrong

theorem changed_value_rejected :
    ¬ Valid equalTable (fun _ => ([4],9))
      (nativeCall equalTable (charge 9) zeroKey initialCache).1.2 := by
  intro h
  have wrong := h zeroKey ([1,1], [.selection 1,.payloadCons,.callback 9]) rfl
  cases wrong

example : (retainedRun equalTable (charge 9) [zeroKey,zeroKey,oneKey] initialCache).1.2.2 =
    (1,2,4,3) := by decide

example : callbackBills (retained equalTable (charge 9) zeroKey
    (nativeCall equalTable (charge 9) zeroKey initialCache).1.2).2 = [] := by
  rw [retained_repeat_trace _ _ _ _ (setup_valid _ _)]
  rfl

/-- Callback order is retained before additive Nat projection. -/
theorem order_is_not_scalar_fusion :
    ([Event.callback 1,.callback 2,.callback 3,.callback 4] : Trace) ≠
      [.callback 1,.callback 3,.callback 2,.callback 4] ∧
    (callbackBills [.callback 1,.callback 2,.callback 3,.callback 4]).sum =
      (callbackBills [.callback 1,.callback 3,.callback 2,.callback 4]).sum := by decide

section Boundaries
open Order SquareKit PartialSpine
variable {α : Type}

/-- Unknown end blocks fallback; completed nil permits it. -/
theorem unknown_and_nil (suffix : Observations α) :
    Observations.append ⊥ suffix = ⊥ ∧
      Observations.append (Ideal.principal .nil) suffix = suffix :=
  ⟨Observations.append_bottom _, Observations.append_nil _⟩

theorem strict_infinite_outer (xs : Stream' (Observations α)) :
    Observations.concatD (stream xs) = ⊥ := Observations.concatD_stream xs
end Boundaries
end DelayedInsertionExamples
