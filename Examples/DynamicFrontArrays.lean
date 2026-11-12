import Applications.Resources.DynamicFrontArrayGrowth

/-! Complete storage observations and refinement consumers for the two policies. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.DynamicFrontArrays
open Resources.DynamicFrontArrays

def literalBlocks : List (List (Event Nat)) :=
  [[.write 0 1],[.allocate 2,.copy 1 (some 1),.write 0 2],
   [.allocate 4,.copy 2 (some 2),.copy 3 (some 1),.write 1 3],[.write 0 4]]
def eagerBlocks : List (List (Event Nat)) :=
  [[.allocate 2,.write 1 1],[.allocate 4,.copy 3 (some 1),.write 2 2],
   [.write 1 3],[.allocate 8,.copy 5 (some 3),.copy 6 (some 2),.copy 7 (some 1),.write 4 4]]

theorem literal_four : grouped add [1,2,3,4] empty =
    (⟨#[some 4,some 3,some 2,some 1],0⟩,literalBlocks) := by decide

theorem eager_four : grouped Eager.add [1,2,3,4] empty =
    (⟨#[none,none,none,none,some 4,some 3,some 2,some 1],4⟩,eagerBlocks) := by decide

theorem literal_trace : (adds [1,2,3,4] empty).2 = literalBlocks.flatten := by
  have h := grouped_flatten add [1,2,3,4] empty
  rw [literal_four] at h
  exact (congrArg Prod.snd h).symm

theorem eager_trace : (Eager.adds [1,2,3,4] empty).2 = eagerBlocks.flatten := by
  have h := grouped_flatten Eager.add [1,2,3,4] empty
  rw [eager_four] at h
  exact (congrArg Prod.snd h).symm

theorem refined_value (xs : List Nat) : value (adds xs empty).1 = xs.reverse :=
  from_empty_value xs

theorem policies_agree (xs : List Nat) :
    value (Eager.adds xs empty).1 = value (adds xs empty).1 :=
  Eager.logical_agreement xs empty_layout

theorem different_first_capacity :
    (add 1 empty).1.slots.size = 1 ∧ (Eager.add 1 empty).1.slots.size = 2 := by decide

theorem neither_uniformly_cheaper :
    work (Eager.adds [1,2,3] empty).2 < work (adds [1,2,3] empty).2 ∧
    work (adds [1,2,3,4] empty).2 < work (Eager.adds [1,2,3,4] empty).2 := by decide

theorem eager_bills : bills Eager.add work [1,2,3,4,5,6,7,8,9] empty =
    [1,2,1,4,1,1,1,8,1] := by decide

def fullSingleton : State Nat := ⟨#[some 9],0⟩
theorem fullSingleton_layout : Layout fullSingleton [9] := by simp [Layout,fullSingleton]

theorem spare_needs_hypothesis : (Eager.add 7 fullSingleton).1.free = 0 ∧
    ¬ (work (Eager.add 7 fullSingleton).2 + Eager.growths (Eager.add 7 fullSingleton).2 +
      fullSingleton.slots.size = 1 + (Eager.add 7 fullSingleton).1.slots.size) := by decide

theorem fullSingleton_preserves_layout : Layout (Eager.add 7 fullSingleton).1 [7,9] :=
  Eager.add_layout 7 fullSingleton_layout

theorem zero_growth : Eager.add 7 ⟨#[],0⟩ = (⟨#[],0⟩,[.allocate 0,.write 0 7]) := by decide

theorem empty_allocation_is_growth : allocation [Event.allocate (α := Nat) 0] = 0 ∧
    Eager.growths [Event.allocate (α := Nat) 0] = 1 := by decide

theorem malformed_raw : add 7 ⟨#[some 9],4⟩ = (⟨#[some 9],3⟩,[.write 3 7]) := by decide

theorem raw_potential (xs : List Nat) :
    work (adds xs ⟨#[some 9],4⟩).2 + potential (adds xs ⟨#[some 9],4⟩).1 ≤
      potential ⟨#[some 9],4⟩ + 3*xs.length := adds_potential xs _

theorem copy_window : copyInto [none,some 7] 1 #[some 90,none,none,some 91] =
    (#[some 90,none,some 7,some 91],[.copy 1 none,.copy 2 (some 7)]) := by decide

theorem copy_attempts : copyInto [some 7,some 8] 0 #[some 90] =
    (#[some 7],[.copy 0 (some 7),.copy 1 (some 8)]) := by decide

theorem eager_geometric (xs : List Nat) (h : xs ≠ []) :
    ∃ p, 2^p ≤ xs.length ∧ xs.length < 2^(p+1) ∧
      work (Eager.adds xs empty).2 = xs.length + Eager.geometricExtras p :=
  Eager.total_work_power_interval xs h

def indexZeroPrice (es : List (Event Nat)) : Nat :=
  (es.map (fun e => match e with | .write 0 _ => 1 | _ => 0)).sum

theorem indexZeroPrice_append (es fs : List (Event Nat)) :
    indexZeroPrice (es ++ fs) = indexZeroPrice es + indexZeroPrice fs := by
  simp only [indexZeroPrice,List.map_append,List.sum_append]

theorem index_price_run (xs : List Nat) (s : State Nat) :
    ((adds xs s).1,indexZeroPrice (adds xs s).2) =
      Resources.run (fun x t => ((add x t).1,indexZeroPrice (add x t).2)) xs s :=
  adds_metered indexZeroPrice rfl indexZeroPrice_append xs s

theorem index_price_separates : indexZeroPrice (adds [1,2,3,4] empty).2 = 3 ∧
    indexZeroPrice (Eager.adds [1,2,3,4] empty).2 = 0 := by decide

theorem literal_bills : bills add work [1,2,3,4,5,6,7,8,9] empty =
    [1,2,3,1,5,1,1,1,9] := by decide

theorem bills_recover_work (xs : List Nat) :
    (bills Eager.add work xs empty).sum = work (Eager.adds xs empty).2 :=
  bills_sum Eager.add work rfl work_append xs empty

theorem overwritten_window :
    (copyInto [none,some 7] 1 #[some 90,some 8,some 9,some 91]).1.toList =
      [some 90,none,some 7,some 91] :=
  copyInto_window [none,some 7] [some 8,some 9] [some 90] [some 91] _ rfl rfl

theorem order_is_more_than_work :
    work [Event.write 0 1,.write 1 2] = work [.write 1 2,.write 0 1] ∧
      ([Event.write 0 1,.write 1 2] : List (Event Nat)) ≠ [.write 1 2,.write 0 1] := by decide

theorem flatten_loses_boundaries :
    ([[Event.write 0 1,.write 1 2]] : List (List (Event Nat))).flatten =
      [[.write 0 1],[.write 1 2]].flatten ∧
    ([[Event.write 0 1,.write 1 2]] : List (List (Event Nat))) ≠ [[.write 0 1],[.write 1 2]] := by decide

end Examples.DynamicFrontArrays
