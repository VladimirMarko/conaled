import Applications.Huffman.Observation

/-! Public Huffman claims checked against leaf-depth arithmetic and competing trees. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.HuffmanCases
open Bracketing Huffman Huffman.Priority Search.PriorityInterface

abbrev unequal : Tree Nat := .fork (.fork (.leaf 1) (.leaf 2)) (.leaf 10)
abbrev expensive : Tree Nat := .fork (.leaf 1) (.fork (.leaf 2) (.leaf 10))
abbrev duplicates : Tree Nat := .fork (.leaf 2) (.fork (.leaf 1) (.leaf 2))
abbrev zeros : Tree Nat := .fork (.fork (.leaf 0) (.leaf 0)) (.leaf 3)
abbrev tiedLeft : Tree Nat := .fork (.fork (.leaf 3) (.leaf 4)) (.fork (.leaf 1) (.leaf 2))
abbrev tiedList : Tree Nat := .fork (.fork (.leaf 1) (.leaf 2)) (.fork (.leaf 3) (.leaf 4))

theorem unequal_arithmetic : pathCost id 0 unequal = 1*2 + 2*2 + 10*1 := by decide +kernel
theorem expensive_arithmetic : pathCost id 0 expensive = 1*1 + 2*2 + 10*2 := by decide +kernel

theorem unequal_leftist : Optimal id [10,1,2] unequal :=
  huffman_correct exactLeftist id [10,1,2] unequal (by decide +kernel)

theorem unequal_list : Optimal id [10,1,2] unequal :=
  huffman_correct exactList id [10,1,2] unequal (by
    simp [huffman, extract, loop, step, singleQ, queueSize, initial, exactList,
      Priority.insert, cachedLeaf, listRemove, List.mergeSort, unequal])

/-- The certificate bounds every feasible tree, not just a concrete enumeration. -/
theorem unequal_global_bound (t : Tree Nat) (ht : Feasible [10,1,2] t) :
    16 ≤ pathCost id 0 t := by
  have h := unequal_leftist.2 t ht
  simpa only [unequal_arithmetic] using h

theorem expensive_feasible : Feasible [10,1,2] expensive := by
  unfold Feasible
  decide +kernel

theorem expensive_is_worse : pathCost id 0 unequal < pathCost id 0 expensive := by
  rw [unequal_arithmetic, expensive_arithmetic]
  decide +kernel

example (Q : ExactQueue (Tree Nat) Nat) (w : Nat → Nat) : huffman Q w [] = none :=
  (huffman_none_iff Q w []).mpr rfl

example (Q : ExactQueue (Tree Nat) Nat) (w : Nat → Nat) (a : Nat) :
    huffman Q w [a] = some (.leaf a) := huffman_singleton Q w a

example (Q : ExactQueue (Tree Nat) Nat) (w : Nat → Nat) (a : Nat) :
    costResult Q w [a] = some 0 := by
  rw [costResult, huffman_singleton]
  rfl

example : Optimal id [7,2] (.fork (.leaf 2) (.leaf 7)) :=
  huffman_correct exactLeftist id [7,2] _ (by decide +kernel)

example : pathCost id 0 (.fork (.leaf 2) (.leaf 7)) = 2*1 + 7*1 := by decide +kernel

example : Optimal id [2,2,1] duplicates :=
  huffman_correct exactLeftist id [2,2,1] duplicates (by decide +kernel)

example : pathCost id 0 duplicates = 2*1 + 1*2 + 2*2 := by decide +kernel

example : Optimal id [0,0,3] zeros :=
  huffman_correct exactList id [0,0,3] zeros (by
    simp [huffman, extract, loop, step, singleQ, queueSize, initial, exactList,
      Priority.insert, cachedLeaf, listRemove, List.mergeSort, zeros])

example : pathCost id 0 zeros = 0*2 + 0*2 + 3*1 := by decide +kernel

theorem tied_leftist_output : huffman exactLeftist (fun _ : Nat => 1) [1,2,3,4] = some tiedLeft := by decide +kernel

theorem tied_list_output : huffman exactList (fun _ : Nat => 1) [1,2,3,4] = some tiedList := by
  simp [huffman, extract, loop, step, singleQ, queueSize, initial, exactList,
      Priority.insert, cachedLeaf, listRemove, List.mergeSort, tiedList]

example : tiedLeft ≠ tiedList := by decide +kernel

example : Optimal (fun _ : Nat => 1) [1,2,3,4] tiedLeft :=
  huffman_correct exactLeftist _ _ _ tied_leftist_output

example : Optimal (fun _ : Nat => 1) [1,2,3,4] tiedList :=
  huffman_correct exactList _ _ _ tied_list_output

/-- Equal optimum costs survive distinct lawful choices at equal priorities. -/
example : pathCost (fun _ : Nat => 1) 0 tiedLeft = pathCost (fun _ : Nat => 1) 0 tiedList := by
  have h := costResult_eq exactLeftist exactList (fun _ : Nat => 1) [1,2,3,4]
  simpa only [costResult, tied_leftist_output, tied_list_output, Option.map_some, Option.some.injEq] using h

example : pathCost (fun _ : Nat => 1) 0 tiedLeft = 1*2 + 1*2 + 1*2 + 1*2 := by decide +kernel

/-- Cache validity and occurrence size are exercised before the final consumer. -/
example (Q : ExactQueue (Tree Nat) Nat) :
    Good Q id (step Q (initial Q id [10,1,2])) ∧
      queueSize Q (step Q (initial Q id [10,1,2])) = 2 := by
  obtain ⟨hg, _, hn⟩ := initial_spec Q id [10,1,2]
  have hs : 2 ≤ queueSize Q (initial Q id [10,1,2]) := by rw [hn]; decide +kernel
  exact ⟨(step_spec Q id _ hg hs).1, by
    have h := step_size Q _ hg.1 hs
    rw [hn] at h
    change queueSize Q (step Q (initial Q id [10,1,2])) + 1 = 3 at h
    omega⟩

example : Good exactLeftist id (step exactLeftist (initial exactLeftist id [10,1,2])) :=
  (step_spec exactLeftist id _ (initial_spec exactLeftist id [10,1,2]).1 (by decide +kernel)).1

example : Good exactList id (step exactList (initial exactList id [10,1,2])) :=
  (step_spec exactList id _ (initial_spec exactList id [10,1,2]).1 (by decide +kernel)).1

example (Q : ExactQueue (Tree Nat) Nat) :
    Iteration.UntilSpec (singleQ Q) (step Q) (initial Q id [10,1,2])
      (loop Q 2 (initial Q id [10,1,2])) := by
  obtain ⟨hg, _, hn⟩ := initial_spec Q id [10,1,2]
  exact (loop_spec Q id 2 _ hg (by rw [hn]; decide +kernel) (by rw [hn]; decide +kernel)).2.2.1

/-- Zero fuel merely extracts a partial forest atom; it does not certify infeasibility. -/
example : extract exactList (loop exactList 0 (initial exactList id [1,2])) = some (.leaf 1) := by
  simp [extract, loop, initial, exactList, cachedLeaf, listRemove]

example : ¬ Feasible [1,2] (.leaf 1) := by
  intro h
  have he := feasible_size h
  simp [size] at he

example : SourcePriority.huffman id [10,1,2] = some unequal := by
  rw [← SourcePriority.huffman_eq]
  decide +kernel

example : (treeSquare exactLeftist id).impl [10,1,2] = ([10,1,2], some unequal) := by
  change ([10,1,2], huffman exactLeftist id [10,1,2]) = ([10,1,2], some unequal)
  decide +kernel

example : ∃ result, ResultSpec id [10,1,2] result ∧
    liftedCost id result = ((costSquare exactLeftist id).impl [10,1,2]).2 :=
  costSquare_permitted exactLeftist id [10,1,2]

example : (costSquare exactLeftist id).impl [10,1,2] = ([10,1,2], some (ULift.up 16)) := by
  rw [costSquare_impl]
  congr 1
  have he : costResult exactLeftist id [10,1,2] = some 16 := by decide +kernel
  rw [he]
  rfl

example : ∃ t, huffman exactList id [10,1,2] = some t ∧
    Optimal id [10,1,2] t ∧ pathCost id 0 t = 16 :=
  costResult_attained exactList id [10,1,2] 16 (by
    rw [← costResult_eq exactLeftist exactList]
    decide +kernel)

example (xs : List Nat) : costResult exactLeftist id xs = costResult exactList id xs :=
  costResult_eq exactLeftist exactList id xs

/-- Occurrence exchange applies when the two least labels are literally equal. -/
example (t : Tree Nat) (ht : Feasible [1,1,2] t) :
    ∃ s, Feasible [none, some 2] s ∧ cost (mergedWeight id 1 1) s + 1 + 1 ≤ cost id t :=
  greedy_exchange id 1 1 [2] t ht (by
    constructor
    · decide +kernel
    · intro x hx
      have he : x = 2 := List.mem_singleton.mp hx
      subst x
      decide +kernel)

example (shape : Tree (Tree Nat)) :
    cost id (flatten shape) = cost (weight id) shape + ((fringeSpec shape).map (cost id)).sum :=
  cost_flatten id shape

example (Q : ExactQueue (Tree Nat) Nat) :
    singleQ Q (loop Q 2 (initial Q id [10,1,2])) = true := by
  obtain ⟨hg, _, hn⟩ := initial_spec Q id [10,1,2]
  exact (loop_spec Q id 2 _ hg (by rw [hn]; decide +kernel)
    (by rw [hn]; decide +kernel)).2.2.1.stopping

/-- Higher-universe labels exercise the extended shared tree, algorithm and square. -/
example (a : ULift.{1} Nat) :
    huffman exactLeftist ULift.down [a] = some (.leaf a) := huffman_singleton exactLeftist _ a

example (a : ULift.{1} Nat) :
    ∃ result, ResultSpec ULift.down [a] result ∧
      liftedCost ULift.down result = ((costSquare exactList ULift.down).impl [a]).2 :=
  costSquare_permitted exactList ULift.down [a]

/-- Exact insertion retains two identical priority entries; keyed coverage is weaker. -/
example : (exactList.add [(1,2),(1,2)] []).length = 2 := rfl

example (xs : List (Nat × Nat)) (q : exactLeftist.Carrier) :
    (exactLeftist.entries (exactLeftist.add xs q)).Perm (xs ++ exactLeftist.entries q) :=
  exactLeftist.add_exact xs q

example (xs : List (Nat × Nat)) (q : exactList.Carrier) (e : Nat × Nat)
    (he : e ∈ xs ++ exactList.entries q) :
    ∃ e' ∈ exactList.entries (exactList.add xs q), e'.1 % 2 = e.1 % 2 ∧ e'.2 ≤ e.2 :=
  (exactList.keyed (fun n : Nat => n % 2)).add_covers xs q e he

end Examples.HuffmanCases
