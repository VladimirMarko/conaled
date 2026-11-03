import Applications.Resources.RandomAccess.EndObservation

/-! Connected cost observations and domain boundaries for the end operations. -/
namespace Examples.RandomAccessEndCosts
open RandomAccess Resources Resources.RandomAccessCosts

-- Empty construction differs from an attempted removal from empty.
example : toRARun ([] : List Nat) = ([],0) := toRARun_nil
example : unconsRARun ([] : RAList Nat) = (none,1) := unconsRARun_exact _
example : headRARun ([] : RAList Nat) = (none,1) := rfl
example : tailRARun ([] : RAList Nat) = (none,1) := rfl
example : drainRun 0 (toRA [7]) = (([],toRA [7]),0) := rfl
example : drainRun 8 ([] : RAList Nat) = (([],[]),1) := rfl
example : (drainRun 1 (toRA [7])).1 = ([7],[]) := full_drain_value (inv_toRA [7])
example : (toRARun [1,2,3,4]).2 = 7 := by
  have hp := toRARun_potential [1,2,3,4]
  rw [toRARun_value] at hp
  change (toRARun [1,2,3,4]).2 + 1 = 8 at hp
  omega
example : (drainRun 4 (toRA [1,2,3,4])).1 = ([1,2,3,4],[]) :=
  full_drain_value (inv_toRA [1,2,3,4])
example : 4 ≤ (drainRun 4 (toRA [1,2,3,4])).2 ∧
    (drainRun 4 (toRA [1,2,3,4])).2 ≤ 12  := by
  simpa [fromRA_toRA] using full_drain_linear_bounds (inv_toRA [1,2,3,4])
example : (drainRun 4 (toRA [1,2,3,4])).2 = 7 := rfl
example : (drainRun 5 (toRA [1,2,3,4])).2 = 8 := rfl
example : (drainRun 20 (toRA [1,2,3,4])).2 = 8 := rfl
example : ((constructDrain 2).impl [1,2,3,4]).1 = ([1,2],[3,4]) := constructDrain_value _ _
example : ((constructDrain 0).impl [1,2,3,4]).1 = ([],[1,2,3,4]) := constructDrain_value _ _
example : ((constructDrain 4).impl [1,2,3,4]).1 = ([1,2,3,4],[]) := constructDrain_full _
example : ((constructDrain 4).impl [1,2,3,4]).2 = 14 := by rw [constructDrain_cost]; rfl
example : ((constructDrain 5).impl [1,2,3,4]).2 = 15 := by rw [constructDrain_cost]; rfl
example : ((constructDrain 4).impl [1,2,3,4]).2 ≤ 20 := constructDrain_full_bound _
example : ((constructDrain 1).impl ([] : List Nat)) = (([],[]),1) := rfl

-- Potentials include the initial state, and pushing visits input in foldl order.
example : fromRA (pushManyRun [8,9] (toRA [1])).1 = [9,8,1] := by
  rw [pushManyRun_value]; rfl
example : (pushManyRun [8,9] (toRA [1])).2 + ones (pushManyRun [8,9] (toRA [1])).1 = 5 :=
  pushManyRun_potential _ _
example : (drainRun 1 (toRA [1,2,3,4])).2 + zeros (drainRun 1 (toRA [1,2,3,4])).1.2 ≤ 4 :=
  (drainRun_spec 1 (inv_toRA _)).2.2.2
example : (headRARun (toRA [1,2,3,4])).1 = some 1 := headRARun_value _
example : (tailRARun (toRA [1,2,3,4])).1 = some (toRA [2,3,4]) := tailRARun_value _
example : (headRARun (toRA [1,2,3,4])).2 ≤ 4 ∧
    (tailRARun (toRA [1,2,3,4])).2 ≤ 4 := head_tail_log_bounds (inv_toRA _)

-- Malformed borrowed trees still preserve the exact attempted-work count.
example : unconsTRun ([.zero,.one (.leaf 7)] : RAList Nat) = (none,2) := unconsTRun_exact _
example : unconsRARun ([.one (node (.leaf 1) (.leaf 2))] : RAList Nat) = (none,1) :=
  unconsRARun_exact _
example : drainRun 4 ([.zero,.one (.leaf 7)] : RAList Nat) =
    (([],[.zero,.one (.leaf 7)]),2) := rfl
example : fromRA (consRARun 9 ([.zero,.one (.leaf 7)] : RAList Nat)).1 = [9,7] :=
  consRARun_refinement _ _

-- A correct cache need not describe a perfect (balanced) tree.
private def unbalanced : Tree Nat := node (.leaf 1) (node (.leaf 2) (.leaf 3))
private theorem unbalanced_cached : Cached unbalanced :=
  cached_node True.intro (cached_node True.intro True.intro)
example : (structuralSizeRun (erase unbalanced)).1 = 3 := structuralSizeRun_value _
example : (structuralSizeRun (erase unbalanced)).2 + 1 = 6 := structuralSizeRun_work _
example : ((observedStructuralSize Nat).impl ⟨unbalanced,unbalanced_cached⟩).down.1 =
    (cachedSizeSquare.impl ⟨unbalanced,unbalanced_cached⟩).down.1 :=
  (observedSize_comparison ⟨unbalanced,unbalanced_cached⟩).1
example : ((observedStructuralSize Nat).impl ⟨unbalanced,unbalanced_cached⟩).down.2 = 5 ∧
    (cachedSizeSquare.impl ⟨unbalanced,unbalanced_cached⟩).down.2 = 1 := by
  have h := observedSize_comparison ⟨unbalanced,unbalanced_cached⟩
  exact ⟨by have := h.2.1; change _ + 1 = 6 at this; omega, h.2.2⟩
example : cachedSizeRun (.node 99 (.leaf 1) (.leaf 2)) = (99,1) := cachedSizeRun_exact _
example : (structuralSizeRun (erase (.node 99 (.leaf 1) (.leaf 2)))).1 = 2 :=
  structuralSizeRun_value _
example : ¬ Cached (.node 99 (.leaf 1) (.leaf 2) : Tree Nat) := by simp [Cached, size]

-- The skeleton measures rank-sized chunks; at rank two one bit represents four leaves.
example : (fromRA [.one (perfectTree 7 2)]).length =
    4 * BinaryCounter.value (bits [.one (perfectTree 7 2)]) :=
  bits_value (Valid.one (perfectTree_valid 7 2) (Valid.nil 3))
example : BinaryCounter.Canonical (bits (toRA [1,2,3,4])) := bits_canonical (inv_toRA _)
example : bits (consRA 8 (toRA [1,2,3])) = BinaryCounter.inc (bits (toRA [1,2,3])) :=
  bits_consT _ _
example : (consRARun 8 (toRA [1,2,3])).2 = BinaryCounter.flipCost (bits (toRA [1,2,3])) :=
  consTRun_count_bits _ _
example : BinaryCounter.decBits [] = none := rfl
example : BinaryCounter.decBits [false] = none := rfl
example : ¬ BinaryCounter.Canonical [true,false] := by simp [BinaryCounter.Canonical]
example : BinaryCounter.decBits [true,false] = some [false,false] := rfl
example : ∃ ys, BinaryCounter.decBits [false,false,true] = some ys ∧
    BinaryCounter.Canonical ys ∧ BinaryCounter.value [false,false,true] = BinaryCounter.value ys + 1 :=
  BinaryCounter.decBits_spec (by simp [BinaryCounter.Canonical]) (by decide)
example : BinaryCounter.decBits (bits (toRA [1,2,3,4])) = some (bits (toRA [2,3,4])) :=
  bits_unconsT (inv_toRA _) (t := .leaf 1) rfl

-- Numeric decrement describes the same result returned by actual tree borrowing.
example : BinaryCounter.value (bits (toRA [1,2,3,4])) =
    BinaryCounter.value (bits (toRA [2,3,4])) + 1 := by
  obtain ⟨ys, he, _, hv⟩ := BinaryCounter.decBits_spec
    (bits_canonical (inv_toRA [1,2,3,4])) (by decide)
  rw [bits_unconsT (inv_toRA [1,2,3,4]) (t := .leaf 1) (ys := toRA [2,3,4]) rfl] at he
  cases Option.some.inj he
  exact hv

example : ((observedPushPop 8).impl (encode [1,2,3])).1 = some (8,[1,2,3]) :=
  observedPushPop_value _ _
example : ((observedPushPop 8).impl (encode [1,2,3])).2 = 6 := observedPushPop_cost _ _
example : pushPopRun 8 (toRA [1,2,3]) = (some (8,toRA [1,2,3]),6) :=
  pushPopRun_exact _ (inv_toRA _)
example : mixedRun 8 3 (fullDigits 8 0 3) = (fullDigits 8 0 3,24) := mixed_fullDigits_exact _ _ _
example (potential : RAList Nat → Nat) (C : Nat) :
    ∃ ds, Inv ds ∧ (mixedRun 8 1 ds).1 = ds ∧
      potential ds + 2*C < (mixedRun 8 1 ds).2 + potential (mixedRun 8 1 ds).1 :=
  no_uniform_mixed_charge _ potential C

example : fetchRAError 0 ([] : RAList Nat) = .error "index too large" := fetchRAError_nil _
example : fetchRAError 4 (toRA [1,2,3,4]) = .error "index too large" :=
  (fetchRAError_error_iff (inv_toRA _) _).mpr (by decide)
example : fetchRAError 3 (toRA [1,2,3,4]) = .ok 4 :=
  (fetchRAError_ok_iff (inv_toRA _) _ _).mpr rfl
example : tree [1,2,3,4] = some (node (node (.leaf 1) (.leaf 2)) (node (.leaf 3) (.leaf 4))) :=
  four_element_tree _ _ _ _
example : unconsTRun [.zero,.zero,.one (node (node (.leaf 1) (.leaf 2))
    (node (.leaf 3) (.leaf 4)))] = (some (.leaf 1,[.one (.leaf 2),.one (node (.leaf 3) (.leaf 4))]),3) :=
  (four_element_borrow_derivation 1 2 3 4).2.2.2
example : ([(1,7),(2,3),(3,4),(2,8)].scanl (fun ds p => updateRA p.1 p.2 ds)
    (toRA [0,1,2,3])).map fromRA =
      [[0,1,2,3],[0,7,2,3],[0,7,3,3],[0,7,3,4],[0,7,8,4]] := bulk_answer_intermediate_states
example : fromRA (bulk (toRA [0,1,2,3]) [(1,7),(2,3),(3,4),(2,8)]) = [0,7,8,4] :=
  bulk_answer_final_state

end Examples.RandomAccessEndCosts
