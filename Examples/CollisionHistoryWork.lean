import Applications.Resources.CollisionHistory

/-!
# Connected collision history work cases

The numerical expectations count the declared operations of the measured
client. Source value transport and resource observations are checked together.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.CollisionHistoryWork
open Resources Search

theorem generic_three_repeats {κ T : Type} (ops : TotalTable.Ops κ Bool T)
    (Valid : T → Prop) (laws : TotalTable.Laws ops false Valid) (key : κ) :
    (CollisionWork.run (fun k t => (ops.get k t, 1))
      (fun k v t => (ops.set k v t, 2))
      (fun c : Nat => (c + 1, 3)) (4 : Nat) 5 [key, key, key] (0, ops.empty)).1.1 = 2 := by
  rw [CollisionWork.run_value ops _ _ _ 4 5 (by intros; rfl) (by intros; rfl) (by intros; rfl)]
  classical
  change Collisions.collisions ops [key, key, key] = 2
  rw [Collisions.collisions_correct laws]
  change Collisions.count (List.replicate 3 key) = 2
  exact Collisions.count_replicate key 3

/-- Three entries cost12, reads3, one write2, two increments6, terminal5. -/
theorem three_repeats_bill :
    (CollisionWork.run (fun key table => (table key, 1))
      (fun key value table => (Function.update table key value, 2))
      (fun c : Nat => (c + 1, 3)) (4 : Nat) 5 [7, 7, 7]
      (0, fun _ : Nat => false)).2 = 28 := by
  simp [CollisionWork.run_cons, CollisionWork.step, Resources.bind, CollisionWork.run_nil]

theorem unary_operand_orientation (c : Nat) :
    (CollisionWork.unaryAddRun c 1).1 = (CollisionWork.unaryAddRun 1 c).1 ∧
    (CollisionWork.unaryAddRun c 1).2 = c + 1 ∧
    (CollisionWork.unaryAddRun 1 c).2 = 2 := by
  simp [CollisionWork.unaryAddRun_value, CollisionWork.unaryAddRun_cost, Nat.add_comm]

theorem empty_terminal (counter : Nat) (table : Nat → Bool) :
    CollisionWork.run (fun key table => (table key, 9))
      (fun key value table => (Function.update table key value, 8))
      (fun c : Nat => (c + 1, 7)) (6 : Nat) 5 [] (counter, table) = ((counter, table), 5) :=
  CollisionWork.run_nil _ _ _ _ _ _

end Examples.CollisionHistoryWork

namespace Examples.CollisionHistoryWork
open Resources Resources.CollisionHistory

/-- The complete measured realizations retain the literal source numeral lists. -/
theorem measured_source_pi :
    (unaryRun [3, 1, 4, 1, 5, 9, 2, 6]).1.1 = 1 ∧
    (signedRun [3, 1, 4, 1, 5, 9, 2, 6]).1.1.toZNum = 1 := by
  constructor
  · rw [unaryRun_source, Search.Collisions.VerySlow.collisions_correct]
    decide
  · rw [signedRun_source]
    apply ZNum.to_int_inj.mp
    rw [Search.Collisions.RatherSlow.collisions_correct]
    decide

theorem history_shadowing :
    (lookupRun unaryEqRun 7 [(7, false), (7, true)]).1 = false ∧
    (lookupRun unaryEqRun 7 [(7, false), (7, true)]).2 .keyTests = 1 ∧
    (lookupRun unaryEqRun 7 [(7, false), (7, true)]).2 .keyWork = 8 ∧
    (lookupRun unaryEqRun 7 [(7, false), (7, true)]).2 .lookupTerminal = 0 := by
  decide

/-- Equality groups cost 0, 2, and 2+4; the duplicate creates no history cell. -/
theorem unary_head_first_trace :
    (unaryRun [3, 1, 3]).1 = (1, [(1, true), (3, true)]) ∧
    (unaryRun [3, 1, 3]).2 .keyTests = 3 ∧
    (unaryRun [3, 1, 3]).2 .keyWork = 8 ∧
    (unaryRun [3, 1, 3]).2 .historyCells = 2 ∧
    total (unaryRun [3, 1, 3]).2 = 21 := by
  decide

/-- Sign dispatch and reversed negative comparison both affect this trace. -/
theorem signed_head_first_trace :
    (signedRun [-2, 3, -2, -3, 3]).1.1.toZNum = 2 ∧
    (signedRun [-2, 3, -2, -3, 3]).2 .keyTests = 7 ∧
    (signedRun [-2, 3, -2, -3, 3]).2 .keyWork = 20 ∧
    (signedRun [-2, 3, -2, -3, 3]).2 .counterWork = 3 ∧
    (signedRun [-2, 3, -2, -3, 3]).2 .counterCalls = 2 ∧
    total (signedRun [-2, 3, -2, -3, 3]).2 = 44 := by
  decide

theorem actual_empty_costs :
    total (unaryRun []).2 = 1 ∧ total (signedRun []).2 = 1 ∧
    (unaryRun []).1.1 = 0 ∧ (signedRun []).1.1.toZNum = 0 := by
  decide

/-- Source c+1, started at five, costs six then seven unary entered calls. -/
theorem unary_initial_counter_cost :
    (run unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) [7, 7] (5, [(7, true)])).1.1 = 7 ∧
    (run unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) [7, 7] (5, [(7, true)])).2 .counterWork = 13 ∧
    (run unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) [7, 7] (5, [(7, true)])).2 .historyCells = 0 := by
  decide

theorem repeated_unary_counter (key : Nat) :
    (unaryRun [key, key, key]).2 .counterWork = 3 ∧
    (unaryRun [key, key, key]).2 .historyCells = 1 := by
  have repeats : Search.Collisions.count [key, key, key] = 2 := by
    exact Search.Collisions.count_replicate key 3
  have accounting := unaryRun_counter_exact [key, key, key]
  rw [repeats] at accounting
  constructor
  · omega
  · rw [unaryRun_cells]
    simp

theorem repeated_binary_counter :
    (signedRun [-7, -7, -7]).1.1.toZNum = 2 ∧
    (signedRun [-7, -7, -7]).2 .counterWork = 3 ∧
    (signedRun [-7, -7, -7]).2 .counterCalls = 2 ∧
    (signedRun [-7, -7, -7]).2 .historyCells = 1 := by
  decide

theorem fresh_prefix_cardinality :
    (unaryRun [3]).1.2.length = 1 ∧
    (unaryRun [3, 1]).1.2.length = 2 ∧
    (unaryRun [3, 1, 3]).1.2.length = 2 := by
  decide

theorem unary_trace_bound : total (unaryRun [3, 1, 3]).2 ≤ 55 :=
  unaryRun_total_le [3, 1, 3] 3 (by decide)

theorem signed_trace_bound : total (signedRun [-2, 3, -2, -3, 3]).2 ≤ 136 :=
  signedRun_total_le [-2, 3, -2, -3, 3] 2 (by decide)

/-- For n=3 the lower comparison estimate is twelve; actual comparison work is
thirteen, with thirteen further units of declared overhead and history creation. -/
theorem interval_boundaries_and_three :
    total (unaryRun (List.range' 0 0)).2 = 1 ∧
    total (unaryRun (List.range' 1 1)).2 = 4 ∧
    (unaryRun (List.range' 3 3)).2 .keyWork = 13 ∧
    total (unaryRun (List.range' 3 3)).2 = 26 := by
  decide

theorem interval_three_lower : 12 ≤ total (unaryRun (List.range' 3 3)).2 :=
  unaryRun_interval_lower 3

theorem signed_prefix_nonnegative (xs : List ZNum) :
    0 ≤ ((signedRun xs).1.1.toZNum : Int) ∧ ((signedRun xs).1.1 : Nat) ≤ xs.length := by
  refine ⟨PositiveCounter.num_toZNum_nonnegative _, ?_⟩
  rw [signedRun_count]
  exact Nat.sub_le _ _

end Examples.CollisionHistoryWork

namespace Examples.CollisionHistoryWork
open Resources.CollisionHistory

theorem signed_comparison_branches :
    signedEqRun 0 0 = (true, 2) ∧
    signedLtRun (-2) 3 = (true, 2) ∧
    signedLtRun (-2) (-3) = (false, 4) ∧
    signedLtRun (-3) (-2) = (true, 4) := by
  decide

theorem unary_equal_and_different_terminal (n : Nat) :
    (unaryEqRun n n).1 = true ∧ (unaryEqRun n n).2 = n + 1 ∧
    (unaryEqRun 0 (n + 1)).1 = false ∧ (unaryEqRun 0 (n + 1)).2 = 1 := by
  simp [unaryEqRun_value, unaryEqRun_cost]

end Examples.CollisionHistoryWork
