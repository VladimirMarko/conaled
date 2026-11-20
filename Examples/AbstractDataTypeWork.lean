import Applications.Resources.SourceQueue
import Applications.Resources.ListErase
import Applications.Resources.Growth
import Examples.AbstractDataTypes

/-!
# ADT clients that distinguish meanings from measured work

These clients use the source queue operations, the common FIFO executor, and
the unique-key pair-list update. Queue work includes one dispatch per call.
The source reversal counts recursive reverse/append entries, while the linear
realization counts accumulator entries. List update work counts key equality
calls, excluding their internal cost. All values come from the measured runs.

The examples include empty and raw-pair branches, actual enqueue reachability,
initial/final potential, sequential history composition, repeated observations,
and both cheap and worst-case unique-list updates. Real-cast growth statements
refer only to these explicitly defined counts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AbstractDataTypeWork
universe u v
variable {α : Type u} {κ : Type v}
open Resources
open Resources.SourceQueue
open Sequences.SourceQueue
open Sequences.AbstractFIFO (Command)
open Search.OrderedMap.AssociationListEnumeration (UniqueList)

theorem list_enqueue_empty (value : α) : listEnqueueRun [] value = ([value], 1) :=
  listEnqueueRun_exact [] value

theorem list_enqueue_nonempty (first second value : α) :
    listEnqueueRun [first, second] value = ([first, second, value], 3) :=
  listEnqueueRun_exact [first, second] value

theorem list_enqueue_family (count : Nat) (old value : α) :
    listEnqueueRun (List.replicate count old) value =
      (List.replicate count old ++ [value], count + 1) := by
  simpa using listEnqueueRun_exact (List.replicate count old) value

theorem list_enqueue_linear_growth (old value : α) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((listEnqueueRun (List.replicate n old) value).2 : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  apply isBigO_of_nat_bound _ (fun n => n) 2 1
  intro n hn
  rw [list_enqueue_family]
  change n + 1 ≤ 2 * n
  omega

theorem list_enqueue_not_uniform (old value : α) (charge : Nat) :
    charge < (listEnqueueRun (List.replicate charge old) value).2 := by
  rw [list_enqueue_family]
  exact Nat.lt_succ_self charge

/-- The truly empty branch performs no reversal in either realization. -/
theorem empty_queue_dispatch (default : α) :
    peekRun default twoListEmpty = (default, 1) ∧
    linearPeekRun default twoListEmpty = (default, 1) ∧
    dequeueRun (twoListEmpty : TwoList α) = (twoListEmpty, 1) ∧
    linearDequeueRun (twoListEmpty : TwoList α) = (twoListEmpty, 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem nonempty_front_dispatch (default first : α) (front back : List α) :
    peekRun default (first :: front, back) = (first, 1) ∧
    linearPeekRun default (first :: front, back) = (first, 1) ∧
    dequeueRun (first :: front, back) = ((front, back), 1) :=
  ⟨rfl, rfl, rfl⟩

theorem source_singleton_counts (default value : α) :
    peekRun default ([], [value]) = (value, 4) ∧
    linearPeekRun default ([], [value]) = (value, 3) ∧
    dequeueRun ([], [value]) = (([], []), 4) ∧
    linearDequeueRun ([], [value]) = (([], []), 3) :=
  ⟨rfl, rfl, rfl, rfl⟩

def threeEnqueues : List (Command Nat) := [.enqueue 4, .enqueue 9, .enqueue 2]

theorem three_enqueues_reachable :
    Sequences.AbstractFIFO.run (twoListFIFO Nat) threeEnqueues twoListEmpty = ([], [2, 9, 4]) := by
  simpa [threeEnqueues, twoListEmpty] using twoList_run_enqueues [4, 9, 2] [] []

theorem three_back_decode : twoListDecode (([], [2, 9, 4]) : TwoList Nat) = [4, 9, 2] := rfl

theorem three_back_source_peek : peekRun 99 ([], [2, 9, 4]) = (4, 11) := by
  rw [peekRun_back]
  rfl

theorem three_back_linear_peek : linearPeekRun 99 ([], [2, 9, 4]) = (4, 5) := by
  rw [linearPeekRun_back]
  rfl

theorem same_peek_different_cost :
    (peekRun 99 ([], [2, 9, 4])).1 = (linearPeekRun 99 ([], [2, 9, 4])).1 ∧
    (linearPeekRun 99 ([], [2, 9, 4])).2 < (peekRun 99 ([], [2, 9, 4])).2 :=
  ⟨peek_realizations_agree _ _, linearPeekRun_back_cost_lt _ _ _⟩

theorem three_back_source_dequeue : dequeueRun ([], [2, 9, 4]) = (([9, 2], []), 11) := by
  rw [dequeueRun_back]
  rfl

theorem three_back_linear_dequeue : linearDequeueRun ([], [2, 9, 4]) = (([9, 2], []), 5) := by
  rw [linearDequeueRun_back]
  rfl

theorem repeated_source_peeks :
    runPeeksUsing ListReversal.naiveRun 99 3 ([], [2, 9, 4]) = (([], [2, 9, 4]), 33) := by
  rw [runPeeksUsing_exact]
  change (([], [2, 9, 4]), 3 * (peekRun 99 ([], [2, 9, 4])).2) = _
  rw [three_back_source_peek]
  rfl

theorem repeated_linear_peeks :
    runPeeksUsing (fun values => SymmetricCosts.reverseRun values []) 99 3 ([], [2, 9, 4]) =
      (([], [2, 9, 4]), 15) := by
  rw [runPeeksUsing_exact]
  change (([], [2, 9, 4]), 3 * (linearPeekRun 99 ([], [2, 9, 4])).2) = _
  rw [three_back_linear_peek]
  rfl

/-- Even the linear model's three peeks exceed back credit plus charge two. -/
theorem repeated_peeks_exceed_back_credit :
    backPotential (([], [2, 9, 4]) : TwoList Nat) + 2 * 3 <
      (runPeeksUsing (fun values => SymmetricCosts.reverseRun values []) 99 3 ([], [2, 9, 4])).2 := by
  rw [repeated_linear_peeks]
  decide

def fourCommands : List (Command Nat) := threeEnqueues ++ [.delete]

theorem enqueues_then_delete_work :
    Resources.run linearStep fourCommands twoListEmpty = (([9, 2], []), 8) := rfl

theorem enqueues_then_delete_value :
    twoListDecode (Resources.run linearStep fourCommands twoListEmpty).1 = [9, 2] := by
  rw [enqueues_then_delete_work]
  rfl

theorem enqueues_then_delete_head :
    (twoListFIFO Nat).head (Resources.run linearStep fourCommands twoListEmpty).1 = some 9 := by
  change twoListHead? (Resources.run linearStep fourCommands twoListEmpty).1 = some 9
  rw [twoListHead?_decode, enqueues_then_delete_value]
  rfl

theorem four_commands_budget_tight :
    (Resources.run linearStep fourCommands twoListEmpty).2 +
      backPotential (Resources.run linearStep fourCommands twoListEmpty).1 =
        2 * fourCommands.length := rfl

theorem back_credit_is_required :
    2 < (linearDequeueRun (([], [2, 9, 4]) : TwoList Nat)).2 ∧
    (linearDequeueRun (([], [2, 9, 4]) : TwoList Nat)).2 =
      backPotential (([], [2, 9, 4]) : TwoList Nat) + 2 := by
  rw [three_back_linear_dequeue]
  decide

theorem arbitrary_raw_history_bound (commands : List (Command α)) (front back : List α) :
    (Resources.run linearStep commands (front, back)).2 +
        backPotential (Resources.run linearStep commands (front, back)).1 ≤
      back.length + 2 * commands.length :=
  linearRun_potential commands (front, back)

theorem sequential_history_bound (first second : List (Command α)) (queue : TwoList α) :
    (bind (Resources.run linearStep first queue) (Resources.run linearStep second)).2 ≤
      backPotential queue + 2 * (first.length + second.length) :=
  linear_sequential_bound first second queue

theorem public_fifo_budget (commands : List (Command α)) (queue : TwoList α)
    (credit : Nat) (initial : queue.2.length ≤ credit) :
    (Resources.run linearStep commands queue).2 ≤ credit +
      FIFOContracts.abstractBudget (fun _ _ => 2) commands (twoListDecode queue) :=
  linear_client_bound commands queue credit initial

theorem source_no_local_state_potential (default value : α) (potential : TwoList α → Nat) :
    ¬ ∃ charge : Nat, ∀ queue, EnqueueReachable queue →
      (peekStepUsing ListReversal.naiveRun default queue).2 +
          potential (peekStepUsing ListReversal.naiveRun default queue).1 ≤
        potential queue + charge :=
  source_no_uniform_peek_charge default value potential

theorem source_no_initial_credit_escape (default value : α)
    (credit : TwoList α → Nat) (charge : Nat) :
    ∃ queue, EnqueueReachable queue ∧ ∃ count, 0 < count ∧
      credit queue + charge * count < (runPeeksUsing ListReversal.naiveRun default count queue).2 :=
  source_peeks_exceed_initial_credit default value credit charge

theorem linear_no_initial_credit_escape (default value : α)
    (credit : TwoList α → Nat) (charge : Nat) :
    ∃ queue, EnqueueReachable queue ∧ ∃ count, 0 < count ∧
      credit queue + charge * count <
        (runPeeksUsing (fun values => SymmetricCosts.reverseRun values []) default count queue).2 :=
  linear_peeks_exceed_initial_credit default value credit charge

/-- An always nonempty family, constructed by the source enqueue executor. -/
def backFamily (n : Nat) (value : α) : TwoList α := ([], List.replicate (n + 1) value)

theorem backFamily_reachable (n : Nat) (value : α) : EnqueueReachable (backFamily n value) :=
  replicate_reachable (n + 1) value

theorem backFamily_linear_cost (n : Nat) (default value : α) :
    (linearPeekRun default (backFamily n value)).2 = n + 3 := by
  simp [backFamily, List.replicate_succ, linearPeekRun_back]

theorem backFamily_source_double_cost (n : Nat) (default value : α) :
    2 * (peekRun default (backFamily n value)).2 = (n + 2) * (n + 3) + 2 := by
  simpa [backFamily, List.replicate_succ] using
    peekRun_back_double_cost default value (List.replicate n value)

theorem backFamily_source_quadratic_lower (n : Nat) (default value : α) :
    n * n ≤ 2 * (peekRun default (backFamily n value)).2 := by
  rw [backFamily_source_double_cost]
  nlinarith

theorem backFamily_source_quadratic_upper (n : Nat) (default value : α) (large : 1 ≤ n) :
    (peekRun default (backFamily n value)).2 ≤ 10 * (n * n) := by
  have exactCount := backFamily_source_double_cost n default value
  nlinarith

theorem source_peek_quadratic_growth (default value : α) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((peekRun default (backFamily n value)).2 : ℝ))
      (fun n : Nat => ((n * n : Nat) : ℝ)) := by
  apply isBigO_of_nat_bound _ (fun n => n * n) 10 1
  intro n hn
  exact backFamily_source_quadratic_upper n default value hn

theorem linear_peek_linear_growth (default value : α) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((linearPeekRun default (backFamily n value)).2 : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  apply isBigO_of_nat_bound _ (fun n => n) 4 1
  intro n hn
  rw [backFamily_linear_cost]
  omega

/-! ## Actual first erasure, including the unique-list table carrier -/

theorem first_match_stops :
    ListErase.run (fun n : Nat => decide (n = 2)) [1, 2, 2, 3] = ([1, 2, 3], 2) := by
  simpa using ListErase.run_first_hit (fun n : Nat => decide (n = 2)) [1] 2 [2, 3]
    (by simp) (by decide)

theorem raw_repeated_key_update :
    ListErase.pairSetRun 2 "new" [(1, "one"), (2, "old"), (2, "shadowed")] =
      ([(2, "new"), (1, "one"), (2, "shadowed")], 2) := rfl

def unsortedUnique : UniqueList Nat String :=
  ⟨[(2, "two"), (1, "one")], by decide⟩

theorem unique_front_update :
    (ListErase.setRun 2 "new" unsortedUnique).1.1 = [(2, "new"), (1, "one")] ∧
    (ListErase.setRun 2 "new" unsortedUnique).2 = 1 := by
  rw [ListErase.setRun_entries, ListErase.setRun_comparisons]
  change (ListErase.pairSetRun 2 "new" [(2, "two"), (1, "one")]).1 = _ ∧
    (ListErase.pairSetRun 2 "new" [(2, "two"), (1, "one")]).2 = _
  rw [ListErase.pairSetRun_front]
  exact ⟨rfl, rfl⟩

theorem unique_absent_update :
    (ListErase.setRun 3 "three" unsortedUnique).1.1 = [(3, "three"), (2, "two"), (1, "one")] ∧
    (ListErase.setRun 3 "three" unsortedUnique).2 = 2 := by
  rw [ListErase.setRun_entries, ListErase.setRun_comparisons]
  have absent : ∀ binding ∈ unsortedUnique.1, 3 ≠ binding.1 := by
    simp [unsortedUnique]
  rw [ListErase.pairSetRun_absent 3 "three" unsortedUnique.1 absent]
  exact ⟨rfl, rfl⟩

def rangeBindings (n : Nat) (value : α) : List (Nat × α) :=
  (List.range n).map (fun key => (key, value))

theorem rangeBindings_unique (n : Nat) (value : α) :
    ((rangeBindings n value).map Prod.fst).Nodup := by
  simpa [rangeBindings, List.map_map, Function.comp_def] using (List.nodup_range (n := n))

theorem rangeBindings_absent (n : Nat) (value : α) :
    ∀ binding ∈ rangeBindings n value, n ≠ binding.1 := by
  intro binding member
  change binding ∈ (List.range n).map (fun key => (key, value)) at member
  rcases List.mem_map.mp member with ⟨key, keyMember, rfl⟩
  have less := List.mem_range.mp keyMember
  change n ≠ key
  omega

def uniqueRange (n : Nat) (value : α) : UniqueList Nat α :=
  ⟨rangeBindings n value, rangeBindings_unique n value⟩

theorem unique_update_worst_case (n : Nat) (old value : α) :
    (ListErase.setRun n value (uniqueRange n old)).1.1 = (n, value) :: rangeBindings n old ∧
    (ListErase.setRun n value (uniqueRange n old)).2 = n := by
  rw [ListErase.setRun_entries, ListErase.setRun_comparisons]
  change (ListErase.pairSetRun n value (rangeBindings n old)).1 = _ ∧
    (ListErase.pairSetRun n value (rangeBindings n old)).2 = _
  rw [ListErase.pairSetRun_absent n value (rangeBindings n old) (rangeBindings_absent n old)]
  simp [rangeBindings]

theorem unique_update_linear_growth (old value : α) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((ListErase.setRun n value (uniqueRange n old)).2 : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  apply isBigO_of_nat_bound _ (fun n => n) 1 0
  intro n _
  rw [(unique_update_worst_case n old value).2]
  simp

theorem unique_update_no_uniform_bound (old value : α) (charge : Nat) :
    charge < (ListErase.setRun (charge + 1) value (uniqueRange (charge + 1) old)).2 := by
  rw [(unique_update_worst_case _ old value).2]
  exact Nat.lt_succ_self charge

theorem unique_update_erases [DecidableEq κ] (key : κ) (value : α) (bindings : UniqueList κ α) :
    (ListErase.setRun key value bindings).1 =
      Search.OrderedMap.AssociationListEnumeration.set key value bindings :=
  ListErase.setRun_value key value bindings

theorem unique_update_AList_bridge [DecidableEq κ] (key : κ) (value : α)
    (bindings : UniqueList κ α) :
    Search.OrderedMap.AssociationListEnumeration.toAList (ListErase.setRun key value bindings).1 =
      AList.insert key value (Search.OrderedMap.AssociationListEnumeration.toAList bindings) :=
  ListErase.setRun_toAList key value bindings

/-- Values can themselves be types; resource observations remain natural numbers. -/
theorem type_valued_queue (default first second : Type u) :
    peekRun default ([first], [second]) = (first, 1) := rfl

theorem type_valued_unique_update (key : Nat) (value : Type u) (bindings : UniqueList Nat (Type u)) :
    (ListErase.setRun key value bindings).1 =
      Search.OrderedMap.AssociationListEnumeration.set key value bindings ∧
    (ListErase.setRun key value bindings).2 ≤ bindings.1.length :=
  ⟨ListErase.setRun_value _ _ _, ListErase.setRun_comparisons_le _ _ _⟩

/-! ## Bridges to the chapter's exact source-facing wrappers -/

theorem source_list_enqueue (queue : List Nat) (value : Nat) :
    (listEnqueueRun queue value).1 = AbstractDataTypes.ListQueue.enq queue value :=
  listEnqueueRun_value queue value

theorem source_pair_enqueue (queue : TwoList Nat) (value : Nat) :
    (enqueueRun queue value).1 = AbstractDataTypes.TwoListQueueAbs.enq queue value := rfl

theorem source_pair_peek (default : Nat) (queue : TwoList Nat) :
    (peekRun default queue).1 = AbstractDataTypes.TwoListQueueAbs.peek default queue :=
  peekRun_value default queue

theorem source_pair_linear_peek (default : Nat) (queue : TwoList Nat) :
    (linearPeekRun default queue).1 = AbstractDataTypes.TwoListQueueAbs.peek default queue :=
  linearPeekRun_value default queue

theorem source_pair_dequeue (queue : TwoList Nat) :
    (dequeueRun queue).1 = AbstractDataTypes.TwoListQueueAbs.deq queue :=
  dequeueRun_value queue

theorem source_pair_linear_dequeue (queue : TwoList Nat) :
    (linearDequeueRun queue).1 = AbstractDataTypes.TwoListQueueAbs.deq queue :=
  linearDequeueRun_value queue

theorem source_history_peek (default : Nat) (commands : List (Command Nat)) (queue : TwoList Nat) :
    (peekRun default (Resources.run linearStep commands queue).1).1 =
      AbstractDataTypes.TwoListQueueAbs.peek default
        (Sequences.AbstractFIFO.run (twoListFIFO Nat) commands queue) := by
  rw [linearRun_value, source_pair_peek]

theorem source_unique_update (key : Nat) (value : α) (bindings : AbstractDataTypes.ListsETable.table α) :
    (ListErase.setRun key value bindings).1 = AbstractDataTypes.ListsETable.set key value bindings :=
  ListErase.setRun_value key value bindings

theorem source_unique_update_elements (key : Nat) (value : α)
    (bindings : AbstractDataTypes.ListsETable.table α) :
    (ListErase.setRun key value bindings).1.1 =
      AbstractDataTypes.ListsETable.elements (AbstractDataTypes.ListsETable.set key value bindings) :=
  congrArg Subtype.val (ListErase.setRun_value key value bindings)

/-- The measured output supports the source get/bound laws even when value is default. -/
theorem source_measured_update_lookup (default value : α) (key : Nat)
    (bindings : AbstractDataTypes.ListsETable.table α) :
    AbstractDataTypes.ListsETable.bound key (ListErase.setRun key value bindings).1 = true ∧
      AbstractDataTypes.ListsETable.get default key (ListErase.setRun key value bindings).1 = value := by
  apply AbstractDataTypes.ListsETable.correct default value key (ListErase.setRun key value bindings).1
  change (key, value) ∈ (ListErase.setRun key value bindings).1.1
  rw [ListErase.setRun_entries, ListErase.pairSetRun_value]
  exact List.mem_cons_self

end Examples.AbstractDataTypeWork
