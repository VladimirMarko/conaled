import Applications.Resources.RetainedFirstHit

/-! Ordered prefix sums for [0,2,0,3] are [0,2,2,5]. The duplicate 2 must
remain: thresholds 1 and 2 first stop at index 2, not index 3. -/
namespace Examples.RetainedFirstHit
open Resources Resources.FirstHitScan Resources.FirstHitScan.Retained

def read : Nat → Nat := arrayRead #[0,2,0,3]
def thresholds : List Nat := [2,1,5,0,6,2]
def history := updates read 4 0 0 thresholds []

theorem alternating_outputs : history.map Result.out =
    [(2,2),(2,2),(4,5),(0,0),(4,5),(2,2)] := by decide

theorem alternating_cache : history.map Result.cache =
    [[0,2],[0,2],[0,2,2,5],[0,2,2,5],[0,2,2,5],[0,2,2,5]] := by decide

theorem alternating_reads : history.map Result.reads = [2,0,2,0,0,0] := by decide

theorem alternating_costs : history.map Result.cost = [33,29,55,7,51,29] := by decide

theorem fresh_outputs :
    thresholds.map (fun t => (native 4 read (0,(0,t))).1) =
      [(2,2),(2,2),(4,5),(0,0),(4,5),(2,2)] := by
  rw [← updates_outputs read 4 0 0 thresholds [] trivial]
  exact alternating_outputs

theorem history_invariant : ∀ r ∈ history, Valid read 0 0 r.cache ∧
    ∃ t ∈ thresholds, FirstHit read 4 (0,(0,t)) r.steps r.out ∧
      native 4 read (0,(0,t)) = (r.out,(r.steps+1)*7+r.steps*3) :=
  updates_correct read 4 0 0 thresholds [] trivial

theorem whole_sequence_reads : (history.map Result.reads).sum ≤ 4 :=
  total_reads_bound read 4 0 0 thresholds

theorem whole_sequence_bill : (history.map Result.cost).sum + initialCache.2 = 205 ∧
    (history.map (fun r => (r.steps+1)*7+r.steps*3)).sum = 182 ∧
    storage (finalCache read 4 0 0 thresholds []) = 13 := by decide

theorem first_hit_minimal : FirstHit read 4 (0,(0,2)) 2 (2,2) := by
  exact
    (repair_correct read 4 0 0 2 [] trivial).1

theorem later_equal_prefix_rejected : ¬FirstHit read 4 (0,(0,2)) 3 (3,2) := by
  intro h
  have := h.2.2.2 2 (by decide)
  have bad : 2 < 2 := this.2
  omega

theorem supplied_start :
    (repair read 3 1 7 9 []).out = (2,9) ∧
    (repair read 3 1 7 9 []).cache = [9] := by decide

theorem supplied_start_correct : FirstHit read 4 (1,(7,9)) 1 (2,9) := by
  exact
    (repair_correct read 3 1 7 9 [] trivial).1

theorem immediate : repair read 3 1 7 7 [] = ⟨(1,7),[],0,0,7⟩ := by decide

theorem exhausted : repair read 0 4 1 8 [] = ⟨(4,1),[],0,0,7⟩ := rfl

theorem empty : repair (arrayRead #[]) 0 0 1 8 [] = ⟨(0,1),[],0,0,7⟩ := rfl

theorem last_entry : (repair read 4 0 0 5 []).out = (4,5) ∧
    (repair read 4 0 0 6 []).out = (4,5) := by decide

/-- An arbitrary number of updates reuses the library's finite-sequence bound. -/
theorem repeated_threshold_reads (ts : List Nat) :
    ((updates read 4 0 0 ts []).map Result.reads).sum ≤ 4 :=
  total_reads_bound read 4 0 0 ts

theorem reused_cells : (repair read 4 0 0 5 [0,2]).reads = 2 ∧
    (repair read 4 0 0 2 [0,2,2,5]).reads = 0 ∧
    (repair read 4 0 0 5 []).reads = 4 := by decide

/-- Deduplication changes the indexed invariant, even when sums coincide. -/
theorem deduplicated_cache_rejected : ¬Valid read 0 0 [0,2,5] := by
  simp only [Valid]
  decide

/-- Retaining just the old stop cannot answer a decrease by resuming there. -/
theorem resume_old_stop_rejected :
    (repair read 0 4 5 2 []).out ≠ (repair read 4 0 0 2 [0,2,2,5]).out := by decide

/-- A store edit requires a different repair law, not this fixed-store theorem. -/
theorem stale_store_rejected : ¬Valid (fun _ => 0) 0 0 [0,2] ∧
    (repair (fun _ => 0) 4 0 0 2 [0,2]).out ≠
      (repair (fun _ => 0) 4 0 0 2 []).out := by
  simp only [Valid]
  decide

theorem finite_view :
    (compiled 4 (finiteRead (fun j : Fin 4 => (#[0,2,0,3] : Array Nat)[j]))
      (0,(0,5))).1 = (repair read 4 0 0 5 [0,2]).out := by
  apply representation_recovery 4 0 0 5 (by decide) read _ _ [0,2] (by simp only [Valid]; decide)
  intro j hj
  exact (array_reads #[0,2,0,3] j hj).symm

theorem stateful_boundary :
    Incremental.Stateful.Laws (fun t => (native 4 read (0,(0,t))).1)
      (stateful read 4 0 0) (StateValid read 4 0 0) := stateful_laws read 4 0 0

end Examples.RetainedFirstHit
