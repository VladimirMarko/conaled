import Applications.Search.RectangleSweep.MeasuredBalanced
import Applications.Search.RectangleSweep.ActiveCardinality
import Applications.Trees.HeightBalance.HeightBound
import Applications.Resources.Growth

/-!
# Finite admitted support and complete measured rectangle-sweep work

The support set is proof-only. The actual executor is unchanged: it generates
and sorts once, then queries and updates the returned balanced states until a
hit or exhaustion. The closed invariant applies to every admitted state, not
only to the mathematical full-prefix fold. Strict complete-key inorder connects
finite occurrence support to node count; shape balance then bounds actual height.

The resulting bound counts the declared source events, not machine time or bit
complexity. Source correspondence: `docs/research/fdsa-measured-rectangle-scan.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep.MeasuredBalanced
universe u v
variable {α : Type u} {β : Type v}
section Inputs
variable [LE α] [LinearOrder β]

/-- Complete keys preserve every input occurrence even for equal rectangles. -/
def inputKeys (rs : List (Rectangle α β)) : Set (Key α) :=
  Set.range (occurrenceKey rs)

theorem inputKeys_finite (rs : List (Rectangle α β)) : (inputKeys rs).Finite :=
  Set.finite_range (occurrenceKey rs)

theorem inputKeys_ncard (rs : List (Rectangle α β)) : (inputKeys rs).ncard = rs.length := by
  simpa only [inputKeys, Nat.card_fin] using
    Set.ncard_range_of_injective (occurrenceKey_injective rs)

theorem occurrenceKey_mem_inputKeys (rs : List (Rectangle α β)) (i : Fin rs.length) :
    occurrenceKey rs i ∈ inputKeys rs := ⟨i, rfl⟩

theorem event_key_mem_inputKeys (rs : List (Rectangle α β)) (e : Event α β)
    (mem : e ∈ events rs) : e.completeKey ∈ inputKeys rs := by
  rcases (mem_events_iff rs e).mp mem with ⟨kind, i, rfl⟩
  exact occurrenceKey_mem_inputKeys rs i

end Inputs
variable [LinearOrder α] [OrderBot α] [LinearOrder β]

/-- Full balanced-set validity and finite input support, without a prefix claim. -/
def Admitted (rs : List (Rectangle α β)) (t : Tree α) : Prop :=
  IntervalTree.Balanced.Valid keyInterval t ∧
    Trees.setTree (Trees.Cached.erase t) ⊆ inputKeys rs

theorem admitted_nil (rs : List (Rectangle α β)) : Admitted rs .nil := by
  refine ⟨(IntervalTree.Balanced.setLaws keyInterval).empty_valid, ?_⟩
  intro key mem
  exact ((IntervalTree.Balanced.setLaws keyInterval).empty key mem).elim

theorem insertRun_admitted (rs : List (Rectangle α β)) (key : Key α) (t : Tree α)
    (allowed : key ∈ inputKeys rs) (admitted : Admitted rs t) :
    Admitted rs (insertRun key t).1 := by
  refine ⟨insertRun_valid key t admitted.1, ?_⟩
  intro x mem
  rw [insertRun_value] at mem
  rcases ((IntervalTree.Balanced.setLaws keyInterval).insert key t admitted.1 x).mp mem with
    equal | old
  · exact equal.symm ▸ allowed
  · exact admitted.2 old

/-- Deletion preserves input support even for an unsupported deletion key. -/
theorem deleteRun_admitted (rs : List (Rectangle α β)) (key : Key α) (t : Tree α)
    (admitted : Admitted rs t) : Admitted rs (deleteRun key t).1 := by
  refine ⟨deleteRun_valid key t admitted.1, ?_⟩
  intro x mem
  rw [deleteRun_value] at mem
  exact admitted.2 (((IntervalTree.Balanced.setLaws keyInterval).delete key t admitted.1 x).mp mem).2

theorem admitted_numNodes_le (rs : List (Rectangle α β)) (t : Tree α)
    (admitted : Admitted rs t) : t.numNodes ≤ rs.length := by
  rw [← balanced_observe_ncard_eq_numNodes t admitted.1.2, ← inputKeys_ncard rs]
  exact Set.ncard_le_ncard admitted.2 (inputKeys_finite rs)

/-- This uses the erased shape, without reading or trusting a stored height. -/
theorem admitted_height_le (rs : List (Rectangle α β)) (t : Tree α)
    (admitted : Admitted rs t) : t.height ≤ 2 * Nat.clog 2 (rs.length + 1) := by
  have height := Trees.HeightBalance.height_le_mul_clog_numNodes_add_one
    1 (Trees.Cached.erase t) admitted.1.1.1
  simp only [Trees.Cached.height_erase, Trees.Cached.numNodes_erase, Nat.reduceAdd] at height
  exact height.trans (Nat.mul_le_mul_left 2
    (Nat.clog_mono_right 2 (Nat.add_le_add_right (admitted_numNodes_le rs t admitted) 1)))

theorem insertRun_admitted_cost_le (rs : List (Rectangle α β)) (key : Key α) (t : Tree α)
    (admitted : Admitted rs t) :
    (insertRun key t).2 ≤ 86 * Nat.clog 2 (rs.length + 1) + 8 := by
  have work := insertRun_cost_le key t
  have height := admitted_height_le rs t admitted
  omega

theorem splitMaxRun_admitted_cost_le (rs : List (Rectangle α β)) (t : Tree α)
    (admitted : Admitted rs t) :
    (splitMaxRun t).2 ≤ 62 * Nat.clog 2 (rs.length + 1) + 1 := by
  have work := splitMaxRun_cost_le t
  have height := admitted_height_le rs t admitted
  omega

theorem deleteRun_admitted_cost_le (rs : List (Rectangle α β)) (key : Key α) (t : Tree α)
    (admitted : Admitted rs t) :
    (deleteRun key t).2 ≤ 86 * Nat.clog 2 (rs.length + 1) + 1 := by
  have work := deleteRun_cost_le key t
  have height := admitted_height_le rs t admitted
  omega

/-- The query interval need not be projected from an input occurrence. -/
theorem queryRun_admitted_cost_le (rs : List (Rectangle α β)) (t : Tree α)
    (query : IntervalKey α) (admitted : Admitted rs t) :
    (queryRun t query).2 ≤ 10 * Nat.clog 2 (rs.length + 1) + 1 := by
  have work := queryRun_cost_le t query
  have height := admitted_height_le rs t admitted
  omega

/-- Every reached returned state stays admitted; early return reduces this envelope. -/
theorem scanRun_events_cost_le_admitted (rs : List (Rectangle α β)) (t : Tree α)
    (admitted : Admitted rs t) :
    (scanRun t (events rs)).2 ≤
      182 * rs.length * Nat.clog 2 (rs.length + 1) + 12 * rs.length + 1 := by
  have work := Search.RectangleSweep.scanRun_events_cost_le (AddMonoidHom.id Nat)
    insertRun deleteRun queryRun 1 1 (fun key => key ∈ inputKeys rs) (Admitted rs)
    (insertRun_admitted rs) (fun key state _ valid => deleteRun_admitted rs key state valid)
    (10 * Nat.clog 2 (rs.length + 1) + 1)
    (86 * Nat.clog 2 (rs.length + 1) + 8)
    (86 * Nat.clog 2 (rs.length + 1) + 1)
    (fun key state _ valid => insertRun_admitted_cost_le rs key state valid)
    (fun key state _ valid => deleteRun_admitted_cost_le rs key state valid)
    (fun key state _ valid => queryRun_admitted_cost_le rs state (keyInterval key) valid)
    rs (event_key_mem_inputKeys rs) t admitted
  change (scanRun t (events rs)).2 ≤
    2 * rs.length * 1 +
      rs.length * ((10 * Nat.clog 2 (rs.length + 1) + 1) +
        (86 * Nat.clog 2 (rs.length + 1) + 8)) +
      rs.length * (86 * Nat.clog 2 (rs.length + 1) + 1) + 1 at work
  convert work using 1
  ring

/-- All-input work includes positive generation, sorting and terminal overheads. -/
theorem sweepRun_cost_le (rs : List (Rectangle α β)) :
    (sweepRun rs).2 ≤ 24 * rs.length * Nat.clog 2 (2 * rs.length) +
      182 * rs.length * Nat.clog 2 (rs.length + 1) + 40 * rs.length + 8 := by
  rw [sweepRun_cost]
  have sorting := sortEventsRun_raw_cost_le rs
  have scanning := scanRun_events_cost_le_admitted rs .nil (admitted_nil rs)
  omega

private theorem clog_double_le (n : Nat) : Nat.clog 2 (2 * n) ≤ Nat.clog 2 n + 1 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  calc
    2 * n ≤ 2 * 2 ^ Nat.clog 2 n :=
      Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by decide) n)
    _ = 2 ^ (Nat.clog 2 n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

private theorem clog_succ_le (n : Nat) (hn : 1 ≤ n) :
    Nat.clog 2 (n + 1) ≤ Nat.clog 2 n + 1 :=
  (Nat.clog_mono_right 2 (by omega : n + 1 ≤ 2 * n)).trans (clog_double_le n)

theorem sweepRun_cost_le_clog_succ (rs : List (Rectangle α β)) (hn : 1 ≤ rs.length) :
    (sweepRun rs).2 ≤ 278 * rs.length * Nat.clog 2 (rs.length + 1) := by
  have work := sweepRun_cost_le rs
  have logs : Nat.clog 2 (2 * rs.length) ≤ Nat.clog 2 (rs.length + 1) + 1 :=
    (clog_double_le rs.length).trans
      (Nat.add_le_add_right (Nat.clog_mono_right 2 (Nat.le_succ rs.length)) 1)
  have positive : 1 ≤ Nat.clog 2 (rs.length + 1) :=
    Nat.clog_pos (by decide) (by omega)
  have sorting := Nat.mul_le_mul_left (24 * rs.length) logs
  have absorb := Nat.mul_le_mul_left rs.length positive
  nlinarith

/-- The n log n envelope is eventual; it is deliberately not asserted at nil. -/
theorem sweepRun_cost_le_clog (rs : List (Rectangle α β)) (hn : 2 ≤ rs.length) :
    (sweepRun rs).2 ≤ 456 * rs.length * Nat.clog 2 rs.length := by
  have work := sweepRun_cost_le rs
  have sorting := Nat.mul_le_mul_left (24 * rs.length) (clog_double_le rs.length)
  have scanning := Nat.mul_le_mul_left (182 * rs.length) (clog_succ_le rs.length (by omega))
  have positive : 1 ≤ Nat.clog 2 rs.length := Nat.clog_pos (by decide) hn
  have absorb := Nat.mul_le_mul_left rs.length positive
  nlinarith

/-- Ordinary real asymptotics for the actual complete executor at fixed tariff. -/
theorem sweepRun_isBigO (inputs : Nat → List (Rectangle α β))
    (sizes : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => ((sweepRun (inputs n)).2 : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 456) (N := 2)
  intro n hn
  have work := sweepRun_cost_le_clog (inputs n) (by simpa only [sizes n] using hn)
  simpa only [sizes n, Nat.mul_assoc] using work

end Search.RectangleSweep.MeasuredBalanced
