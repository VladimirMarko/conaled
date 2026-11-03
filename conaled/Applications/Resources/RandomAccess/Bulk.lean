import Applications.Resources.RandomAccess.Lookup

/-! Ordered measured updates with exact source loop accounting.
Provenance and statement review: `docs/research/adwh-random-access-costs.md`. -/
namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

/-- Sequential left-to-right updates from Answer 3.12, with one loop visit each. -/
def bulkStep (p : Nat × α) (ds : RAList α) : Measured (RAList α) Nat :=
  let next := updateRARun p.1 p.2 ds
  (next.1, next.2 + 1)

def bulkRun (ds : RAList α) (us : List (Nat × α)) : Measured (RAList α) Nat := run bulkStep us ds

@[simp] theorem bulkRun_nil (ds : RAList α) : bulkRun ds [] = (ds, 0) := rfl

/-- Exact source recurrence, including its one loop visit after each update. -/
theorem bulkRun_cons (ds : RAList α) (k : Nat) (x : α) (us : List (Nat × α)) :
    bulkRun ds ((k,x) :: us) =
      let next := updateRARun k x ds
      let rest := bulkRun next.1 us
      (rest.1, next.2 + rest.2 + 1) := by
  simp [bulkRun, run, bind, bulkStep, Nat.add_assoc, Nat.add_comm]

def bulk (ds : RAList α) (us : List (Nat × α)) : RAList α :=
  us.foldl (fun ys p => updateRA p.1 p.2 ys) ds

theorem bulkRun_value (ds : RAList α) (us : List (Nat × α)) :
    (bulkRun ds us).1 = bulk ds us := by
  rw [bulkRun, run_state]
  simp only [bulkStep, updateRARun_value, bulk]

theorem bulk_valid {r : Nat} {ds : RAList α} (h : Valid r ds) (us : List (Nat × α)) :
    Valid r (bulk ds us) := by
  rw [← bulkRun_value]
  exact run_invariant bulkStep (Valid r)
    (fun p ds h => by simpa [bulkStep, updateRARun_value] using valid_updateRA h p.1 p.2) us ds h

theorem bulk_refinement {r : Nat} {ds : RAList α} (h : Valid r ds)
    (us : List (Nat × α)) :
    fromRA (bulk ds us) = us.foldl (fun ys p => ys.set p.1 p.2) (fromRA ds) := by
  rw [← bulkRun_value]
  exact run_value_fusion bulkStep (fun p xs => xs.set p.1 p.2) fromRA (Valid r)
    (fun p ds h => by simpa [bulkStep, updateRARun_value] using valid_updateRA h p.1 p.2)
    (fun p ds h => by simpa [bulkStep] using updateRARun_refinement h p.1 p.2) us ds h

theorem bulkRun_count_bound {r : Nat} {ds : RAList α} (h : Valid r ds)
    (us : List (Nat × α)) :
    (bulkRun ds us).2 ≤ us.length * (r + 2 * ds.length + 2) := by
  induction us generalizing ds with
  | nil => simp [bulkRun_nil]
  | cons p us ih =>
    obtain ⟨k, x⟩ := p
    have hv : Valid r (updateRARun k x ds).1 := by
      rw [updateRARun_value]; exact valid_updateRA h k x
    have hr := ih hv
    have hc := fetchRARun_count_bound h k
    rw [← updateRARun_count k x ds] at hc
    simp only [updateRARun_value, updateRA_digit_length] at hr
    simp only [bulkRun_cons, List.length_cons, Nat.add_mul, Nat.one_mul, updateRARun_value]
    omega

theorem bulkRun_log_bound {ds : RAList α} (h : Inv ds) (us : List (Nat × α)) :
    (bulkRun ds us).2 ≤ us.length * (2 * (fromRA ds).length.log2 + 4) := by
  have hc := bulkRun_count_bound h us
  have hl := digits_log_bound h
  have hm := Nat.mul_le_mul_left us.length
    (show 0 + 2 * ds.length + 2 ≤ 2 * (fromRA ds).length.log2 + 4 by omega)
  omega

theorem bulk_last_count {r : Nat} {ds : RAList α} (h : Valid r ds)
    (hne : ds ≠ []) (xs : List α) :
    (bulkRun ds (xs.map (fun x => ((fromRA ds).length - 1, x)))).2 =
      xs.length * (r + 2 * ds.length + 1) := by
  induction xs generalizing ds with
  | nil => simp [bulkRun_nil]
  | cons x xs ih =>
    let k := (fromRA ds).length - 1
    let next := updateRA k x ds
    have hv : Valid r next := valid_updateRA h k x
    have hn : next ≠ [] := updateRA_ne_nil k x hne
    have hd : next.length = ds.length := updateRA_digit_length k x ds
    have hl : (fromRA next).length = (fromRA ds).length := by
      rw [updateRA_refinement h]
      simp
    have hr := ih hv hn
    rw [hd, hl] at hr
    have hc := fetchRARun_last_count h hne
    simp only [List.map_cons, bulkRun_cons, updateRARun_value, updateRARun_count]
    change (fetchRARun k ds).2 +
      (bulkRun next (xs.map (fun x => ((fromRA ds).length - 1, x)))).2 + 1 = _
    rw [hr]
    change (fetchRARun ((fromRA ds).length - 1) ds).2 + _ + 1 = _
    rw [hc]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Matching worst-case logarithmic cost on every nonempty valid representation. -/
theorem bulk_last_log_exact {ds : RAList α} (h : Inv ds) (hne : ds ≠ []) (xs : List α) :
    (bulkRun ds (xs.map (fun x => ((fromRA ds).length - 1, x)))).2 =
      xs.length * (2 * (fromRA ds).length.log2 + 3) := by
  rw [bulk_last_count h hne, digits_log_exact h hne]
  congr 1
  omega


end Resources.RandomAccessCosts
