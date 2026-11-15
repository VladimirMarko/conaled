import Applications.Resources.RandomSelection

/-! The finite fresh-occurrence quickselect execution.

Each active invocation samples one current occurrence and executes `stepRun`.
Only its selected strict child is run; the equal branch returns directly. The
trace records actual active sizes and occurrence indices. Source calls are a
separate observation of the same execution. Strict length decrease constructs
the PMF without an almost-sure termination assumption or a truncating fuel.

Empty calls cost one entry and one empty-length traversal. Valid ranks never
reach that empty continuation. Invalid public rank zero is an explicit free
boundary failure; positive public ranks use the existing one-based convention.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open Applications.Selection
universe u
variable {α : Type u}

/-- Each pair records active length and the sampled occurrence index. -/
abbrev Trace := List (Nat × Nat)

/-- Returned optional value, actual choice trace, and source calls. -/
abbrev Outcome (α : Type u) := Measured (Option α) (Trace × Nat)

/-- Actual scan volume, independently of the source-call observation. -/
def scanVolume (trace : Trace) : Nat := (trace.map Prod.fst).sum

@[simp] theorem scanVolume_nil : scanVolume [] = 0 := rfl

@[simp] theorem scanVolume_cons (n i : Nat) (trace : Trace) :
    scanVolume ((n, i) :: trace) = n + scanVolume trace := rfl

/-- Prepend this executed step and add its actual local calls to its one child. -/
def prepend (n i calls : Nat) (result : Outcome α) : Outcome α :=
  (result.1, ((n, i) :: result.2.1, calls + result.2.2))

section Ordered
variable [LinearOrder α]

noncomputable section

/-- Fresh conditional uniform occurrence choices, with one recursive child.
The invalid zero-based extension may reach an empty state and return `none`. -/
def run : Nat → List α → PMF (Outcome α)
  | _, [] => PMF.pure (none, ([], (SymmetricCosts.lengthRun ([] : List α)).2 + 1))
  | k, head :: tail =>
      PMF.bind (RandomQuickSort.uniformIndex tail.length) fun i =>
        let action := stepRun k (head :: tail) i
        match _hstep : action.1 with
        | Sum.inl (j, ys) =>
            PMF.map (prepend (head :: tail).length i.val action.2) (run j ys)
        | Sum.inr p => PMF.pure (some p, ([((head :: tail).length, i.val)], action.2))
termination_by _ xs => xs.length
decreasing_by
  exact (stepRun_child k (head :: tail) i j ys _hstep).1

@[simp] theorem run_nil (k : Nat) :
    run k ([] : List α) = PMF.pure (none, ([], 2)) := by
  rw [run]
  rfl

/-- The exact probability-tree equation retains the actual measured step. -/
theorem run_cons (k : Nat) (head : α) (tail : List α) :
    run k (head :: tail) =
      PMF.bind (RandomQuickSort.uniformIndex tail.length) fun i =>
        let action := stepRun k (head :: tail) i
        match action.1 with
        | Sum.inl (j, ys) =>
            PMF.map (prepend (head :: tail).length i.val action.2) (run j ys)
        | Sum.inr p => PMF.pure (some p, ([((head :: tail).length, i.val)], action.2)) := by
  rw [run]
  apply congrArg (PMF.bind _)
  funext i
  dsimp only
  split <;> rename_i hstep <;> simp only [hstep]

/-- All supported choices return the same sorted-index specification. This
includes the total invalid-rank extension, not just successful calls. -/
theorem run_value (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) : result.1 = (ordered xs)[k]? := by
  match xs with
  | [] =>
      have he : result = (none, ([], 2)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      subst result
      simp [ordered]
  | head :: tail =>
      rw [run_cons] at hr
      obtain ⟨i, _, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      dsimp only at hr
      have hs := stepRun_semantics k (head :: tail) i
      cases hstep : (stepRun k (head :: tail) i).1 with
      | inl state =>
          rcases state with ⟨j, ys⟩
          rw [hstep] at hr hs
          obtain ⟨child, hc, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
          have hv := run_value j ys child hc
          rw [← he]
          exact hv.trans hs
      | inr p =>
          rw [hstep] at hr hs
          have he : result =
              (some p, ([((head :: tail).length, i.val)], (stepRun k (head :: tail) i).2)) :=
            (PMF.mem_support_pure_iff _ _).mp hr
          rw [he]
          exact hs
termination_by xs.length
decreasing_by
  exact (stepRun_child k (head :: tail) i j ys hstep).1

theorem run_ranked (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) (a : α) (ha : result.1 = some a) :
    RankedAt xs k a :=
  ranked_iff_index.mpr ((run_value k xs result hr).symm.trans ha)

theorem run_none (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) : result.1 = none ↔ xs.length ≤ k := by
  rw [run_value k xs result hr, List.getElem?_eq_none_iff, (ordered_perm xs).length_eq]

/-- Every outcome of a valid zero-based request is successful and has that
occurrence rank. Child validity follows from `stepRun_child`, without `Nodup`. -/
theorem run_valid (k : Nat) (xs : List α) (hk : k < xs.length)
    (result : Outcome α) (hr : result ∈ (run k xs).support) :
    ∃ a, result.1 = some a ∧ RankedAt xs k a := by
  cases ha : result.1 with
  | none =>
      have hn := (run_none k xs result hr).mp ha
      omega
  | some a => exact ⟨a, rfl, run_ranked k xs result hr a ha⟩

private theorem run_support_bounds (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    result.2.1.length ≤ xs.length ∧
      xs.length ≤ scanVolume result.2.1 ∧
      2 * scanVolume result.2.1 ≤ xs.length * (xs.length + 1) ∧
      scanVolume result.2.1 ≤ result.2.2 ∧
      result.2.2 ≤ 9 * scanVolume result.2.1 + 2 ∧
      ∀ entry ∈ result.2.1, 0 < entry.1 ∧ entry.2 < entry.1 ∧ entry.1 ≤ xs.length := by
  match xs with
  | [] =>
      have he : result = (none, ([], 2)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      subst result
      simp
  | head :: tail =>
      rw [run_cons] at hr
      obtain ⟨i, _, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      dsimp only at hr
      have hi := i.isLt
      have hn : 0 < (head :: tail).length := by simp
      have hl := stepRun_cost_bounds k (head :: tail) i
      cases hstep : (stepRun k (head :: tail) i).1 with
      | inl state =>
          rcases state with ⟨j, ys⟩
          rw [hstep] at hr
          obtain ⟨child, hc, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
          obtain ⟨hcount, hinitial, hvolume, hlower, hupper, hentries⟩ :=
            run_support_bounds j ys child hc
          have hchild := (stepRun_child k (head :: tail) i j ys hstep).1
          simp only [List.length_cons] at hchild hl
          have hproduct : ys.length * (ys.length + 1) ≤
              tail.length * (tail.length + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          rw [← he]
          dsimp only [prepend]
          simp only [List.length_cons, scanVolume_cons]
          refine ⟨by omega, by omega, by nlinarith, by omega, by omega, ?_⟩
          intro entry hentry
          rcases List.mem_cons.mp hentry with hentry | hentry
          · subst entry
            exact ⟨hn, hi, Nat.le_refl _⟩
          · obtain ⟨hp, hi', hb⟩ := hentries entry hentry
            exact ⟨hp, hi', Nat.le_trans hb (Nat.le_of_lt hchild)⟩
      | inr p =>
          rw [hstep] at hr
          have he : result =
              (some p, ([((head :: tail).length, i.val)], (stepRun k (head :: tail) i).2)) :=
            (PMF.mem_support_pure_iff _ _).mp hr
          subst result
          simp only [List.length_singleton, scanVolume_cons, scanVolume_nil, Nat.add_zero]
          have hproduct : (head :: tail).length ≤
              (head :: tail).length * (head :: tail).length := by
            simp
          refine ⟨by omega, Nat.le_refl _, by nlinarith, hl.1, by omega, ?_⟩
          intro entry hentry
          have heq : entry = ((head :: tail).length, i.val) := List.mem_singleton.mp hentry
          subst entry
          exact ⟨hn, hi, Nat.le_refl _⟩
termination_by xs.length
decreasing_by
  exact (stepRun_child k (head :: tail) i j ys hstep).1

/-- Number of active calls, including the initial call and every reached child. -/
theorem run_active_calls_le (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) : result.2.1.length ≤ xs.length :=
  (run_support_bounds k xs result hr).1

/-- The first active scan already visits every input occurrence. -/
theorem run_initial_scan_le (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) : xs.length ≤ scanVolume result.2.1 :=
  (run_support_bounds k xs result hr).2.1

/-- The triangular worst-case upper bound covers arbitrary duplicates and ranks. -/
theorem run_scanVolume_le (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    scanVolume result.2.1 ≤ xs.length * (xs.length + 1) / 2 := by
  have h := (run_support_bounds k xs result hr).2.2.1
  omega

/-- Same-execution resource transport. The additive two is the possible final
empty call in the invalid-rank extension; no random-bit charge is asserted. -/
theorem run_source_bridge (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    scanVolume result.2.1 ≤ result.2.2 ∧ result.2.2 ≤ 9 * scanVolume result.2.1 + 2 :=
  ⟨(run_support_bounds k xs result hr).2.2.2.1,
    (run_support_bounds k xs result hr).2.2.2.2.1⟩

/-- Every recorded choice is valid for a positive active size bounded by the
initial length. This bound will control initial segments in the tail proof. -/
theorem run_trace_entries (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    ∀ entry ∈ result.2.1, 0 < entry.1 ∧ entry.2 < entry.1 ∧ entry.1 ≤ xs.length :=
  (run_support_bounds k xs result hr).2.2.2.2.2

theorem run_source_quadratic (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (run k xs).support) :
    result.2.2 ≤ 9 * (xs.length * (xs.length + 1) / 2) + 2 := by
  have hv := run_scanVolume_le k xs result hr
  have hc := (run_source_bridge k xs result hr).2
  omega

/-- Existing one-based public ranks, with visible failure at rank zero. -/
def select (k : Nat) (xs : List α) : PMF (Outcome α) :=
  if k = 0 then PMF.pure (none, ([], 0)) else run (k - 1) xs

theorem select_value (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (select k xs).support) : result.1 = sortSelect k xs := by
  by_cases hk : k = 0
  · simp only [select, hk, ↓reduceIte, PMF.mem_support_pure_iff] at hr
    subst result
    simp [sortSelect, hk]
  · simp only [select, hk, ↓reduceIte] at hr
    simpa only [sortSelect, hk, ↓reduceIte] using run_value (k - 1) xs result hr

theorem select_none (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (select k xs).support) :
    result.1 = none ↔ k = 0 ∨ xs.length < k := by
  rw [select_value k xs result hr, sortSelect_none]

theorem select_some_iff (k : Nat) (xs : List α) (result : Outcome α)
    (hr : result ∈ (select k xs).support) (a : α) :
    result.1 = some a ↔ 0 < k ∧ RankedAt xs (k - 1) a := by
  rw [select_value k xs result hr, sortSelect_some_iff]

/-- Project actual work to a countable carrier before any measure is chosen. -/
def scanLaw (k : Nat) (xs : List α) : PMF Nat :=
  PMF.map (fun result => scanVolume result.2.1) (run k xs)

def sourceLaw (k : Nat) (xs : List α) : PMF Nat :=
  PMF.map (fun result => result.2.2) (run k xs)

theorem scanLaw_support (k : Nat) (xs : List α) :
    (scanLaw k xs).support ⊆ Set.Iic (xs.length * (xs.length + 1) / 2) := by
  intro n hn
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
  rw [← he]
  exact run_scanVolume_le k xs result hr

theorem scanLaw_support_finite (k : Nat) (xs : List α) : (scanLaw k xs).support.Finite :=
  (Set.finite_Iic _).subset (scanLaw_support k xs)

theorem sourceLaw_support (k : Nat) (xs : List α) :
    (sourceLaw k xs).support ⊆ Set.Iic (9 * (xs.length * (xs.length + 1) / 2) + 2) := by
  intro n hn
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
  rw [← he]
  exact run_source_quadratic k xs result hr

theorem sourceLaw_support_finite (k : Nat) (xs : List α) : (sourceLaw k xs).support.Finite :=
  (Set.finite_Iic _).subset (sourceLaw_support k xs)

end
end Ordered
end Resources.RandomSelection
