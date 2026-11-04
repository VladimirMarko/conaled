import Applications.Resources.RandomSelectionEndpoints

/-! Exact atoms of the existing fresh-occurrence execution and its trace.

The recorded first index separates different sampled branches. Within a fixed
initial state, the complete recorded trace determines the supported returned
value and measured source calls. Consequently the actual trace pushforward has
the same atom mass as its unique supported complete outcome. This statement
includes duplicates, empty inputs and invalid worker ranks; it does not assert
uniqueness across different initial states or for unsupported outcomes.

These are observation and factorization laws for `run`, not a second executor.
They provide the probability interface needed for the full endpoint path.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open scoped ENNReal
universe u
variable {α : Type u}

noncomputable section

/-- An executed prefix retains the child's value, trace and source calls. -/
theorem prepend_injective (n i calls : Nat) :
    Function.Injective (prepend (α := α) n i calls) := by
  intro r s h
  apply Prod.ext
  · exact congrArg (fun z : Outcome α => z.1) h
  · apply Prod.ext
    · exact congrArg (fun z : Outcome α => z.2.1.tail) h
    · exact Nat.add_left_cancel (congrArg (fun z : Outcome α => z.2.2) h)

/-- Adding a fixed executed prefix does not merge complete child outcomes. -/
theorem map_prepend_apply (n i calls : Nat) (p : PMF (Outcome α)) (r : Outcome α) :
    PMF.map (prepend n i calls) p (prepend n i calls r) = p r := by
  classical
  simp only [PMF.map_apply, (prepend_injective n i calls).eq_iff, tsum_ite_eq']

section Ordered
variable [LinearOrder α]

/-- Exact fresh-choice factorization for any actual recursive step. No child
support, distinctness or valid-rank premise is needed for this atom equality. -/
theorem run_child_atom (k : Nat) (head : α) (tail : List α)
    (i : Fin (tail.length + 1)) (j : Nat) (ys : List α)
    (hi : (stepRun k (head :: tail) i).1 = Sum.inl (j, ys)) (r : Outcome α) :
    run k (head :: tail)
        (prepend (head :: tail).length i.val (stepRun k (head :: tail) i).2 r) =
      (((tail.length + 1 : Nat) : ℝ≥0∞)⁻¹) * run j ys r := by
  classical
  rw [run_cons, PMF.bind_apply]
  refine (tsum_eq_single i ?_).trans ?_
  · intro q hqi
    apply mul_eq_zero_of_right
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hmem
    dsimp only at hmem
    cases hq : (stepRun k (head :: tail) q).1 with
    | inl state =>
        rcases state with ⟨j', ys'⟩
        rw [hq] at hmem
        obtain ⟨r', _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
        have hh := congrArg (fun z : Outcome α => z.2.1.head?.map Prod.snd) he
        change some q.val = some i.val at hh
        exact hqi (Fin.ext (Option.some.inj hh))
    | inr p =>
        rw [hq] at hmem
        have he := (PMF.mem_support_pure_iff _ _).mp hmem
        have hh := congrArg (fun z : Outcome α => z.2.1.head?.map Prod.snd) he
        change some i.val = some q.val at hh
        exact hqi (Fin.ext (Option.some.inj hh).symm)
  · dsimp only
    rw [hi, map_prepend_apply, RandomQuickSort.uniformIndex_apply]

/-- For a fixed input and rank, a supported trace determines the entire actual
outcome, including its measured cost. The rank may be invalid and values may
repeat. The proof follows the one actual strict child selected by each index. -/
theorem run_trace_injective (k : Nat) (xs : List α) (r s : Outcome α)
    (hr : r ∈ (run k xs).support) (hs : s ∈ (run k xs).support)
    (ht : r.2.1 = s.2.1) : r = s := by
  match xs with
  | [] =>
      have er : r = (none, ([], 2)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      have es : s = (none, ([], 2)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hs
      exact er.trans es.symm
  | head :: tail =>
      let branch : Fin (tail.length + 1) → PMF (Outcome α) := fun i =>
        let action := stepRun k (head :: tail) i
        match action.1 with
        | Sum.inl (j, ys) =>
            PMF.map (prepend (head :: tail).length i.val action.2) (run j ys)
        | Sum.inr p =>
            PMF.pure (some p, ([((head :: tail).length, i.val)], action.2))
      have hrun : run k (head :: tail) =
          PMF.bind (RandomQuickSort.uniformIndex tail.length) branch :=
        run_cons k head tail
      have tag (q : Fin (tail.length + 1)) (z : Outcome α)
          (hz : z ∈ (branch q).support) :
          z.2.1.head?.map Prod.snd = some q.val := by
        dsimp only [branch] at hz
        cases hq : (stepRun k (head :: tail) q).1 with
        | inl state =>
            rcases state with ⟨j, ys⟩
            rw [hq] at hz
            obtain ⟨child, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
            rw [← he]
            rfl
        | inr p =>
            rw [hq] at hz
            have he := (PMF.mem_support_pure_iff _ _).mp hz
            rw [he]
            rfl
      rw [hrun] at hr hs
      obtain ⟨i, _, hri⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      obtain ⟨j, _, hsj⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      have ti := tag i r hri
      have tj := tag j s hsj
      have te := congrArg (fun trace : Trace => trace.head?.map Prod.snd) ht
      have hij : i = j := Fin.ext (Option.some.inj (ti.symm.trans (te.trans tj)))
      subst j
      dsimp only [branch] at hri hsj
      cases hstep : (stepRun k (head :: tail) i).1 with
      | inl state =>
          rcases state with ⟨j, ys⟩
          rw [hstep] at hri hsj
          obtain ⟨r', hr', er⟩ := (PMF.mem_support_map_iff _ _ _).mp hri
          obtain ⟨s', hs', es⟩ := (PMF.mem_support_map_iff _ _ _).mp hsj
          have ht' := ht
          rw [← er, ← es] at ht'
          have hc : r'.2.1 = s'.2.1 := congrArg List.tail ht'
          have he := run_trace_injective j ys r' s' hr' hs' hc
          exact er.symm.trans
            ((congrArg (prepend (head :: tail).length i.val
              (stepRun k (head :: tail) i).2) he).trans es)
      | inr p =>
          rw [hstep] at hri hsj
          have er := (PMF.mem_support_pure_iff _ _).mp hri
          have es := (PMF.mem_support_pure_iff _ _).mp hsj
          exact er.trans es.symm
termination_by xs.length
decreasing_by
  exact (stepRun_child k (head :: tail) i j ys hstep).1

/-- The trace observation is a pushforward of the existing actual execution. -/
def traceLaw (k : Nat) (xs : List α) : PMF Trace :=
  PMF.map (fun r : Outcome α => r.2.1) (run k xs)

theorem traceLaw_support (k : Nat) (xs : List α) (trace : Trace) :
    trace ∈ (traceLaw k xs).support ↔
      ∃ r ∈ (run k xs).support, r.2.1 = trace :=
  PMF.mem_support_map_iff _ _ _

/-- An actual supported outcome is the unique contributor to its trace atom.
This connects complete-outcome probability to the exact projected trace event. -/
theorem traceLaw_atom (k : Nat) (xs : List α) (r : Outcome α)
    (hr : r ∈ (run k xs).support) : traceLaw k xs r.2.1 = run k xs r := by
  classical
  rw [traceLaw, PMF.map_apply]
  refine (tsum_eq_single r ?_).trans ?_
  · intro s hsr
    by_cases ht : r.2.1 = s.2.1
    · simp only [ht, ↓reduceIte]
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro hs
      exact hsr (run_trace_injective k xs s r hs hr ht.symm)
    · exact ite_eq_right ht
  · exact ite_eq_left rfl

@[simp] theorem traceLaw_nil (k : Nat) :
    traceLaw k ([] : List α) = PMF.pure [] := by
  simp only [traceLaw, run_nil, PMF.pure_map]

/-- The valid singleton is the actual endpoint path's unit-mass base case. -/
theorem run_singleton_atom (x : α) :
    run 0 [x] (some x, ([(1, 0)], 9)) = 1 := by
  simpa using run_replicate_valid_atom 0 0 x (by decide) 0

end Ordered
end
end Resources.RandomSelection
