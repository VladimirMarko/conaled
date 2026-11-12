import Applications.Search.Incremental.Invariant

/-! The finite trace bound excludes fuel exhaustion for the actual executor. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

theorem Trace.snoc {w : Graph n} {start : Fin n} {h : Fin n → ℚ}
    {g out : Labels n} {us : List (Fin n)} (tr : Trace w start h g us out)
    (u : Fin n) (hu : Selected w start h out u) :
    Trace w start h g (us ++ [u]) (nextLabels w start out u) := by
  induction tr with
  | nil => exact .cons hu (.nil _)
  | cons hs ht ih => exact .cons hs (ih hu)

theorem runWith_exhausted (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (cont : State n → Prop) [DecidablePred cont]
    (hcont : ∀ s, Valid w start s → cont s → select h s ≠ none)
    (fuel : Nat) (s out : State n) (hs : Valid w start s)
    (he : runWith w start h cont fuel s = .exhausted out) :
    ∃ us, Trace w start h s.g us out.g ∧ us.length = fuel ∧ Valid w start out ∧ cont out := by
  induction fuel generalizing s out with
  | zero =>
    by_cases hc : cont s
    · simp only [runWith.eq_def, ite_eq_left hc, Outcome.exhausted.injEq] at he
      subst out
      exact ⟨[], .nil _, rfl, hs, hc⟩
    · rw [runWith.eq_def] at he
      simp [hc] at he
  | succ k ih =>
    by_cases hc : cont s
    · cases hu : select h s with
      | none => exact False.elim (hcont s hs hc hu)
      | some u =>
        rw [runWith.eq_def] at he
        simp only [ite_eq_left hc, hu] at he
        obtain ⟨us, ht, hl, hv, hc'⟩ := ih (expand w start s u) out (expand_valid w hw start s hs u) he
        have ht' : Trace w start h (nextLabels w start s.g u) us out.g := by
          simpa only [expand_nextLabels w start s hs u] using ht
        exact ⟨u :: us, .cons (select_selected w start h s hs u hu) ht', by simp [hl], hv, hc'⟩
    · rw [runWith.eq_def] at he
      simp [hc] at he

theorem runWith_stopped (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (cont : State n → Prop) [DecidablePred cont]
    (fuel : Nat) (s out : State n) (hs : Valid w start s)
    (he : runWith w start h cont fuel s = .stopped out) :
    ∃ us, Trace w start h s.g us out.g ∧ Valid w start out ∧ ¬ cont out := by
  induction fuel generalizing s out with
  | zero =>
    by_cases hc : cont s
    · rw [runWith.eq_def] at he
      simp [hc] at he
    · rw [runWith.eq_def] at he
      simp only [ite_eq_right hc, Outcome.stopped.injEq] at he
      subst out
      exact ⟨[], .nil _, hs, hc⟩
  | succ k ih =>
    by_cases hc : cont s
    · cases hu : select h s with
      | none => simp [runWith.eq_def, hc, hu] at he
      | some u =>
        rw [runWith.eq_def] at he
        simp only [ite_eq_left hc, hu] at he
        obtain ⟨us, ht, hv, hc'⟩ := ih (expand w start s u) out (expand_valid w hw start s hs u) he
        have ht' : Trace w start h (nextLabels w start s.g u) us out.g := by
          simpa only [expand_nextLabels w start s hs u] using ht
        exact ⟨u :: us, .cons (select_selected w start h s hs u hu) ht', hv, hc'⟩
    · rw [runWith.eq_def] at he
      simp only [ite_eq_right hc, Outcome.stopped.injEq] at he
      subst out
      exact ⟨[], .nil _, hs, hc⟩

theorem runWith_total (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (cont : State n → Prop) [DecidablePred cont]
    (hcont : ∀ s, Valid w start s → cont s → select h s ≠ none)
    (s : State n) (hs : Valid w start s) :
    ∃ out, runWith w start h cont (2*n) s = .stopped out := by
  cases he : runWith w start h cont (2*n) s with
  | stopped out => exact ⟨out, rfl⟩
  | exhausted out =>
    obtain ⟨us, ht, hl, hv, hc⟩ := runWith_exhausted w hw start h cont hcont (2*n) s out hs he
    cases hu : select h out with
    | none => exact False.elim (hcont out hv hc hu)
    | some u =>
      have ht' := ht.snoc u (select_selected w start h out hv u hu)
      have hb := ht'.length_le w hw start h hh
      simp only [List.length_append, List.length_singleton, hl] at hb
      omega

theorem run_total (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) : ∃ out, run w start goal h (2*n) s = .stopped out :=
  runWith_total w hw start h hh (active goal h)
    (fun s hs hc hn => no_select_not_active w start goal h s hs hn hc) s hs

theorem drain_total (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) : ∃ out, drain w start h (2*n) s = .stopped out :=
  runWith_total w hw start h hh (fun s => select h s ≠ none) (fun _ _ hc => hc) s hs

end Search.Incremental
