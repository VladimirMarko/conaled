import Mathlib.Tactic

/-!
Conservative monitors for a bounded next/until fragment (#207). Satisfaction
is on infinite traces. The executable evaluator reads optional observations;
no missing observation is asserted to describe the unobserved source truth.
-/
namespace Temporal.Monitor
universe u
variable {Obs : Type u}

inductive Formula (Obs : Type u) : Type u
  | atom : (Obs → Bool) → Formula Obs
  | not : Formula Obs → Formula Obs
  | and : Formula Obs → Formula Obs → Formula Obs
  | next : Formula Obs → Formula Obs
  | untilWithin : Nat → Formula Obs → Formula Obs → Formula Obs

namespace Formula

def horizon : Formula Obs → Nat
  | .atom _ => 0
  | .not p => p.horizon
  | .and p q => max p.horizon q.horizon
  | .next p => 1+p.horizon
  | .untilWithin h p q => h + max p.horizon q.horizon

/-- Independent infinite-trace semantics; waiting excludes the terminal index. -/
def Sat (x : Nat → Obs) (n : Nat) : Formula Obs → Prop
  | .atom p => p (x n) = true
  | .not p => ¬ Sat x n p
  | .and p q => Sat x n p ∧ Sat x n q
  | .next p => Sat x (n+1) p
  | .untilWithin h p q => ∃ k, k ≤ h ∧ Sat x (n+k) q ∧ ∀ j, j < k → Sat x (n+j) p

/-- Missing entries receive an arbitrary provisional Boolean value. Only the
horizon agreement theorem licenses a conclusive monitor verdict. -/
def evaluate (read : Nat → Option Obs) (n : Nat) : Formula Obs → Bool
  | .atom p => (read n).any p
  | .not p => !(evaluate read n p)
  | .and p q => evaluate read n p && evaluate read n q
  | .next p => evaluate read (n+1) p
  | .untilWithin h p q => (List.range (h+1)).any (fun k =>
      evaluate read (n+k) q && (List.range k).all (fun j => evaluate read (n+j) p))

/-- Every read used by the evaluator lies within its structural horizon. -/
theorem evaluate_correct (p : Formula Obs) (read : Nat → Option Obs) (x : Nat → Obs) (n : Nat)
    (agree : ∀ j, j ≤ p.horizon → read (n+j) = some (x (n+j))) :
    evaluate read n p = true ↔ Sat x n p := by
  induction p generalizing n with
  | atom pred =>
    have h := agree 0 le_rfl
    simpa [evaluate, Sat] using congrArg (fun v => v.any pred = true) h
  | not p ih =>
    simpa [evaluate, Sat, Bool.not_eq_true] using not_congr (ih n agree)
  | and p q ihp ihq =>
    have hp := ihp n (fun j hj => agree j (hj.trans (Nat.le_max_left _ _)))
    have hq := ihq n (fun j hj => agree j (hj.trans (Nat.le_max_right _ _)))
    simpa [evaluate, Sat] using and_congr hp hq
  | next p ih =>
    apply ih (n+1)
    intro j hj
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      agree (j+1) (by simp only [horizon]; omega)
  | untilWithin h p q ihp ihq =>
    simp only [evaluate, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      List.all_eq_true, Sat]
    apply exists_congr
    intro k
    constructor
    · rintro ⟨hk,hq,hp⟩
      refine ⟨by omega, ?_, ?_⟩
      · apply (ihq (n+k) ?_).mp hq
        intro j hj
        simpa [Nat.add_assoc] using agree (k+j) (by simp only [horizon]; omega)
      · intro j hj
        apply (ihp (n+j) ?_).mp (hp j hj)
        intro l hl
        simpa [Nat.add_assoc] using agree (j+l) (by simp only [horizon]; omega)
    · rintro ⟨hk,hq,hp⟩
      refine ⟨by omega, ?_, ?_⟩
      · apply (ihq (n+k) ?_).mpr hq
        intro j hj
        simpa [Nat.add_assoc] using agree (k+j) (by simp only [horizon]; omega)
      · intro j hj
        apply (ihp (n+j) ?_).mpr (hp j hj)
        intro l hl
        simpa [Nat.add_assoc] using agree (j+l) (by simp only [horizon]; omega)

/-- Changing only observations beyond the horizon preserves the property. -/
theorem sat_prefix (p : Formula Obs) (x y : Nat → Obs) (n : Nat)
    (agree : ∀ j, j ≤ p.horizon → x (n+j) = y (n+j)) :
    p.Sat x n ↔ p.Sat y n :=
  (p.evaluate_correct (fun j => some (x j)) x n (fun _ _ => rfl)).symm.trans
    (p.evaluate_correct (fun j => some (x j)) y n (fun j hj => congrArg some (agree j hj)))

end Formula

inductive Verdict where
  | pending | satisfied | violated
  deriving DecidableEq, Repr

abbrev State (p : Formula Obs) := {xs : List Obs // xs.length ≤ p.horizon+1}

def initial (p : Formula Obs) : State p := ⟨[], by simp⟩

def step (p : Formula Obs) (s : State p) (x : Obs) : State p :=
  ⟨(s.val ++ [x]).take (p.horizon+1), by simp⟩

def run (p : Formula Obs) (s : State p) (xs : List Obs) : State p := xs.foldl (step p) s

def verdict (p : Formula Obs) (s : State p) : Verdict :=
  if s.val.length < p.horizon+1 then .pending
  else if p.evaluate (fun j => s.val[j]?) 0 then .satisfied else .violated

theorem run_append (p : Formula Obs) (s : State p) (xs ys : List Obs) :
    run p s (xs++ys) = run p (run p s xs) ys := List.foldl_append

private theorem take_left (xs ys : List Obs) (k : Nat) :
    (xs.take k ++ ys).take k = (xs++ys).take k := by
  by_cases h : k ≤ xs.length
  · rw [List.take_append_of_le_length (by simpa using h), List.take_take,
      List.take_append_of_le_length h, Nat.min_self]
  · have ht : xs.take k = xs := List.take_of_length_le (by omega)
    rw [ht]

theorem run_entries (p : Formula Obs) (s : State p) (xs : List Obs) :
    (run p s xs).val = (s.val++xs).take (p.horizon+1) := by
  induction xs generalizing s with
  | nil => simpa [run] using (List.take_of_length_le s.property).symm
  | cons x xs ih =>
    change (run p (step p s x) xs).val = _
    rw [ih]
    change (((s.val++[x]).take (p.horizon+1))++xs).take (p.horizon+1) = _
    rw [take_left]
    simp [List.append_assoc]

theorem step_full (p : Formula Obs) (s : State p) (full : s.val.length = p.horizon+1) (x : Obs) :
    step p s x = s := by
  apply Subtype.ext
  change (s.val++[x]).take (p.horizon+1) = s.val
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le s.property]

/-- Terminal verdicts are absorbing because the complete observation window is retained. -/
theorem terminal_absorbing (p : Formula Obs) (s : State p)
    (conclusive : verdict p s ≠ .pending) (x : Obs) : verdict p (step p s x) = verdict p s := by
  have full : s.val.length = p.horizon+1 := by
    by_contra h
    have short : s.val.length < p.horizon+1 := lt_of_le_of_ne s.property h
    exact conclusive (by simp [verdict,short])
  rw [step_full p s full x]

/-- This retention theorem counts stored frames, not bytes or upstream logs. -/
theorem retention (p : Formula Obs) (s : State p) (xs : List Obs) :
    (run p s xs).val.length ≤ p.horizon+1 := (run p s xs).property

/-- Observed prefix from index zero of the supplied trace (which may itself be shifted). -/
def Prefix (xs : List Obs) (x : Nat → Obs) : Prop :=
  ∀ j, j < xs.length → xs[j]? = some (x j)

theorem run_pending (p : Formula Obs) (xs : List Obs) (short : xs.length < p.horizon+1) :
    verdict p (run p (initial p) xs) = .pending := by
  simp [verdict, run_entries, initial, List.take_of_length_le (by omega : xs.length ≤ p.horizon+1), short]

/-- After the declared horizon the verdict agrees with the infinite semantics. -/
theorem run_complete (p : Formula Obs) (xs : List Obs) (x : Nat → Obs)
    (observed : Prefix xs x) (enough : p.horizon+1 ≤ xs.length) :
    (verdict p (run p (initial p) xs) = .satisfied ↔ p.Sat x 0) ∧
    (verdict p (run p (initial p) xs) = .violated ↔ ¬ p.Sat x 0) := by
  have agreement : ∀ j, j ≤ p.horizon → (xs.take (p.horizon+1))[0+j]? = some (x (0+j)) := by
    intro j hj
    simpa [List.getElem?_take, show j < p.horizon+1 by omega] using observed j (by omega)
  have eval := p.evaluate_correct (fun j => (xs.take (p.horizon+1))[j]?) x 0 agreement
  simp only [verdict, run_entries, initial, List.nil_append, List.length_take,
    Nat.min_eq_left enough, lt_self_iff_false, ↓reduceIte]
  cases he : p.evaluate (fun j => (xs.take (p.horizon+1))[j]?) 0 <;> simp_all

/-- Every conclusive verdict holds for every extension, even if no horizon premise is supplied. -/
theorem run_sound (p : Formula Obs) (xs : List Obs) (x : Nat → Obs) (observed : Prefix xs x) :
    (verdict p (run p (initial p) xs) = .satisfied → p.Sat x 0) ∧
    (verdict p (run p (initial p) xs) = .violated → ¬ p.Sat x 0) := by
  by_cases h : p.horizon+1 ≤ xs.length
  · have e := run_complete p xs x observed h
    exact ⟨e.1.mp,e.2.mp⟩
  · rw [run_pending p xs (by omega)]
    simp

/-- Canonical finite observations of a trace, without an end-of-trace assertion. -/
def observePrefix (x : Nat → Obs) (k : Nat) : List Obs := List.ofFn (fun i : Fin k => x i.val)

theorem prefix_observed (x : Nat → Obs) (k : Nat) : Prefix (observePrefix x k) x := by
  intro j hj
  simp only [observePrefix, List.length_ofFn] at hj
  simp [observePrefix, hj]

/-- Unbounded eventuality cannot be settled from a silent finite prefix. -/
theorem unbounded_undetermined (k : Nat) :
    ∃ x y : Nat → Bool, observePrefix x k = observePrefix y k ∧
      (¬ ∃ n, x n = true) ∧ (∃ n, y n = true) := by
  refine ⟨fun _ => false, fun n => decide (k ≤ n), ?_, ?_, ?_⟩
  · apply congrArg List.ofFn
    funext i
    simp [show ¬ k ≤ i.val by omega]
  · simp
  · exact ⟨k,by simp⟩

end Temporal.Monitor
