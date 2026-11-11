import Applications.Resources.ListExecution
import Mathlib.Data.List.Basic

/-! Longest acceptable prefix for a predicate on whole lists. Empty exhaustion
is admissible even when the predicate rejects empty. This differs from SuffixTrim. -/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.WholeListTrim

universe u v
variable {α : Type u}

def Accept (p : List α → Bool) (xs : List α) : Prop := xs = [] ∨ p xs = true

/-- Independent longest-prefix contract; no recursion, prices or closure premise. -/
def Spec (p : List α → Bool) (xs out : List α) : Prop :=
  out <+: xs ∧ Accept p out ∧
    ∀ ys, ys <+: xs → Accept p ys → ys.length ≤ out.length

/-- Finite ordinary-list prefix checks suffice to certify an independent answer. -/
theorem Spec.of_checks (p : List α → Bool) (xs out : List α)
    (hprefix : out <+: xs) (accepted : Accept p out)
    (maximal : ∀ i : Fin (xs.length + 1), Accept p (xs.take i.val) → i.val ≤ out.length) :
    Spec p xs out := by
  refine ⟨hprefix, accepted, ?_⟩
  intro ys hy ha
  have hlen := hy.length_le
  apply maximal ⟨ys.length, by omega⟩
  simpa only [← List.prefix_iff_eq_take.mp hy] using ha

/-- Repeated whole-list testing with selected abstract length prices. A successful
nonempty guard costs length; failure plus dropLast costs twice length; empty is free. -/
def run (p : List α → Bool) (xs : List α) : Measured (List α) Nat :=
  match xs with
  | [] => ([], 0)
  | x :: tail =>
    if p (x :: tail) then (x :: tail, (x :: tail).length)
    else
      let r := run p (x :: tail).dropLast
      (r.1, 2 * (x :: tail).length + r.2)
termination_by xs.length

/-- Pure returned value of the one measured runner, not a second trim algorithm. -/
def trim (p : List α → Bool) (xs : List α) : List α := (run p xs).1

private theorem prefix_dropLast_of_lt {xs ys : List α} (hp : ys <+: xs)
    (hl : ys.length < xs.length) : ys <+: xs.dropLast := by
  rw [List.dropLast_eq_take, List.prefix_take_iff]
  exact ⟨hp, by omega⟩

/-- Every length is considered in descending order, without a closure premise. -/
theorem run_spec (p : List α → Bool) (xs : List α) : Spec p xs (run p xs).1 := by
  cases xs with
  | nil =>
    rw [run]
    exact ⟨List.prefix_rfl, Or.inl rfl, fun _ h _ => h.length_le⟩
  | cons x tail =>
    rw [run]
    split
    · rename_i hp
      exact ⟨List.prefix_rfl, Or.inr hp, fun _ h _ => h.length_le⟩
    · rename_i hp
      obtain ⟨hpre, hgood, hmax⟩ := run_spec p (x :: tail).dropLast
      refine ⟨hpre.trans (List.dropLast_prefix _), hgood, ?_⟩
      intro ys hys hacc
      apply hmax ys
      · apply prefix_dropLast_of_lt hys
        have hle := hys.length_le
        by_cases hlt : ys.length < (x :: tail).length
        · exact hlt
        · have heq : ys = x :: tail := hys.eq_of_length (by omega)
          rcases hacc with he | ha
          · simp [heq] at he
          · exact False.elim (hp (heq ▸ ha))
      · exact hacc
termination_by xs.length

/-- Independent specification outputs are unique, not only outputs of run. -/
theorem Spec.unique {p : List α → Bool} {xs a b : List α}
    (ha : Spec p xs a) (hb : Spec p xs b) : a = b := by
  have hab := hb.2.2 _ ha.1 ha.2.1
  have hba := ha.2.2 _ hb.1 hb.2.1
  exact (List.prefix_of_prefix_length_le ha.1 hb.1 hab).eq_of_length (by omega)

theorem value_of_spec (p : List α → Bool) (xs out : List α) (h : Spec p xs out) :
    (run p xs).1 = out := (run_spec p xs).unique h

theorem trim_spec (p : List α → Bool) (xs : List α) : Spec p xs (trim p xs) := run_spec p xs

theorem trim_prefix (p : List α → Bool) (xs : List α) : trim p xs <+: xs := (trim_spec p xs).1

theorem trim_length_le (p : List α → Bool) (xs : List α) : (trim p xs).length ≤ xs.length :=
  (trim_prefix p xs).length_le

theorem trim_accept (p : List α → Bool) (xs : List α) : Accept p (trim p xs) :=
  (trim_spec p xs).2.1

theorem run_of_accept (p : List α → Bool) (xs : List α) (h : Accept p xs) :
    run p xs = (xs, xs.length) := by
  cases xs with
  | nil => simp [run]
  | cons x tail =>
    have hp : p (x :: tail) = true := h.resolve_left (by simp)
    simp [run, hp]

theorem trim_of_accept (p : List α → Bool) (xs : List α) (h : Accept p xs) :
    trim p xs = xs := congrArg Prod.fst (run_of_accept p xs h)

theorem run_empty (p : List α → Bool) : run p [] = ([], 0) := by rw [run]

/-- Exact identity of the executed length-price schedule, including empty exhaustion. -/
theorem work_exact (p : List α → Bool) (xs : List α) :
    (run p xs).2 + (run p xs).1.length * (run p xs).1.length =
      xs.length * (xs.length + 1) := by
  cases xs with
  | nil => simp [run]
  | cons x tail =>
    rw [run]
    split
    · simp only [List.length_cons, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
    · have ih := work_exact p (x :: tail).dropLast
      simp only [List.length_dropLast_cons, Nat.mul_add, Nat.mul_one] at ih
      simp only [List.length_cons, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
termination_by xs.length

theorem work_upper (p : List α → Bool) (xs : List α) :
    (run p xs).2 ≤ xs.length * (xs.length + 1) := by
  have h := work_exact p xs
  omega

theorem work_quadratic_upper (p : List α → Bool) (xs : List α) (hn : 0 < xs.length) :
    (run p xs).2 ≤ 2 * xs.length * xs.length := by
  have h := Nat.mul_le_mul_left xs.length (show xs.length + 1 ≤ 2 * xs.length by omega)
  have hu := work_upper p xs
  calc
    (run p xs).2 ≤ xs.length * (xs.length + 1) := hu
    _ ≤ xs.length * (2 * xs.length) := h
    _ = 2 * xs.length * xs.length := by simp [Nat.mul_comm]

theorem all_false_run (xs : List α) :
    run (fun _ => false) xs = ([], xs.length * (xs.length + 1)) := by
  have hgood := (run_spec (fun _ => false) xs).2.1
  have hnil : (run (fun _ => false) xs).1 = [] := by simpa [Accept] using hgood
  have hw := work_exact (fun _ => false) xs
  apply Prod.ext
  · exact hnil
  · simpa [hnil] using hw

theorem all_false_bounds (xs : List α) (hn : 0 < xs.length) :
    xs.length * xs.length ≤ (run (fun _ => false) xs).2 ∧
      (run (fun _ => false) xs).2 ≤ 2 * xs.length * xs.length := by
  constructor
  · rw [all_false_run]
    simp [Nat.mul_add]
  · exact work_quadratic_upper _ xs hn

theorem all_true_run (xs : List α) : run (fun _ => true) xs = (xs, xs.length) :=
  run_of_accept _ xs (Or.inr rfl)

/-- Even eventually, all-input quadratic lower bounds fail on immediate acceptance. -/
theorem quadratic_lower_obstruction (C N : Nat) :
    ∃ n, N ≤ n ∧ C * (run (fun _ => true) (List.replicate n (0 : Nat))).2 < n * n := by
  let n := max N (C + 1)
  have hp : 0 < n := by dsimp [n]; omega
  refine ⟨n, Nat.le_max_left _ _, ?_⟩
  rw [all_true_run]
  simp only [List.length_replicate]
  exact Nat.mul_lt_mul_of_pos_right (by dsimp [n]; omega) hp

/-- Existing measured bind executes the full fold of the chosen prefix. -/
def foldTrim {β : Type v} (c : Nat) (p : List α → Bool) (f : α → β → β)
    (seed : β) (xs : List α) : Measured β Nat :=
  bind (run p xs) (ListExecution.foldr c f seed)

theorem fold_value_of_spec {β : Type v} (c : Nat) (p : List α → Bool) (f : α → β → β)
    (seed : β) (xs out : List α) (h : Spec p xs out) :
    (foldTrim c p f seed xs).1 = out.foldr f seed := by
  simp only [foldTrim, bind, ListExecution.foldr_value, value_of_spec p xs out h]

theorem fold_work_of_spec {β : Type v} (c : Nat) (p : List α → Bool) (f : α → β → β)
    (seed : β) (xs out : List α) (h : Spec p xs out) :
    (foldTrim c p f seed xs).2 + out.length * out.length =
      xs.length * (xs.length + 1) + (1 + c) * out.length + 1 := by
  have hw := work_exact p xs
  rw [value_of_spec p xs out h] at hw
  simp only [foldTrim, bind, ListExecution.foldr_work, value_of_spec p xs out h]
  omega

end Resources.WholeListTrim
