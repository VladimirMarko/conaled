import Applications.Resources.FoldedPrune

/-! Constant dispatch prices for the existing whole-list trim/prune semantics. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.PricedPrune
universe u v
variable {α : Type u}

/-- Actual dispatch recursion; empty dispatch does not call the predicate. -/
def trim (g : Nat) (p : List α → Bool) (xs : List α) : Measured (List α) Nat :=
  match xs with
  | [] => ([],g)
  | x :: tail =>
    if p (x :: tail) then (x :: tail,(x :: tail).length+g)
    else let r := trim g p (x :: tail).dropLast
         (r.1,2*(x :: tail).length+g+r.2)
termination_by xs.length

theorem trim_value (g : Nat) (p : List α → Bool) (xs : List α) :
    (trim g p xs).1 = (WholeListTrim.run p xs).1 := by
  cases xs with
  | nil => simp [trim, WholeListTrim.run]
  | cons x tail =>
    rw [trim, WholeListTrim.run]
    split
    · rfl
    · exact trim_value g p (x :: tail).dropLast
termination_by xs.length

theorem trim_extra (g : Nat) (p : List α → Bool) (xs : List α) :
    (trim g p xs).2 + g*(WholeListTrim.run p xs).1.length =
      (WholeListTrim.run p xs).2 + g*(xs.length+1) := by
  cases xs with
  | nil => simp [trim, WholeListTrim.run]
  | cons x tail =>
    rw [trim, WholeListTrim.run]
    split
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega
    · have h := trim_extra g p (x :: tail).dropLast
      simp only [List.length_dropLast_cons] at h
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at *
      omega
termination_by xs.length

theorem trim_zero (p : List α → Bool) (xs : List α) : trim 0 p xs = WholeListTrim.run p xs := by
  apply Prod.ext (trim_value _ _ _)
  simpa using trim_extra 0 p xs

theorem trim_spec (g : Nat) (p : List α → Bool) (xs : List α) :
    WholeListTrim.Spec p xs (trim g p xs).1 := by
  rw [trim_value]; exact WholeListTrim.run_spec p xs

theorem trim_exact (g : Nat) (p : List α → Bool) (xs : List α) :
    (trim g p xs).2 + (trim g p xs).1.length*(trim g p xs).1.length +
      g*(trim g p xs).1.length = xs.length*(xs.length+1)+g*(xs.length+1) := by
  rw [trim_value]
  have h := trim_extra g p xs
  have h0 := WholeListTrim.work_exact p xs
  omega

theorem trim_bound (g : Nat) (p : List α → Bool) (xs : List α) :
    (trim g p xs).2 ≤ xs.length*(xs.length+1)+g*(xs.length+1) := by
  have h := trim_exact g p xs
  omega

def cut (g : Nat) (p : List α → Bool) (x : α) (xs : List α) : Measured (List α) Nat :=
  let r := trim g p (x :: xs)
  (r.1,1+r.2)

theorem cut_value (g : Nat) (p : List α → Bool) (x : α) (xs : List α) :
    (cut g p x xs).1 = (FoldedPrune.cut p x xs).1 := trim_value g p _

theorem cut_zero (p : List α → Bool) (x : α) (xs : List α) :
    cut 0 p x xs = FoldedPrune.cut p x xs := by
  simp only [cut, trim_zero, FoldedPrune.cut]

theorem cut_extra (g : Nat) (p : List α → Bool) (x : α) (xs : List α) :
    (cut g p x xs).2 + g*(FoldedPrune.cut p x xs).1.length =
      (FoldedPrune.cut p x xs).2 + g*(xs.length+2) := by
  have h := trim_extra g p (x :: xs)
  simp only [List.length_cons, Nat.add_assoc, Nat.reduceAdd] at h
  simp only [cut, FoldedPrune.cut]
  omega

def potential (g : Nat) (xs : List α) : Nat := xs.length*xs.length+g*xs.length
def charge (g : Nat) (_ : α) (xs : List α) : Nat := 3*(xs.length+1)+2*g

theorem cut_exact (g : Nat) (p : List α → Bool) (x : α) (xs : List α) :
    (cut g p x xs).2 + potential g (cut g p x xs).1 =
      potential g xs + charge g x xs := by
  have he := cut_extra g p x xs
  have h0 := FoldedPrune.cut_exact p x xs
  simp only [potential, charge, cut_value]
  simp only [FoldedPrune.potential, FoldedPrune.charge] at h0
  simp only [Nat.mul_succ] at he
  omega

def prune (g : Nat) (p : List α → Bool) : List α → Measured (List α) Nat
  | [] => ([],0)
  | x :: xs => bind (prune g p xs) (cut g p x)

theorem prune_value (g : Nat) (p : List α → Bool) (xs : List α) :
    (prune g p xs).1 = (FoldedPrune.run p xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [prune, FoldedPrune.run, bind, cut_value, ih]

theorem prune_spec (g : Nat) (p : List α → Bool) (xs : List α) :
    FoldedPrune.Spec p xs (prune g p xs).1 := by
  rw [prune_value]; exact FoldedPrune.run_spec p xs

theorem prune_longest (g : Nat) (p : List α → Bool) (hc : FoldedPrune.TailClosed p)
    (xs : List α) : WholeListTrim.Spec p xs (prune g p xs).1 := by
  rw [prune_value]; exact FoldedPrune.run_longest_prefix p hc xs

theorem prune_eq_workload (g : Nat) (p : List α → Bool) (xs : List α) :
    prune g p xs = Resources.run (cut g p) xs.reverse [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, Resources.run_append, ← ih]
    simp [prune, Resources.run, bind, pure]

theorem workload_value (g : Nat) (p : List α → Bool) (commands initial : List α) :
    (Resources.run (cut g p) commands initial).1 =
      (Resources.run (FoldedPrune.cut p) commands initial).1 := by
  induction commands generalizing initial with
  | nil => rfl
  | cons x xs ih => simp only [Resources.run_cons, ih, cut_value]

theorem workload_exact (g : Nat) (p : List α → Bool) (commands initial : List α) :
    (Resources.run (cut g p) commands initial).2 +
      potential g (Resources.run (cut g p) commands initial).1 =
      potential g initial + budget (cut g p) (charge g) commands initial :=
  run_potential_exact _ _ _ (cut_exact g p) commands initial

theorem budget_exact (g : Nat) (p : List α → Bool) (commands initial : List α) :
    budget (cut g p) (charge g) commands initial =
      budget (FoldedPrune.cut p) FoldedPrune.charge commands initial + 2*g*commands.length := by
  induction commands generalizing initial with
  | nil => simp [budget]
  | cons x xs ih =>
    simp only [budget, charge, FoldedPrune.charge, ih, cut_value, List.length_cons,
      Nat.mul_add, Nat.mul_one]
    omega

theorem prune_exact (g : Nat) (p : List α → Bool) (xs : List α) :
    (prune g p xs).2 + potential g (prune g p xs).1 =
      budget (FoldedPrune.cut p) FoldedPrune.charge xs.reverse [] + 2*g*xs.length := by
  rw [prune_eq_workload]
  have h := workload_exact g p xs.reverse []
  simpa [potential, budget_exact] using h

theorem prune_extra (g : Nat) (p : List α → Bool) (xs : List α) :
    (prune g p xs).2 + g*(FoldedPrune.run p xs).1.length =
      (FoldedPrune.run p xs).2 + 2*g*xs.length := by
  have h := prune_exact g p xs
  have h0 := FoldedPrune.work_exact p xs
  rw [prune_value] at h
  simp only [potential] at h
  simp only [FoldedPrune.potential] at h0
  omega

theorem prune_zero (p : List α → Bool) (xs : List α) :
    prune 0 p xs = FoldedPrune.run p xs := by
  apply Prod.ext (prune_value _ _ _)
  simpa using prune_extra 0 p xs

theorem prune_bound (g : Nat) (p : List α → Bool) (xs : List α) :
    (prune g p xs).2 ≤ 3*xs.length*xs.length+2*g*xs.length := by
  have h := prune_exact g p xs
  have hb := FoldedPrune.budget_bound p xs
  omega

theorem prune_quadratic_bound (g : Nat) (p : List α → Bool) (xs : List α) :
    (prune g p xs).2 ≤ (3+2*g)*xs.length*xs.length := by
  have hb := prune_bound g p xs
  cases xs with
  | nil => simp [prune]
  | cons x xs =>
    have hn : (x :: xs).length ≤ (x :: xs).length*(x :: xs).length := by
      simp only [List.length_cons, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
    have hg := Nat.mul_le_mul_left (2*g) hn
    simp only [Nat.add_mul, Nat.mul_assoc] at *
    omega

def foldPrune {β : Type v} (g c : Nat) (p : List α → Bool) (f : α → β → β)
    (seed : β) (xs : List α) : Measured β Nat :=
  bind (prune g p xs) (ListExecution.foldr c f seed)

theorem fold_value_of_spec {β : Type v} (g c : Nat) (p : List α → Bool)
    (f : α → β → β) (seed : β) (xs out : List α) (h : FoldedPrune.Spec p xs out) :
    (foldPrune g c p f seed xs).1 = out.foldr f seed := by
  simp only [foldPrune, bind, ListExecution.foldr_value, prune_value,
    FoldedPrune.value_of_spec p xs out h]

theorem fold_value_of_longest {β : Type v} (g c : Nat) (p : List α → Bool)
    (f : α → β → β) (seed : β) (xs out : List α) (hc : FoldedPrune.TailClosed p)
    (h : WholeListTrim.Spec p xs out) :
    (foldPrune g c p f seed xs).1 = out.foldr f seed := by
  have hv := (prune_longest g p hc xs).unique h
  simp only [foldPrune, bind, ListExecution.foldr_value, hv]

theorem fold_work_of_spec {β : Type v} (g c : Nat) (p : List α → Bool)
    (f : α → β → β) (seed : β) (xs out : List α) (h : FoldedPrune.Spec p xs out) :
    (foldPrune g c p f seed xs).2 + potential g out =
      budget (FoldedPrune.cut p) FoldedPrune.charge xs.reverse [] +
        2*g*xs.length+(1+c)*out.length+1 := by
  have he := prune_exact g p xs
  rw [prune_value, FoldedPrune.value_of_spec p xs out h] at he
  simp only [foldPrune, bind, ListExecution.foldr_work, prune_value,
    FoldedPrune.value_of_spec p xs out h]
  omega

end Resources.PricedPrune
