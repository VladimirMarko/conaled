import Applications.Resources.WholeListTrim
import Applications.Resources.Potential

/-! Tail-first pruning of whole-list predicates, through native measured steps. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.FoldedPrune
universe u v
variable {α : Type u}

/-- Independent recursive value contract; each stage uses longest-prefix Spec. -/
inductive Spec (p : List α → Bool) : List α → List α → Prop
  | nil : Spec p [] []
  | cons {x : α} {xs old out : List α} : Spec p xs old →
      WholeListTrim.Spec p (x :: old) out → Spec p (x :: xs) out

/-- Acceptance survives removing a head, with empty exhaustion admissible. -/
def TailClosed (p : List α → Bool) : Prop :=
  ∀ x xs, p (x :: xs) = true → WholeListTrim.Accept p xs



/-- One cons unit followed by the existing whole-list trim execution. -/
def cut (p : List α → Bool) (x : α) (xs : List α) : Measured (List α) Nat :=
  let r := WholeListTrim.run p (x :: xs)
  (r.1, 1 + r.2)

def run (p : List α → Bool) : List α → Measured (List α) Nat
  | [] => ([], 0)
  | x :: xs => bind (run p xs) (cut p x)

def prune (p : List α → Bool) (xs : List α) : List α := (run p xs).1

theorem cut_value (p : List α → Bool) (x : α) (xs : List α) :
    (cut p x xs).1 = WholeListTrim.trim p (x :: xs) := rfl

theorem cut_length (p : List α → Bool) (x : α) (xs : List α) :
    (cut p x xs).1.length ≤ xs.length + 1 := WholeListTrim.trim_length_le p _

def potential (xs : List α) : Nat := xs.length * xs.length
def charge (_ : α) (xs : List α) : Nat := 3 * (xs.length + 1)

theorem cut_exact (p : List α → Bool) (x : α) (xs : List α) :
    (cut p x xs).2 + potential (cut p x xs).1 = potential xs + charge x xs := by
  have h := WholeListTrim.work_exact p (x :: xs)
  simp only [List.length_cons, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at h
  simp only [cut, potential, charge, Nat.mul_add, Nat.mul_one]
  omega

theorem run_spec (p : List α → Bool) (xs : List α) : Spec p xs (run p xs).1 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons ih (WholeListTrim.run_spec p _)

theorem value_of_spec (p : List α → Bool) (xs out : List α) (h : Spec p xs out) :
    (run p xs).1 = out := by
  induction h with
  | nil => rfl
  | @cons x xs old out _ hcut ih =>
    simp only [run, bind, cut, ih]
    exact WholeListTrim.value_of_spec _ _ _ hcut

theorem Spec.unique {p : List α → Bool} {xs a b : List α}
    (ha : Spec p xs a) (hb : Spec p xs b) : a = b :=
  (value_of_spec _ _ _ ha).symm.trans (value_of_spec _ _ _ hb)

theorem run_prefix (p : List α → Bool) (xs : List α) : (run p xs).1 <+: xs := by
  induction xs with
  | nil => exact List.prefix_rfl
  | cons x xs ih =>
    exact (WholeListTrim.trim_prefix p _).trans (List.cons_prefix_cons.mpr ⟨rfl, ih⟩)

theorem run_length (p : List α → Bool) (xs : List α) :
    (run p xs).1.length ≤ xs.length := (run_prefix p xs).length_le

theorem run_accept (p : List α → Bool) (xs : List α) :
    WholeListTrim.Accept p (run p xs).1 := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons x xs => exact WholeListTrim.trim_accept p _

theorem run_longest_prefix (p : List α → Bool) (hc : TailClosed p) (xs : List α) :
    WholeListTrim.Spec p xs (run p xs).1 := by
  induction xs with
  | nil => exact ⟨List.prefix_rfl, Or.inl rfl, fun _ h _ => h.length_le⟩
  | cons x xs ih =>
    refine ⟨run_prefix p _, run_accept p _, ?_⟩
    intro ys hy ha
    cases ys with
    | nil => simp
    | cons y ys =>
      obtain ⟨heq, hp⟩ := List.cons_prefix_cons.mp hy
      subst y
      have ht : p (x :: ys) = true := ha.resolve_left (by simp)
      have hl := ih.2.2 ys hp (hc x ys ht)
      have hpre := List.prefix_of_prefix_length_le hp ih.1 hl
      exact (WholeListTrim.run_spec p (x :: (run p xs).1)).2.2 (x :: ys)
        (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩) ha

theorem prune_eq_trim (p : List α → Bool) (hc : TailClosed p) (xs : List α) :
    prune p xs = WholeListTrim.trim p xs :=
  (run_longest_prefix p hc xs).unique (WholeListTrim.trim_spec p xs)

theorem pairwise_tailClosed (r : α → α → Prop) [DecidableRel r] :
    TailClosed (fun xs : List α => decide (xs.Pairwise r)) := by
  intro x xs h
  exact Or.inr (decide_eq_true (List.pairwise_cons.mp (of_decide_eq_true h)).2)

theorem run_value_fold (p : List α → Bool) (xs : List α) :
    (run p xs).1 = xs.foldr (fun x s => WholeListTrim.trim p (x :: s)) [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [run, bind, cut_value, List.foldr_cons, ih]

theorem run_eq_workload (p : List α → Bool) (xs : List α) :
    run p xs = Resources.run (cut p) xs.reverse [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, Resources.run_append, ← ih]
    simp [run, Resources.run, bind, pure]

theorem workload_exact (p : List α → Bool) (commands : List α) (initial : List α) :
    (Resources.run (cut p) commands initial).2 +
      potential (Resources.run (cut p) commands initial).1 =
      potential initial + budget (cut p) charge commands initial :=
  run_potential_exact (cut p) charge potential (cut_exact p) commands initial

theorem work_exact (p : List α → Bool) (xs : List α) :
    (run p xs).2 + potential (run p xs).1 = budget (cut p) charge xs.reverse [] := by
  rw [run_eq_workload]
  simpa [potential] using workload_exact p xs.reverse []

theorem budget_bound (p : List α → Bool) (xs : List α) :
    budget (cut p) charge xs.reverse [] ≤ 3 * xs.length * xs.length := by
  induction xs with
  | nil => simp [budget]
  | cons x xs ih =>
    have hl := run_length p xs
    rw [List.reverse_cons, budget_append, ← run_eq_workload]
    simp only [budget, charge, Nat.add_zero, List.length_cons,
      Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega

theorem work_bound (p : List α → Bool) (xs : List α) :
    (run p xs).2 ≤ 3 * xs.length * xs.length := by
  have he := work_exact p xs
  have hb := budget_bound p xs
  omega

def foldPrune {β : Type v} (c : Nat) (p : List α → Bool) (f : α → β → β)
    (seed : β) (xs : List α) : Measured β Nat :=
  bind (run p xs) (ListExecution.foldr c f seed)

theorem fold_value_of_spec {β : Type v} (c : Nat) (p : List α → Bool)
    (f : α → β → β) (seed : β) (xs out : List α) (h : Spec p xs out) :
    (foldPrune c p f seed xs).1 = out.foldr f seed := by
  simp only [foldPrune, bind, ListExecution.foldr_value, value_of_spec p xs out h]

theorem fold_value_of_longest {β : Type v} (c : Nat) (p : List α → Bool)
    (f : α → β → β) (seed : β) (xs out : List α) (hc : TailClosed p)
    (h : WholeListTrim.Spec p xs out) : (foldPrune c p f seed xs).1 = out.foldr f seed := by
  have hv := (run_longest_prefix p hc xs).unique h
  simp only [foldPrune, bind, ListExecution.foldr_value, hv]

theorem fold_work (c : Nat) (p : List α → Bool) {β : Type v}
    (f : α → β → β) (seed : β) (xs : List α) :
    (foldPrune c p f seed xs).2 + potential (run p xs).1 =
      budget (cut p) charge xs.reverse [] + (1+c)*(run p xs).1.length + 1 := by
  have h := work_exact p xs
  simp only [foldPrune, bind, ListExecution.foldr_work]
  omega

theorem fold_work_of_spec (c : Nat) (p : List α → Bool) {β : Type v}
    (f : α → β → β) (seed : β) (xs out : List α) (h : Spec p xs out) :
    (foldPrune c p f seed xs).2 + potential out =
      budget (cut p) charge xs.reverse [] + (1+c)*out.length + 1 := by
  simpa only [value_of_spec p xs out h] using fold_work c p f seed xs

end Resources.FoldedPrune
