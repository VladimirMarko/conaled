import Applications.Resources.ListAppend
import Applications.Resources.Workload

/-!
# Finite list executions with structural work

A dispatch costs one; a produced/copied cons costs one; `c` prices a combining
operation. Full folds observe the whole finite spine. Selectors and recursive
selector folds retain their own control flow. These are declared source costs,
not machine time, physical allocation, or a general lazy evaluator.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListExecution

universe u v
variable {α : Type u} {β : Type v}

def foldr (c : Nat) (f : α → β → β) (e : β) : List α → Measured β Nat
  | [] => (e, 1)
  | x :: xs => bind (foldr c f e xs) (fun y => (f x y, 1 + c))

/-- The existing measured runner executes the actual left-to-right transitions. -/
def foldl (c : Nat) (f : β → α → β) (e : β) (xs : List α) : Measured β Nat :=
  bind (run (fun x s => (f s x, 1 + c)) xs e) (fun s => (s, 1))

theorem foldr_value (c : Nat) (f : α → β → β) (e : β) (xs : List α) :
    (foldr c f e xs).1 = xs.foldr f e := by
  induction xs <;> simp_all [foldr, bind]

theorem foldl_value (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldl c f e xs).1 = xs.foldl f e := by
  simp only [foldl, bind, run_state]

theorem foldr_work (c : Nat) (f : α → β → β) (e : β) (xs : List α) :
    (foldr c f e xs).2 = (1 + c) * xs.length + 1 := by
  induction xs <;> simp_all [foldr, bind, Nat.mul_add]; omega

theorem foldl_work (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldl c f e xs).2 = (1 + c) * xs.length + 1 := by
  simp only [foldl, bind]
  rw [run_observation _ (fun _ => 1 + c) (fun _ _ => rfl)]
  simp [List.map_const', List.sum_replicate_nat, Nat.mul_comm]

def reverseAcc : List α → List α → Measured (List α) Nat
  | [], acc => (acc, 1)
  | x :: xs, acc =>
      let r := reverseAcc xs (x :: acc)
      (r.1, r.2 + 2)

def reverse (xs : List α) : Measured (List α) Nat :=
  foldl 1 (fun ys x => x :: ys) [] xs

theorem reverseAcc_value (xs acc : List α) :
    (reverseAcc xs acc).1 = xs.reverse ++ acc := by
  induction xs generalizing acc <;>
    simp_all [reverseAcc, List.reverse_cons, List.append_assoc]

theorem reverseAcc_work (xs acc : List α) :
    (reverseAcc xs acc).2 = 2 * xs.length + 1 := by
  induction xs generalizing acc <;> simp_all [reverseAcc, Nat.mul_add]

theorem reverse_value (xs : List α) : (reverse xs).1 = xs.reverse := by
  simp [reverse, foldl_value]

theorem reverse_work (xs : List α) : (reverse xs).2 = 2 * xs.length + 1 :=
  foldl_work 1 _ _ xs

theorem reverseAcc_eq_reverse (xs : List α) : reverseAcc xs [] = reverse xs := by
  apply Prod.ext
  · simp [reverseAcc_value, reverse_value]
  · rw [reverseAcc_work, reverse_work]

/-- This realization actually executes, and charges, its preliminary reversal. -/
def foldlViaReverse (c : Nat) (f : β → α → β) (e : β) (xs : List α) : Measured β Nat :=
  bind (reverse xs) (foldr c (fun x y => f y x) e)

theorem foldlViaReverse_value (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldlViaReverse c f e xs).1 = xs.foldl f e := by
  simp [foldlViaReverse, bind, foldr_value, reverse_value]

theorem foldlViaReverse_work (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldlViaReverse c f e xs).2 = (3 + c) * xs.length + 2 := by
  simp [foldlViaReverse, bind, foldr_work, reverse_work, reverse_value, Nat.add_mul]
  omega

theorem foldlViaReverse_extra (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldlViaReverse c f e xs).2 = (foldl c f e xs).2 + 2 * xs.length + 1 := by
  rw [foldlViaReverse_work, foldl_work]
  simp [Nat.add_mul]
  omega

def head : List α → Measured (Option α) Nat
  | [] => (none, 1)
  | x :: _ => (some x, 1)

def tail : List α → Measured (Option (List α)) Nat
  | [] => (none, 1)
  | _ :: xs => (some xs, 1)

theorem head_value (xs : List α) : (head xs).1 = xs.head? := by cases xs <;> rfl

theorem head_fold_value (xs : List α) :
    (head xs).1 = xs.foldr (fun x _ => some x) none := by cases xs <;> rfl

theorem head_work (xs : List α) : (head xs).2 = 1 := by cases xs <;> rfl

theorem tail_value (xs : List α) : (tail xs).1 = xs.tail? := by cases xs <;> rfl

theorem tail_work (xs : List α) : (tail xs).2 = 1 := by cases xs <;> rfl

def last : List α → Measured (Option α) Nat
  | [] => (none, 1)
  | [x] => (some x, 1)
  | _ :: y :: ys =>
      let r := last (y :: ys)
      (r.1, r.2 + 1)

def init : List α → Measured (Option (List α)) Nat
  | [] => (none, 1)
  | [_] => (some [], 1)
  | x :: y :: ys =>
      let r := init (y :: ys)
      (r.1.map (x :: ·), r.2 + 2)

theorem last_value (xs : List α) : (last xs).1 = xs.getLast? := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases xs <;> simp_all [last]

theorem init_value (xs : List α) :
    (init xs).1 = if xs = [] then none else some xs.dropLast := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases xs <;> simp_all [init]

theorem last_work_cons (x : α) (xs : List α) : (last (x :: xs)).2 = xs.length + 1 := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => simp [last, ih]

theorem init_work_cons (x : α) (xs : List α) : (init (x :: xs)).2 = 2 * xs.length + 1 := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => simp [init, ih, Nat.mul_add]

theorem init_prefix_length (x : α) (xs : List α) :
    ((init (x :: xs)).1.getD []).length = xs.length := by simp [init_value]

private theorem foldl_dropLast_getLast (f : β → α → β) (e : β) (xs : List α)
    (h : xs ≠ []) : f (xs.dropLast.foldl f e) (xs.getLast h) = xs.foldl f e := by
  conv_rhs => rw [← List.dropLast_concat_getLast h]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

def foldrViaHead (c : Nat) (f : α → β → β) (e : β) : List α → Measured β Nat
  | [] => (e, 1)
  | x :: xs =>
      let h := head (x :: xs)
      let t := tail (x :: xs)
      let r := foldrViaHead c f e (t.1.getD [])
      (f (h.1.getD x) r.1, 1 + h.2 + t.2 + r.2 + c)

theorem foldrViaHead_value (c : Nat) (f : α → β → β) (e : β) (xs : List α) :
    (foldrViaHead c f e xs).1 = xs.foldr f e := by
  induction xs <;> simp_all [foldrViaHead, head, tail]

theorem foldrViaHead_work (c : Nat) (f : α → β → β) (e : β) (xs : List α) :
    (foldrViaHead c f e xs).2 = (3 + c) * xs.length + 1 := by
  induction xs <;> simp_all [foldrViaHead, head, tail, Nat.mul_add]; omega

def foldlViaInit (c : Nat) (f : β → α → β) (e : β) (xs : List α) : Measured β Nat :=
  match xs with
  | [] => (e, 1)
  | x :: ys =>
      let i := init (x :: ys)
      let l := last (x :: ys)
      let r := foldlViaInit c f e (i.1.getD [])
      (f r.1 (l.1.getD x), 1 + i.2 + l.2 + r.2 + c)
termination_by xs.length
decreasing_by simp [init_prefix_length]

theorem foldlViaInit_value (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldlViaInit c f e xs).1 = xs.foldl f e := by
  rw [foldlViaInit.eq_def]
  cases xs with
  | nil => rfl
  | cons x xs =>
      simp only [init_value, List.cons_ne_nil, ↓reduceIte, Option.getD_some,
        last_value, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]
      rw [foldlViaInit_value]
      exact foldl_dropLast_getLast f e (x :: xs) (List.cons_ne_nil _ _)
termination_by xs.length
decreasing_by simp

private theorem range_sum_double (n : Nat) :
    2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.sum_append]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at *
      omega

private theorem range_sum_upper (n : Nat) : (List.range (n + 1)).sum ≤ n * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [List.range_succ, List.sum_append]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

theorem foldlViaInit_work (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldlViaInit c f e xs).2 =
      3 * (List.range (xs.length + 1)).sum + c * xs.length + 1 := by
  rw [foldlViaInit.eq_def]
  cases xs with
  | nil => simp
  | cons x xs =>
      have ih := foldlViaInit_work c f e ((init (x :: xs)).1.getD [])
      simp only [init_prefix_length] at ih
      simp only [init_work_cons, last_work_cons, List.length_cons]
      rw [ih, List.range_succ (n := xs.length + 1), List.sum_append]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.mul_add]
      omega
termination_by xs.length
decreasing_by simp [init_prefix_length]

theorem foldlViaInit_quadratic_lower (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    xs.length * xs.length ≤ (foldlViaInit c f e xs).2 := by
  have h := range_sum_double xs.length
  rw [foldlViaInit_work]
  simp only [Nat.mul_add, Nat.mul_one] at h
  omega

theorem foldlViaInit_quadratic_upper (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldlViaInit c f e xs).2 ≤ (3 + c) * (xs.length + 1) * (xs.length + 1) := by
  rw [foldlViaInit_work]
  have h := range_sum_upper xs.length
  have hn : xs.length ≤ (xs.length + 1) * (xs.length + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  have hc := Nat.mul_le_mul_left c hn
  have ht : 3 * (List.range (xs.length + 1)).sum + 1 ≤
      3 * ((xs.length + 1) * (xs.length + 1)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  calc
    _ ≤ 3 * ((xs.length + 1) * (xs.length + 1)) +
        c * ((xs.length + 1) * (xs.length + 1)) := by omega
    _ = _ := by simp only [Nat.add_mul, Nat.mul_assoc]

def foldrByHead (c : Nat) (f : α → β → β) (e : β) : List α → Measured β Nat
  | [] => (e, 1)
  | x :: xs =>
      let h := head (x :: xs)
      let t := tail (x :: xs)
      let r := foldr c f e (t.1.getD [])
      (f (h.1.getD x) r.1, 1 + h.2 + t.2 + r.2 + c)

def foldlByInit (c : Nat) (f : β → α → β) (e : β) : List α → Measured β Nat
  | [] => (e, 1)
  | x :: xs =>
      let i := init (x :: xs)
      let l := last (x :: xs)
      let r := foldl c f e (i.1.getD [])
      (f r.1 (l.1.getD x), 1 + i.2 + l.2 + r.2 + c)

theorem foldrByHead_value (c : Nat) (f : α → β → β) (e : β) (xs : List α) :
    (foldrByHead c f e xs).1 = xs.foldr f e := by
  cases xs <;> simp [foldrByHead, head, tail, foldr_value]

theorem foldlByInit_value (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (foldlByInit c f e xs).1 = xs.foldl f e := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simp only [foldlByInit, init_value, List.cons_ne_nil, ↓reduceIte,
        Option.getD_some, last_value, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
        foldl_value]
      exact foldl_dropLast_getLast f e (x :: xs) (List.cons_ne_nil _ _)

theorem foldrByHead_work_cons (c : Nat) (f : α → β → β) (e : β) (x : α) (xs : List α) :
    (foldrByHead c f e (x :: xs)).2 = (1 + c) * xs.length + c + 4 := by
  simp [foldrByHead, head, tail, foldr_work]
  omega

theorem foldlByInit_work_cons (c : Nat) (f : β → α → β) (e : β) (x : α) (xs : List α) :
    (foldlByInit c f e (x :: xs)).2 = (4 + c) * xs.length + c + 4 := by
  simp [foldlByInit, foldl_work, init_prefix_length, init_work_cons, last_work_cons,
    Nat.add_mul]
  omega

end Resources.ListExecution
