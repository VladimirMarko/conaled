import Applications.Resources.Potential
import Applications.Sequences.Symmetric.Core

/-! Actual symmetric-list operations with distinct source charges and structural visits.
Provenance and statement review: `docs/research/adwh-potential-accounting.md`. -/
namespace Resources.SymmetricCosts
open Sequences.Symmetric
universe u
variable {α : Type u}

def potential (s : SymList α) : Nat :=
  (s.1.length - s.2.length) + (s.2.length - s.1.length)

theorem potential_nil : potential (nilSL : SymList α) = 0 := rfl

theorem potential_reverse (s : SymList α) : potential (reverseSL s) = potential s := by
  simp [potential, reverseSL, Nat.add_comm]

theorem potential_le_length (s : SymList α) : potential s ≤ lengthSL s := by
  simp only [potential, lengthSL]
  omega

def lengthRun : List α → Nat × Nat
  | [] => (0, 1)
  | _ :: xs => let r := lengthRun xs; (r.1 + 1, r.2 + 1)

theorem lengthRun_exact (xs : List α) : lengthRun xs = (xs.length, xs.length + 1) := by
  induction xs <;> simp_all [lengthRun]

def splitRun : Nat → List α → (List α × List α) × Nat
  | 0, xs => (([], xs), 1)
  | _ + 1, [] => (([], []), 1)
  | n + 1, x :: xs =>
      let r := splitRun n xs
      ((x :: r.1.1, r.1.2), r.2 + 1)

theorem splitRun_value (n : Nat) (xs : List α) :
    (splitRun n xs).1 = (xs.take n, xs.drop n) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [splitRun, ih]

theorem splitRun_work (n : Nat) (xs : List α) :
    (splitRun n xs).2 = min n xs.length + 1 := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [splitRun, ih, Nat.succ_min_succ]

def reverseRun : List α → List α → List α × Nat
  | [], acc => (acc, 1)
  | x :: xs, acc =>
      let r := reverseRun xs (x :: acc)
      (r.1, r.2 + 1)

theorem reverseRun_value (xs acc : List α) :
    (reverseRun xs acc).1 = xs.reverse ++ acc := by
  induction xs generalizing acc <;> simp_all [reverseRun, List.append_assoc]

theorem reverseRun_work (xs acc : List α) : (reverseRun xs acc).2 = xs.length + 1 := by
  induction xs generalizing acc <;> simp_all [reverseRun]

/-- The length, shared split, and reversal from the source's `where` clause. -/
def rebalanceRun (xs : List α) : SymList α × Nat :=
  bind (lengthRun xs) fun n =>
    bind (splitRun (n / 2) xs) fun halves =>
      let rev := reverseRun halves.2 []
      ((halves.1, rev.1), rev.2)

theorem rebalanceRun_value (xs : List α) : (rebalanceRun xs).1 = splitSL xs := by
  simp [rebalanceRun, bind, lengthRun_exact, splitRun_value, reverseRun_value, splitSL]

theorem rebalanceRun_work (xs : List α) : (rebalanceRun xs).2 = 2 * xs.length + 3 := by
  have hd := Nat.div_le_self xs.length 2
  simp only [rebalanceRun, bind, lengthRun_exact, splitRun_work, splitRun_value,
    reverseRun_work, List.length_drop, Nat.min_eq_left hd]
  omega

def tailRun : SymList α → SymList α × Nat
  | ([], _) => (nilSL, 1)
  | ([_], ys) => let r := rebalanceRun ys; (reverseSL r.1, r.2 + 1)
  | (_ :: x :: xs, ys) => ((x :: xs, ys), 1)

def tailCharge : SymList α → Nat
  | ([_], ys) => ys.length
  | _ => 1

theorem tailRun_value (s : SymList α) : (tailRun s).1 = tailSL s := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [tailRun, tailSL, rebalanceRun_value]

theorem tailRun_singleton (x : α) (ys : List α) :
    tailRun ([x], ys) = (reverseSL (splitSL ys), 2 * ys.length + 4) := by
  simp [tailRun, rebalanceRun_value, rebalanceRun_work, Nat.add_assoc]

theorem tailRun_work_le (s : SymList α) : (tailRun s).2 ≤ 2 * tailCharge s + 4 := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil => simp [tailRun, tailCharge]
  | cons x xs => cases xs <;> simp [tailRun, tailCharge, rebalanceRun_work]

theorem tailCharge_potential (s : SymList α) :
    tailCharge s + potential (tailSL s) ≤ potential s + 2 := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil => simp [tailCharge, tailSL, potential, nilSL]
  | cons x xs =>
    cases xs with
    | nil =>
      have hd := Nat.div_le_self ys.length 2
      simp only [tailCharge, tailSL, potential, reverseSL, splitSL,
        List.length_take, List.length_reverse, List.length_drop, List.length_cons,
        List.length_nil, Nat.min_eq_left hd]
      omega
    | cons y xs =>
      simp only [tailCharge, tailSL, potential, List.length_cons]
      omega

def initRun (s : SymList α) : SymList α × Nat :=
  let r := tailRun (reverseSL s)
  (reverseSL r.1, r.2)

theorem initRun_value (s : SymList α) : (initRun s).1 = initSL s := by
  simp [initRun, tailRun_value, initSL]

theorem initRun_singleton (xs : List α) (y : α) :
    initRun (xs, [y]) = (splitSL xs, 2 * xs.length + 4) := by
  simp [initRun, reverseSL, tailRun_singleton]

theorem cons_potential (x : α) (s : SymList α) :
    1 + potential (consSL x s) ≤ potential s + 2 := by
  rcases s with ⟨xs, ys⟩
  cases ys <;> simp only [consSL, potential, List.length_cons, List.length_nil] <;> omega

theorem snoc_potential (x : α) (s : SymList α) :
    1 + potential (snocSL x s) ≤ potential s + 2 := by
  rcases s with ⟨xs, ys⟩
  cases xs <;> simp only [snocSL, potential, List.length_cons, List.length_nil] <;> omega

inductive Operation (α : Type u) where
  | cons (x : α)
  | snoc (x : α)
  | head
  | last
  | tail
  | init

structure Result (α : Type u) where
  state : SymList α
  observation : Option (Option α)
  charge : Nat
  work : Nat

def execute : Operation α → SymList α → Result α
  | .cons x, s => ⟨consSL x s, none, 1, 1⟩
  | .snoc x, s => ⟨snocSL x s, none, 1, 1⟩
  | .head, s => ⟨s, some (headSL s), 1, 1⟩
  | .last, s => ⟨s, some (lastSL s), 1, 1⟩
  | .tail, s => let r := tailRun s; ⟨r.1, none, tailCharge s, r.2⟩
  | .init, s => let r := initRun s; ⟨r.1, none, tailCharge (reverseSL s), r.2⟩

theorem execute_inv (op : Operation α) (s : SymList α) (h : Inv s) :
    Inv (execute op s).state := by
  cases op with
  | cons x => exact inv_consSL x s
  | snoc x => exact inv_snocSL x s
  | head => exact h
  | last => exact h
  | tail => simpa [execute, tailRun_value] using inv_tailSL s h
  | init => simpa [execute, initRun_value] using inv_initSL s h

/-- Independent ordinary-list state transition for each operation. -/
def listStep : Operation α → List α → List α
  | .cons x, xs => x :: xs
  | .snoc x, xs => xs ++ [x]
  | .head, xs => xs
  | .last, xs => xs
  | .tail, xs => xs.tail
  | .init, xs => xs.dropLast

theorem execute_abstraction (op : Operation α) (s : SymList α) (h : Inv s) :
    fromSL (execute op s).state = listStep op (fromSL s) := by
  cases op with
  | cons x => exact fromSL_consSL x s h
  | snoc x => exact fromSL_snocSL x s h
  | head => rfl
  | last => rfl
  | tail => simpa [execute, tailRun_value, listStep] using fromSL_tailSL s h
  | init => simpa [execute, initRun_value, listStep] using fromSL_initSL s h

theorem execute_charge_potential (op : Operation α) (s : SymList α) :
    (execute op s).charge + potential (execute op s).state ≤ potential s + 2 := by
  cases op with
  | cons x => exact cons_potential x s
  | snoc x => exact snoc_potential x s
  | head => simp [execute]; omega
  | last => simp [execute]; omega
  | tail => simpa [execute, tailRun_value] using tailCharge_potential s
  | init =>
      simpa [execute, initRun_value, initSL, potential_reverse] using
        tailCharge_potential (reverseSL s)

theorem execute_work_le (op : Operation α) (s : SymList α) :
    (execute op s).work ≤ 2 * (execute op s).charge + 4 := by
  cases op <;> simp only [execute]
  · decide
  · decide
  · decide
  · decide
  · exact tailRun_work_le s
  · exact tailRun_work_le (reverseSL s)

theorem execute_work_potential (op : Operation α) (s : SymList α) :
    (execute op s).work + 2 * potential (execute op s).state ≤ 2 * potential s + 8 := by
  have h₁ := execute_charge_potential op s
  have h₂ := execute_work_le op s
  omega

def chargeStep (op : Operation α) (s : SymList α) : SymList α × Nat :=
  let r := execute op s; (r.state, r.charge)

def workStep (op : Operation α) (s : SymList α) : SymList α × Nat :=
  let r := execute op s; (r.state, r.work)

theorem run_same_state (ops : List (Operation α)) (s : SymList α) :
    (Resources.run chargeStep ops s).1 =
      (Resources.run workStep ops s).1 := by
  rw [Resources.run_state, Resources.run_state]
  rfl

theorem run_inv (ops : List (Operation α)) (s : SymList α) (h : Inv s) :
    Inv (Resources.run workStep ops s).1 := by
  exact Resources.run_invariant workStep Inv execute_inv ops s h

theorem run_abstraction (ops : List (Operation α)) (s : SymList α) (h : Inv s) :
    fromSL (Resources.run workStep ops s).1 =
      ops.foldl (fun xs op => listStep op xs) (fromSL s) := by
  exact Resources.run_value_fusion workStep listStep fromSL Inv execute_inv execute_abstraction ops s h

theorem run_charge_potential (ops : List (Operation α)) (s : SymList α) :
    (Resources.run chargeStep ops s).2 +
        potential (Resources.run chargeStep ops s).1 ≤
      potential s + 2 * ops.length :=
  Resources.run_constant_charge chargeStep potential 2 execute_charge_potential ops s

theorem run_work_potential (ops : List (Operation α)) (s : SymList α) :
    (Resources.run workStep ops s).2 +
        2 * potential (Resources.run workStep ops s).1 ≤
      2 * potential s + 8 * ops.length :=
  Resources.run_constant_charge workStep (fun s => 2 * potential s) 8
    execute_work_potential ops s

theorem run_charge_empty (ops : List (Operation α)) :
    (Resources.run chargeStep ops nilSL).2 ≤ 2 * ops.length := by
  have h := run_charge_potential ops nilSL
  rw [potential_nil, Nat.zero_add] at h
  omega

theorem run_work_empty (ops : List (Operation α)) :
    (Resources.run workStep ops nilSL).2 ≤ 8 * ops.length := by
  have h := run_work_potential ops nilSL
  rw [potential_nil] at h
  omega

theorem head_observation (s : SymList α) (h : Inv s) :
    (execute .head s).observation = some (fromSL s).head? := by
  simp [execute, headSL_eq_head s h]

theorem last_observation (s : SymList α) (h : Inv s) :
    (execute .last s).observation = some (fromSL s).getLast? := by
  simp [execute, lastSL_eq_getLast s h]

theorem initial_potential_needed :
    Inv (([0], [1, 2, 3]) : SymList Nat) ∧
      (Resources.run chargeStep [.tail] ([0], [1, 2, 3])).2 > 2 := by
  constructor
  · simp [Sequences.Symmetric.Inv]
  · decide

end Resources.SymmetricCosts
