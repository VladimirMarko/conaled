import Applications.Search.Incremental.Accounting
import Applications.Search.Incremental.Rows
import Applications.Search.Incremental.Core

/-! Measured primitive operations for the explicitly priced logical-cell machine.
All branches and scalar operations produce events, and erasure is proved. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental.Measured
open Accounting
variable {n : Nat} {α β : Type}

def leCost (a b : Cost) : Accounting.Measured Bool :=
  match a, b with
  | ⊤, ⊤ => (true, [.branch,.branch])
  | ⊤, _ => (false, [.branch,.branch])
  | _, ⊤ => (true, [.branch,.branch])
  | (a : ℚ), (b : ℚ) => (decide (a ≤ b), [.branch,.branch,.compare])

@[simp] theorem leCost_value (a b : Cost) : (leCost a b).1 = decide (a ≤ b) := by
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;> simp [leCost]

def eqCost (a b : Cost) : Accounting.Measured Bool :=
  match a, b with
  | ⊤, ⊤ => (true, [.branch,.branch])
  | ⊤, _ => (false, [.branch,.branch])
  | _, ⊤ => (false, [.branch,.branch])
  | (a : ℚ), (b : ℚ) => (decide (a = b), [.branch,.branch,.compare])

@[simp] theorem eqCost_value (a b : Cost) : (eqCost a b).1 = decide (a = b) := by
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;> simp [eqCost]

def addCost (a b : Cost) : Accounting.Measured Cost :=
  match a, b with
  | ⊤, _ => (⊤, [.branch])
  | _, ⊤ => (⊤, [.branch,.branch])
  | (a : ℚ), (b : ℚ) => ((a+b : ℚ), [.branch,.branch,.add])

@[simp] theorem addCost_value (a b : Cost) : (addCost a b).1 = a+b := by
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;> simp [addCost]

def minCost (a b : Cost) : Accounting.Measured Cost :=
  let test := leCost a b
  (if test.1 then a else b, test.2 ++ [.branch])

@[simp] theorem minCost_value (a b : Cost) : (minCost a b).1 = min a b := by
  simp [minCost, min_def]

def append (xs ys : List α) : Accounting.Measured (List α) :=
  match xs with
  | [] => (ys, [.read,.branch])
  | x :: xs =>
    let tail := append xs ys
    (x :: tail.1, [.read,.branch] ++ tail.2 ++ [.allocate])

@[simp] theorem append_value (xs ys : List α) : (append xs ys).1 = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

def filter (test : α → Accounting.Measured Bool) : List α → Accounting.Measured (List α)
  | [] => ([], [.read,.branch])
  | x :: xs =>
    let tx := test x
    let tail := filter test xs
    (if tx.1 then x :: tail.1 else tail.1,
      [.read,.branch] ++ tx.2 ++ [.branch] ++ tail.2 ++ if tx.1 then [.allocate] else [])

@[simp] theorem filter_value (test : α → Accounting.Measured Bool) (xs : List α) :
    (filter test xs).1 = xs.filter (fun x => (test x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [filter, ih, List.filter_cons]

def rowMinimum (w : Graph n) (g : Labels n) (v : Fin n) : List (Fin n) → Accounting.Measured Cost
  | [] => (⊤, [.read,.branch])
  | u :: us =>
    let value := addCost (g u) (w u v)
    let tail := rowMinimum w g v us
    let result := minCost value.1 tail.1
    (result.1, [.read,.branch,.read,.read] ++ value.2 ++ tail.2 ++ result.2)

@[simp] theorem rowMinimum_value (w : Graph n) (g : Labels n) (v : Fin n) (us : List (Fin n)) :
    (rowMinimum w g v us).1 = _root_.Incremental.LocalRows.fold min ⊤ us (fun u => g u+w u v) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [rowMinimum, ih, _root_.Incremental.LocalRows.fold]

def rhs (w : Graph n) (start : Fin n) (g : Labels n) (v : Fin n) : Accounting.Measured Cost :=
  if v = start then (0,[.compare,.branch]) else
    let result := rowMinimum w g v (List.finRange n)
    (result.1, [.compare,.branch] ++ List.replicate n .allocate ++ result.2)

@[simp] theorem rhs_value (w : Graph n) (start : Fin n) (g : Labels n) (v : Fin n) :
    (rhs w start g v).1 = rhsValue w start g v := by
  by_cases hv : v = start <;> simp [rhs, rhsValue, hv, predecessorMinimum_fold]

def key (h : Fin n → ℚ) (g r : Labels n) (v : Fin n) : Accounting.Measured Key :=
  let low := minCost (g v) (r v)
  let first := addCost low.1 (h v)
  (toLex (first.1,low.1), [.read,.read,.read] ++ low.2 ++ first.2)

@[simp] theorem key_value (h : Fin n → ℚ) (g r : Labels n) (v : Fin n) :
    (key h g r v).1 = labelKey h g r v := by simp [key, labelKey]

def ltCost (a b : Cost) : Accounting.Measured Bool :=
  match a, b with
  | ⊤, _ => (false, [.branch])
  | _, ⊤ => (true, [.branch,.branch])
  | (a : ℚ), (b : ℚ) => (decide (a < b), [.branch,.branch,.compare])

@[simp] theorem ltCost_value (a b : Cost) : (ltCost a b).1 = decide (a < b) := by
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;> simp [ltCost]

def leKey (a b : Key) : Accounting.Measured Bool :=
  let lt := ltCost (ofLex a).1 (ofLex b).1
  if lt.1 then (true, lt.2 ++ [.branch]) else
    let eq := eqCost (ofLex a).1 (ofLex b).1
    if eq.1 then
      let second := leCost (ofLex a).2 (ofLex b).2
      (second.1, lt.2 ++ [.branch] ++ eq.2 ++ [.branch] ++ second.2)
    else (false, lt.2 ++ [.branch] ++ eq.2 ++ [.branch])

@[simp] theorem leKey_value (a b : Key) : (leKey a b).1 = decide (a ≤ b) := by
  by_cases hl : (ofLex a).1 < (ofLex b).1 <;>
    by_cases he : (ofLex a).1 = (ofLex b).1 <;> simp [leKey, hl, he, Prod.Lex.le_iff]

def ltKey (a b : Key) : Accounting.Measured Bool :=
  let lt := ltCost (ofLex a).1 (ofLex b).1
  if lt.1 then (true, lt.2 ++ [.branch]) else
    let eq := eqCost (ofLex a).1 (ofLex b).1
    if eq.1 then
      let second := ltCost (ofLex a).2 (ofLex b).2
      (second.1, lt.2 ++ [.branch] ++ eq.2 ++ [.branch] ++ second.2)
    else (false, lt.2 ++ [.branch] ++ eq.2 ++ [.branch])

@[simp] theorem ltKey_value (a b : Key) : (ltKey a b).1 = decide (a < b) := by
  by_cases hl : (ofLex a).1 < (ofLex b).1 <;>
    by_cases he : (ofLex a).1 = (ofLex b).1 <;> simp [ltKey, hl, he, Prod.Lex.lt_iff]

def selectList (h : Fin n → ℚ) (g r : Labels n) : List (Fin n) → Accounting.Measured (Option (Fin n))
  | [] => (none, [.read,.branch])
  | u :: us =>
    let tail := selectList h g r us
    match tail.1 with
    | none => (some u, [.read,.branch] ++ tail.2 ++ [.branch])
    | some v =>
      let ku := key h g r u
      let kv := key h g r v
      let test := leKey ku.1 kv.1
      (some (if test.1 then u else v),
        [.read,.branch] ++ tail.2 ++ [.branch] ++ ku.2 ++ kv.2 ++ test.2 ++ [.branch])

@[simp] theorem selectList_value (h : Fin n → ℚ) (g r : Labels n) (us : List (Fin n)) :
    (selectList h g r us).1 = Optimization.Thinning.argmin (labelKey h g r) us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [selectList, ih]
    cases ht : Optimization.Thinning.argmin (labelKey h g r) us <;>
      simp [Optimization.Thinning.argmin, ht]

def select (h : Fin n → ℚ) (s : State n) : Accounting.Measured (Option (Fin n)) :=
  selectList h s.g s.rhs s.queue

@[simp] theorem select_value (h : Fin n → ℚ) (s : State n) :
    (select h s).1 = Search.Incremental.select h s := selectList_value _ _ _ _

def topKey (h : Fin n → ℚ) (s : State n) : Accounting.Measured Key :=
  let selected := select h s
  match selected.1 with
  | none => (toLex (⊤,⊤), selected.2 ++ [.branch])
  | some u => let result := key h s.g s.rhs u
              (result.1, selected.2 ++ [.branch] ++ result.2)

@[simp] theorem topKey_value (h : Fin n → ℚ) (s : State n) :
    (topKey h s).1 = Search.Incremental.topKey h s := by
  simp only [topKey, select_value]
  cases hu : Search.Incremental.select h s <;> simp [Search.Incremental.topKey, hu]

def active (goal : Fin n) (h : Fin n → ℚ) (s : State n) : Accounting.Measured Bool :=
  let top := topKey h s
  let target := key h s.g s.rhs goal
  let before := ltKey top.1 target.1
  if before.1 then (true, top.2 ++ target.2 ++ before.2 ++ [.branch]) else
    let equal := eqCost (s.g goal) (s.rhs goal)
    (!equal.1, top.2 ++ target.2 ++ before.2 ++ [.branch,.read,.read] ++ equal.2)

@[simp] theorem active_value (goal : Fin n) (h : Fin n → ℚ) (s : State n) :
    (active goal h s).1 = decide (Search.Incremental.active goal h s) := by
  by_cases hb : Search.Incremental.topKey h s < labelKey h s.g s.rhs goal <;>
    simp [active, Search.Incremental.active, hb]

end Search.Incremental.Measured
