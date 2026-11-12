import Applications.Search.Incremental.Measured
import Applications.Search.Incremental.Patches

/-! An executable event-producing realization of retained-state repair. Bills
come from its actual branches and list traversals, with exact state erasure. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental.Measured
open Accounting
variable {n : Nat}

def removeVertex (v : Fin n) (xs : List (Fin n)) : Accounting.Measured (List (Fin n)) :=
  filter (fun u => (u != v, [.compare])) xs

@[simp] theorem removeVertex_value (v : Fin n) (xs : List (Fin n)) :
    (removeVertex v xs).1 = xs.filter (· != v) := by simp [removeVertex]

def refresh (w : Graph n) (start : Fin n) (s : State n) (v : Fin n) : Accounting.Measured (State n) :=
  let r := rhs w start s.g v
  let removed := removeVertex v s.queue
  let equal := eqCost (s.g v) r.1
  let added := if equal.1 then [] else [v]
  let queue := append removed.1 added
  ({ s with rhs := Function.update s.rhs v r.1, queue := queue.1 },
    r.2 ++ [.write] ++ removed.2 ++ [.read] ++ equal.2 ++ [.branch] ++
      (if equal.1 then [] else [.allocate]) ++ queue.2)

@[simp] theorem refresh_value (w : Graph n) (start : Fin n) (s : State n) (v : Fin n) :
    (refresh w start s v).1 = Search.Incremental.refresh w start s v := by
  simp [refresh, Search.Incremental.refresh]

def refreshMany (w : Graph n) (start : Fin n) : State n → List (Fin n) → Accounting.Measured (State n)
  | s, [] => (s, [.read,.branch])
  | s, v :: vs =>
    let head := refresh w start s v
    let tail := refreshMany w start head.1 vs
    (tail.1, [.read,.branch] ++ head.2 ++ tail.2)

@[simp] theorem refreshMany_value (w : Graph n) (start : Fin n) (s : State n) (vs : List (Fin n)) :
    (refreshMany w start s vs).1 = Search.Incremental.refreshMany w start s vs := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => simp [refreshMany, ih, Search.Incremental.refreshMany]

def successors (w : Graph n) (u : Fin n) : Accounting.Measured (List (Fin n)) :=
  let result := filter (fun v =>
    let test := eqCost (w u v) ⊤
    (!test.1, [.read] ++ test.2)) (List.finRange n)
  (result.1, List.replicate n .allocate ++ result.2)

@[simp] theorem successors_value (w : Graph n) (u : Fin n) :
    (successors w u).1 = Search.Incremental.successors w u := by
  simp [successors, Search.Incremental.successors]

def expand (w : Graph n) (start : Fin n) (s : State n) (u : Fin n) : Accounting.Measured (State n) :=
  let over := ltCost (s.rhs u) (s.g u)
  let g' := Function.update s.g u (if over.1 then s.rhs u else ⊤)
  let removed := removeVertex u s.queue
  let next := successors w u
  let touched := if over.1 then next.1 else u :: next.1
  let result := refreshMany w start { s with g := g', queue := removed.1 } touched
  (result.1, [.read,.read] ++ over.2 ++ [.branch] ++
    (if over.1 then [.read] else []) ++ [.write] ++ removed.2 ++ next.2 ++ [.branch] ++
    (if over.1 then [] else [.allocate]) ++ result.2)

@[simp] theorem expand_value (w : Graph n) (start : Fin n) (s : State n) (u : Fin n) :
    (expand w start s u).1 = Search.Incremental.expand w start s u := by
  simp [expand, Search.Incremental.expand]

def run (w : Graph n) (start goal : Fin n) (h : Fin n → ℚ) :
    Nat → State n → Accounting.Measured (Outcome n)
  | 0, s =>
    let test := active goal h s
    (if test.1 then .exhausted s else .stopped s,
      test.2 ++ [.branch] ++ if test.1 then [.branch] else [])
  | k+1, s =>
    let test := active goal h s
    if test.1 then
      let selected := select h s
      match selected.1 with
      | none => (.exhausted s, test.2 ++ [.branch,.branch] ++ selected.2 ++ [.branch])
      | some u =>
        let step := expand w start s u
        let tail := run w start goal h k step.1
        (tail.1, test.2 ++ [.branch,.branch] ++ selected.2 ++ [.branch] ++ step.2 ++ tail.2)
    else (.stopped s, test.2 ++ [.branch])

theorem run_value (w : Graph n) (start goal : Fin n) (h : Fin n → ℚ) (fuel : Nat) (s : State n) :
    (run w start goal h fuel s).1 = Search.Incremental.run w start goal h fuel s := by
  induction fuel generalizing s with
  | zero =>
    change _ = runWith w start h (Search.Incremental.active goal h) 0 s
    rw [runWith.eq_def]
    simp [run]
  | succ k ih =>
    change _ = runWith w start h (Search.Incremental.active goal h) (k+1) s
    rw [runWith.eq_def]
    by_cases hc : Search.Incremental.active goal h s
    · simp only [run, active_value, decide_eq_true hc, ite_true, ite_eq_left hc, select_value]
      cases hu : Search.Incremental.select h s <;> simp [ih, expand_value, Search.Incremental.run]
    · simp [run, hc]

def applyAssignment (start : Fin n) (p : Graph n × State n) (e : Assignment n) :
    Accounting.Measured (Graph n × State n) :=
  let w' := assign p.1 e
  let updated := refresh w' start p.2 e.target
  ((w',updated.1), [.read,.read,.read,.write] ++ updated.2)

@[simp] theorem applyAssignment_value (start : Fin n) (p : Graph n × State n) (e : Assignment n) :
    (applyAssignment start p e).1 = Search.Incremental.applyAssignment start p e := by
  simp [applyAssignment, Search.Incremental.applyAssignment]

def applyUpdates (start : Fin n) : Graph n → State n → Batch n → Accounting.Measured (Graph n × State n)
  | w, s, [] => ((w,s), [.read,.branch])
  | w, s, e :: es =>
    let head := applyAssignment start (w,s) e
    let tail := applyUpdates start head.1.1 head.1.2 es
    (tail.1, [.read,.branch] ++ head.2 ++ tail.2)

@[simp] theorem applyUpdates_value (start : Fin n) (w : Graph n) (s : State n) (es : Batch n) :
    (applyUpdates start w s es).1 = Search.Incremental.applyUpdates start w s es := by
  induction es generalizing w s with
  | nil => rfl
  | cons e es ih => simp [applyUpdates, ih, Search.Incremental.applyUpdates]

/-- Materialize a label map by ordered cell writes. Function maps realize the
logical cells; their host closure representation is outside this cost model. -/
def labels (f : Fin n → Accounting.Measured Cost) : List (Fin n) → Accounting.Measured (Labels n)
  | [] => (fun _ => ⊤, [.read,.branch])
  | v :: vs =>
    let tail := labels f vs
    (Function.update tail.1 v (f v).1, [.read,.branch] ++ tail.2 ++ (f v).2 ++ [.allocate,.write])

theorem labels_value (f : Fin n → Accounting.Measured Cost) (vs : List (Fin n)) (v : Fin n) :
    (labels f vs).1 v = if v ∈ vs then (f v).1 else ⊤ := by
  induction vs with
  | nil => simp [labels]
  | cons u us ih =>
    by_cases hv : v = u
    · subst v; simp [labels]
    · simp [labels, ih, hv]

def initial (start : Fin n) : Accounting.Measured (State n) :=
  let gs := labels (fun _ => (⊤, [])) (List.finRange n)
  let rs := labels (fun v => (if v = start then 0 else ⊤, [.compare,.branch])) (List.finRange n)
  (⟨gs.1, rs.1, [start]⟩,
    List.replicate n .allocate ++ gs.2 ++ List.replicate n .allocate ++
    rs.2 ++ [.allocate])

@[simp] theorem initial_value (start : Fin n) : (initial start).1 = Search.Incremental.initial start := by
  have hg : (labels (fun _ : Fin n => ((⊤ : Cost), [])) (List.finRange n)).1 = fun _ => ⊤ := by
    funext v; simp [labels_value]
  have hr : (labels (fun v : Fin n => (if v = start then (0 : Cost) else ⊤, [.compare,.branch])) (List.finRange n)).1 =
      fun v => if v = start then 0 else ⊤ := by
    funext v; simp [labels_value]
  simp [initial, Search.Incremental.initial, hg, hr]

def complete (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) : Accounting.Measured (State n) :=
  let out := run w start goal h (2*n) s
  (out.1.getStopped (by rw [run_value]; exact run_total w hw start goal h hh s hs),
    [.multiply] ++ out.2 ++ [.branch])

@[simp] theorem complete_value (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) :
    (complete w hw start goal h hh s hs).1 = Search.Incremental.complete w hw start goal h hh s hs := by
  simp only [complete, Search.Incremental.complete, run_value]

def initializeState (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) : Accounting.Measured (State n) :=
  let seed := initial start
  let out := complete w hw start goal h hh.2.2 seed.1 (by rw [initial_value]; exact initial_valid w start)
  (out.1, seed.2 ++ out.2)

@[simp] theorem initializeState_value (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) :
    (initializeState w hw start goal h hh).1 = Search.Incremental.initializeState w hw start goal h hh := by
  simp [initializeState, Search.Incremental.initializeState]

def repair (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es) (hh : ConsistentHeuristic (applyBatch w es) goal h) :
    Accounting.Measured (State n) :=
  let p := applyUpdates start w s es
  let out := complete p.1.1 (by rw [applyUpdates_value, applyUpdates_graph]; exact applyBatch_positive w hw es hp)
    start goal h (by rw [applyUpdates_value, applyUpdates_graph]; exact hh.2.2)
    p.1.2 (by rw [applyUpdates_value]; exact applyUpdates_valid start w s hs es)
  (out.1, p.2 ++ out.2)

@[simp] theorem repair_value (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es) (hh : ConsistentHeuristic (applyBatch w es) goal h) :
    (repair w hw start goal h s hs es hp hh).1 = Search.Incremental.repair w hw start goal h s hs es hp hh := by
  simp [repair, Search.Incremental.repair]

def observe (goal : Fin n) (s : State n) : Accounting.Measured Cost := (s.g goal, [.read])

end Search.Incremental.Measured
