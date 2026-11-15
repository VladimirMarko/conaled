import Applications.Search.Incremental.Fresh
import Applications.Search.Incremental.Measured

/-! Literal operation accounting for the fresh, keyed-list comparator.
The event trace prices logical cells and scalar calls, not rational bit work or
Lean's heap. Trace construction and administrative pairs are unpriced.
Materialized paths allocate three fields; each prior-list cons allocates one.
The source's two calls to `extend` are evaluated separately. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental.FreshCosts
open Accounting
variable {n : Nat} {α β : Type}

def map (f : α → Accounting.Measured β) : List α → Accounting.Measured (List β)
  | [] => ([], [.read,.branch])
  | x :: xs =>
    let y := f x
    let tail := map f xs
    (y.1 :: tail.1, [.read,.branch] ++ y.2 ++ tail.2 ++ [.allocate])

@[simp] theorem map_value (f : α → Accounting.Measured β) (xs : List α) :
    (map f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, ih]

def filterMap (f : α → Accounting.Measured (Option β)) : List α → Accounting.Measured (List β)
  | [] => ([], [.read,.branch])
  | x :: xs =>
    let y := f x
    let tail := filterMap f xs
    match y.1 with
    | none => (tail.1, [.read,.branch] ++ y.2 ++ [.branch] ++ tail.2)
    | some b => (b :: tail.1, [.read,.branch] ++ y.2 ++ [.branch] ++ tail.2 ++ [.allocate])

@[simp] theorem filterMap_value (f : α → Accounting.Measured (Option β)) (xs : List α) :
    (filterMap f xs).1 = xs.filterMap (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : (f x).1 <;> simp [filterMap, hx, ih]

abbrev Entry (n : Nat) := Heuristic.Path (Fin n) × Nat

def insert (e : Entry n) : List (Entry n) → Accounting.Measured (List (Entry n))
  | [] => ([e], [.read,.branch,.allocate])
  | a :: as =>
    if e.1.vertex = a.1.vertex then
      (if e.2 ≤ a.2 then e :: as else a :: as,
        [.read,.branch,.compare,.branch,.compare,.branch,.allocate])
    else
      let tail := insert e as
      (a :: tail.1, [.read,.branch,.compare,.branch] ++ tail.2 ++ [.allocate])

@[simp] theorem insert_value (e : Entry n) (q : List (Entry n)) :
    (insert e q).1 = PrioritySearchQueue.insert Heuristic.Path.vertex e q := by
  induction q with
  | nil => rfl
  | cons a as ih => by_cases h : e.1.vertex = a.1.vertex <;>
      simp [insert, PrioritySearchQueue.insert, h, ih]

def add (es q : List (Entry n)) : Accounting.Measured (List (Entry n)) :=
  match es with
  | [] => (q, [.read,.branch])
  | e :: es =>
    let tail := add es q
    let result := insert e tail.1
    (result.1, [.read,.branch] ++ tail.2 ++ result.2)

@[simp] theorem add_value (es q : List (Entry n)) :
    (add es q).1 = PrioritySearchQueue.add Heuristic.Path.vertex es q := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [add, ih, PrioritySearchQueue.add]

def putOrdered (e : Entry n) : List (Entry n) → Accounting.Measured (List (Entry n))
  | [] => ([e], [.read,.branch,.allocate])
  | a :: as =>
    if e.1.vertex ≤ a.1.vertex then
      (e :: a :: as, [.read,.branch,.compare,.branch,.allocate,.allocate])
    else let tail := putOrdered e as
         (a :: tail.1, [.read,.branch,.compare,.branch] ++ tail.2 ++ [.allocate])

@[simp] theorem putOrdered_value (e : Entry n) (q : List (Entry n)) :
    (putOrdered e q).1 = PrioritySearchQueue.putOrdered Heuristic.Path.vertex e q := by
  induction q with
  | nil => rfl
  | cons a as ih => by_cases h : e.1.vertex ≤ a.1.vertex <;>
      simp [putOrdered, PrioritySearchQueue.putOrdered, h, ih]

def ordered : List (Entry n) → Accounting.Measured (List (Entry n))
  | [] => ([], [.read,.branch])
  | e :: es =>
    let tail := ordered es
    let result := putOrdered e tail.1
    (result.1, [.read,.branch] ++ tail.2 ++ result.2)

@[simp] theorem ordered_value (q : List (Entry n)) :
    (ordered q).1 = PrioritySearchQueue.ordered Heuristic.Path.vertex q := by
  induction q with
  | nil => rfl
  | cons e es ih => simp [ordered, ih, PrioritySearchQueue.ordered]

def takeMin (e : Entry n) : List (Entry n) → Accounting.Measured (Entry n × List (Entry n))
  | [] => ((e, []), [.read,.branch])
  | a :: as =>
    let r := takeMin a as
    (if e.2 ≤ r.1.1.2 then (e, a :: as) else (r.1.1, e :: r.1.2),
      [.read,.branch] ++ r.2 ++ [.compare,.branch,.allocate])

@[simp] theorem takeMin_value (e : Entry n) (q : List (Entry n)) :
    (takeMin e q).1 = PrioritySearchQueue.takeMin e q := by
  induction q generalizing e with
  | nil => rfl
  | cons a as ih => simp [takeMin, ih, PrioritySearchQueue.takeMin]

def remove (q : List (Entry n)) : Accounting.Measured (Option (Entry n × List (Entry n))) :=
  let sorted := ordered q
  match sorted.1 with
  | [] => (none, sorted.2 ++ [.read,.branch])
  | e :: es => let r := takeMin e es
               (some r.1, sorted.2 ++ [.read,.branch] ++ r.2)

@[simp] theorem remove_value (q : List (Entry n)) :
    (remove q).1 = PrioritySearchQueue.remove Heuristic.Path.vertex q := by
  simp only [remove, ordered_value]
  cases h : PrioritySearchQueue.ordered Heuristic.Path.vertex q <;>
    simp [PrioritySearchQueue.remove, h]

def lookup (v : Fin n) : Heuristic.Store (Fin n) → Accounting.Measured (Option Nat)
  | [] => (none, [.read,.branch])
  | (u,c) :: xs =>
    if v = u then (some c, [.read,.branch,.compare,.branch])
    else let tail := lookup v xs
         (tail.1, [.read,.branch,.compare,.branch] ++ tail.2)

@[simp] theorem lookup_value (v : Fin n) (st : Heuristic.Store (Fin n)) :
    (lookup v st).1 = Heuristic.lookup v st := by
  induction st with
  | nil => rfl
  | cons a xs ih => rcases a with ⟨u,c⟩; by_cases h : v=u <;>
      simp [lookup, Heuristic.lookup, h, ih]

def seen (v : Fin n) (st : Heuristic.Store (Fin n)) : Accounting.Measured Bool :=
  let r := lookup v st
  (r.1.isSome, r.2 ++ [.branch])

@[simp] theorem seen_value (v : Fin n) (st : Heuristic.Store (Fin n)) :
    (seen v st).1 = Heuristic.seen v st := by simp [seen, Heuristic.seen]

def put (v : Fin n) (c : Nat) (st : Heuristic.Store (Fin n)) :
    Accounting.Measured (Heuristic.Store (Fin n)) :=
  let r := Measured.filter (fun z => (decide (z.1 ≠ v), [.compare])) st
  ((v,c) :: r.1, r.2 ++ [.allocate])

@[simp] theorem put_value (v : Fin n) (c : Nat) (st : Heuristic.Store (Fin n)) :
    (put v c st).1 = Heuristic.put v c st := by simp [put, Heuristic.put]

def extend (p : Heuristic.Path (Fin n)) (v : Fin n) (d : Nat) :
    Accounting.Measured (Heuristic.Path (Fin n)) :=
  (Heuristic.extend p v d, [.allocate,.add,.allocate,.allocate,.allocate])

def succs (g : Heuristic.Graph (Fin n)) (h : Fin n → Nat) (p : Heuristic.Path (Fin n)) :
    Accounting.Measured (List (Entry n)) :=
  let r := map (fun (v,d) =>
    let a := extend p v d
    let b := extend p v d
    ((a.1, Heuristic.estimate h b.1), a.2 ++ b.2 ++ [.read,.add])) (g p.vertex)
  (r.1, [.read] ++ r.2)

@[simp] theorem succs_value (g : Heuristic.Graph (Fin n)) (h : Fin n → Nat)
    (p : Heuristic.Path (Fin n)) : (succs g h p).1 = Heuristic.succs g h p := by
  simp [succs, extend, Heuristic.succs]

def children (g : Heuristic.Graph (Fin n)) (h : Fin n → Nat)
    (st : Heuristic.Store (Fin n)) (p : Heuristic.Path (Fin n)) :
    Accounting.Measured (List (Entry n)) :=
  let xs := succs g h p
  let r := Measured.filter (fun e => let test := seen e.1.vertex st; (!test.1,test.2)) xs.1
  (r.1, xs.2 ++ r.2)

@[simp] theorem children_value (g : Heuristic.Graph (Fin n)) (h : Fin n → Nat)
    (st : Heuristic.Store (Fin n)) (p : Heuristic.Path (Fin n)) :
    (children g h st p).1 = Heuristic.children .closed g h st p := by
  simp [children, Heuristic.children]

def start (h : Fin n → Nat) (s : Fin n) : Accounting.Measured (List (Entry n)) :=
  let r := add [(Heuristic.root s,h s)] []
  (r.1, [.allocate,.allocate,.allocate,.read,.allocate] ++ r.2)

@[simp] theorem start_value (h : Fin n → Nat) (s : Fin n) :
    (start h s).1 = Heuristic.start (Fresh.frontier n) h s := by
  simp [start, Heuristic.start, Fresh.frontier, PrioritySearchQueue.keyed]

def runLoop (g : Heuristic.Graph (Fin n)) (h : Fin n → Nat) (goal : Fin n) :
    Nat → Heuristic.Store (Fin n) → List (Entry n) →
      Accounting.Measured (Option (Option (Heuristic.Path (Fin n))))
  | 0, _, _ => (none, [.branch])
  | fuel+1, st, q =>
    let selected := remove q
    match selected.1 with
    | none => (some none, [.branch] ++ selected.2 ++ [.branch])
    | some (e,r) =>
      if e.1.vertex = goal then
        (some (some e.1), [.branch] ++ selected.2 ++ [.branch,.compare,.branch])
      else
        let test := seen e.1.vertex st
        if test.1 then
          let tail := runLoop g h goal fuel st r
          (tail.1, [.branch] ++ selected.2 ++ [.branch,.compare,.branch] ++ test.2 ++ [.branch] ++ tail.2)
        else
          let recorded := put e.1.vertex e.1.cost st
          let cs := children g h st e.1
          let queue := add cs.1 r
          let tail := runLoop g h goal fuel recorded.1 queue.1
          (tail.1, [.branch] ++ selected.2 ++ [.branch,.compare,.branch] ++ test.2 ++ [.branch] ++
            recorded.2 ++ cs.2 ++ queue.2 ++ tail.2)

@[simp] theorem runLoop_value (g : Heuristic.Graph (Fin n)) (h : Fin n → Nat) (goal : Fin n)
    (fuel : Nat) (st : Heuristic.Store (Fin n)) (q : List (Entry n)) :
    (runLoop g h goal fuel st q).1 =
      Heuristic.run (Fresh.frontier n) .closed g h (fun v => decide (v=goal)) fuel st q := by
  induction fuel generalizing st q with
  | zero => rfl
  | succ fuel ih =>
    simp only [runLoop, remove_value]
    cases hr : PrioritySearchQueue.remove Heuristic.Path.vertex q with
    | none => simp [Heuristic.run, Fresh.frontier, PrioritySearchQueue.keyed, hr]
    | some x =>
      rcases x with ⟨e,r⟩
      by_cases hg : e.1.vertex=goal
      · simp [Heuristic.run, Fresh.frontier, PrioritySearchQueue.keyed, hr, hg]
      · simp only [hg, ite_false, seen_value, put_value, children_value, add_value, ih]
        cases hs : Heuristic.seen e.1.vertex st <;>
          simp [Heuristic.run, Fresh.frontier, PrioritySearchQueue.keyed, hr, hg, Heuristic.skip,
            Heuristic.record, hs]

def flatMap (f : α → Accounting.Measured (List β)) : List α → Accounting.Measured (List β)
  | [] => ([], [.read,.branch])
  | x :: xs =>
    let ys := f x
    let tail := flatMap f xs
    let result := Measured.append ys.1 tail.1
    (result.1, [.read,.branch] ++ ys.2 ++ tail.2 ++ result.2)

@[simp] theorem flatMap_value (f : α → Accounting.Measured (List β)) (xs : List α) :
    (flatMap f xs).1 = xs.flatMap (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [flatMap, ih]

/-- Finite enumeration allocates one logical list cell per element. -/
def enumerate (n : Nat) : Accounting.Measured (List (Fin n)) :=
  (List.finRange n, List.replicate n .allocate)

def values (w : Graph n) (h : Fin n → ℚ) : Accounting.Measured (List ℚ) :=
  let vertices := enumerate n
  let edges := flatMap (fun u =>
    let vs := enumerate n
    let row := filterMap (fun v => (w u v, [.read])) vs.1
    (row.1, vs.2 ++ row.2)) vertices.1
  let hv := enumerate n
  let heuristics := map (fun u => (h u, [.read])) hv.1
  let result := Measured.append edges.1 heuristics.1
  (result.1, vertices.2 ++ edges.2 ++ hv.2 ++ heuristics.2 ++ result.2)

@[simp] theorem values_value (w : Graph n) (h : Fin n → ℚ) :
    (values w h).1 = Fresh.values w h := by
  simp [values, enumerate, Fresh.values]

def product : List Nat → Accounting.Measured Nat
  | [] => (1, [.read,.branch])
  | x :: xs => let tail := product xs
               (x * tail.1, [.read,.branch] ++ tail.2 ++ [.multiply])

@[simp] theorem product_value (xs : List Nat) : (product xs).1 = xs.prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [product, ih]

def denominator (qs : List ℚ) : Accounting.Measured Nat :=
  let ds := map (fun q => (q.den, [.denominator])) qs
  let p := product ds.1
  (p.1, ds.2 ++ p.2)

@[simp] theorem denominator_value (qs : List ℚ) :
    (denominator qs).1 = Fresh.denominator qs := by simp [denominator, Fresh.denominator]

/-- Encoding prices multiplication and the scalar nonnegative floor operation
as one divide event. This is a scalar convention, not a rational bit bound. -/
def encode (s : RationalCost.Scale) (q : ℚ) : Accounting.Measured Nat :=
  (s.encode q, [.multiply,.divide])

def row (s : RationalCost.Scale) (w : Graph n) (u : Fin n) :
    Accounting.Measured (List (Fin n × Nat)) :=
  let vs := enumerate n
  let raw := map (fun v => ((v,w u v), [.read])) vs.1
  let result := filterMap (fun (v,d) =>
    match d with
    | none => (none, [.branch])
    | some q => let e := encode s q
                (some (v,e.1), [.branch] ++ e.2)) raw.1
  (result.1, vs.2 ++ raw.2 ++ result.2)

@[simp] theorem row_value (s : RationalCost.Scale) (w : Graph n) (u : Fin n) :
    (row s w u).1 = RationalCost.adjacency s (adjacency w) u := by
  simp only [row, enumerate, map_value, filterMap_value, RationalCost.adjacency, adjacency]
  congr 1
  funext x
  rcases x with ⟨v,d⟩
  cases d <;> rfl

def prepare (w : Graph n) (h : Fin n → ℚ) : Accounting.Measured (Fresh.Prepared n) :=
  let qs := values w h
  let d := denominator qs.1
  let S : RationalCost.Scale := ⟨d.1, by
    rw [denominator_value]
    exact Fresh.denominator_pos _⟩
  let rows := Vector.ofFn (row S w)
  let hs := Vector.ofFn (fun v => let e := encode S (h v); (e.1, [.read] ++ e.2))
  (⟨S, rows.map Prod.fst, hs.map Prod.fst⟩,
    qs.2 ++ d.2 ++ rows.toList.flatMap Prod.snd ++ List.replicate n .allocate ++
      hs.toList.flatMap Prod.snd ++ List.replicate n .allocate)

@[simp] theorem prepare_value (w : Graph n) (h : Fin n → ℚ) :
    (prepare w h).1 = Fresh.prepare w h := by
  simp [prepare, Fresh.prepare, Fresh.scale, encode, Function.comp_def]

def length : List α → Accounting.Measured Nat
  | [] => (0, [.read,.branch])
  | _ :: xs => let r := length xs
               (r.1+1, [.read,.branch] ++ r.2 ++ [.add])

@[simp] theorem length_value (xs : List α) : (length xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [length, ih]

def budget (n : Nat) : Accounting.Measured Nat :=
  let vs := enumerate n
  let l := length vs.1
  (l.1*(n+1)+2, vs.2 ++ l.2 ++ [.add,.multiply,.add])

@[simp] theorem budget_value (n : Nat) : (budget n).1 = Fresh.budget n := by
  simp [budget, enumerate, Fresh.budget, Heuristic.closedBudget]

def run (p : Fresh.Prepared n) (startVertex goal : Fin n) :
    Accounting.Measured (Option (Option (Heuristic.Path (Fin n)))) :=
  let b := budget n
  let q := start p.estimate startVertex
  let r := runLoop p.graph p.estimate goal b.1 [] q.1
  (r.1, b.2 ++ q.2 ++ r.2)

@[simp] theorem run_value (p : Fresh.Prepared n) (startVertex goal : Fin n) :
    (run p startVertex goal).1 = Fresh.run p startVertex goal := by
  simp only [run, budget_value, start_value]
  exact runLoop_value _ _ _ _ _ _

def result (w : Graph n) (h : Fin n → ℚ) (startVertex goal : Fin n) :
    Accounting.Measured Cost :=
  let p := prepare w h
  let r := run p.1 startVertex goal
  let completed := r.1.get (by
    change (run (prepare w h).1 startVertex goal).1.isSome = true
    simp only [run_value, prepare_value]
    obtain ⟨out, eq⟩ := Fresh.run_total w h startVertex goal
    rw [eq]
    rfl)
  match completed with
  | none => (⊤, p.2 ++ r.2 ++ [.branch,.branch])
  | some path => ((p.1.scale.decode path.cost : Cost), p.2 ++ r.2 ++ [.branch,.branch,.divide])

@[simp] theorem result_value (w : Graph n) (h : Fin n → ℚ) (startVertex goal : Fin n) :
    (result w h startVertex goal).1 = Fresh.result w h startVertex goal := by
  obtain ⟨out, eq⟩ := Fresh.run_total w h startVertex goal
  simp only [result, run_value, prepare_value, eq, Option.get_some, Fresh.result]
  cases out <;> rfl

def cost (prices : Prices) (w : Graph n) (h : Fin n → ℚ) (startVertex goal : Fin n) : Nat :=
  bill prices (result w h startVertex goal).2

theorem result_correct {w : Graph n} (hw : Positive w) {goal : Fin n} {h : Fin n → ℚ}
    (hh : ConsistentHeuristic w goal h) (startVertex : Fin n) :
    DistanceResult w startVertex goal (result w h startVertex goal).1 := by
  rw [result_value]
  exact Fresh.result_correct hw hh startVertex

end Search.Incremental.FreshCosts
