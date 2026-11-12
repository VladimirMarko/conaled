import Applications.Resources.PositionalPermutations
import Applications.Memoization.Slots

/-! Finite delayed insertion. Events price source operations, not native time or
allocation. Each thunk invocation repeats its body; retention is a separate
native cache operation. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DelayedInsertion
universe u v
variable {α : Type u} {β : Type v}

inductive Event where
  | input (terminal : Bool)
  | outerDispatch (terminal : Bool)
  | outerCons
  | thunk
  | deferredPrepend
  | continuation
  | payloadCons
  | outerObserve (visits : Nat)
  | request (id : Nat)
  | selection (visits : Nat)
  | lookup (visits : Nat)
  | hit
  | miss
  | callback (bill : Nat)
  | update (visits : Nat)
  | delivery (id : Nat)
  | identities (cells : Nat)
  | setupCells (cells : Nat)
  | innerObserve (visits : Nat)
  deriving DecidableEq, BEq, Repr, ReflBEq, LawfulBEq

abbrev Trace := List Event
abbrev Thunk (α : Type u) := Unit → Measured α Trace

/-- Projection counts only constructed outer cells, including intermediate maps. -/
def outerCells : Trace → Nat
  | [] => 0
  | .outerCons :: es => 1 + outerCells es
  | _ :: es => outerCells es

def callbackBills (t : Trace) : List Nat := t.filterMap fun e =>
  match e with | .callback n => some n | _ => none

private def seed (x : α) (xs : List α) : Thunk (List α) :=
  fun _ => (x :: xs, [.payloadCons])

private def prepend (y : α) (t : Thunk (List α)) : Thunk (List α) :=
  fun _ => let r := t (); (y :: r.1, r.2 ++ [.payloadCons])

/-- Mapping creates deferred prepends; it does not invoke any recipe. -/
def wrap (y : α) : List (Thunk (List α)) → Measured (List (Thunk (List α))) Trace
  | [] => ([], [.outerDispatch true])
  | t :: ts =>
    let h := prepend y t
    let r := wrap y ts
    (h :: r.1,
      [.outerDispatch false, .deferredPrepend] ++ r.2 ++ [.outerCons])

/-- Ordinary insertion constructs the intermediate outer spine of every map. -/
def ordinary (x : α) : List α → Measured (List (Thunk (List α))) Trace
  | [] => ([seed x []], [.input true, .thunk, .outerCons])
  | suffix@(y :: ys) =>
    let h := seed x suffix
    let r := ordinary x ys
    let m := wrap y r.1
    (h :: m.1,
      [.input false, .thunk] ++ r.2 ++ m.2 ++ [.outerCons])

/-- The native fold ignores recipes and retains the preceding construction bill. -/
def countOuter (built : Measured (List (Thunk β)) Trace) : Measured Nat Trace :=
  let r := ListExecution.foldl 0 (fun n (_ : Thunk β) => n + 1) 0 built.1
  (r.1, built.2 ++ [.outerObserve r.2])

/-- Independent primitive map relation: closure behavior is specified at force,
while construction records dispatch, deferred closure creation, and outer cons. -/
inductive Wraps (y : α) : List (Thunk (List α)) → List (Thunk (List α)) → Trace → Prop
  | nil : Wraps y [] [] [.outerDispatch true]
  | cons {t t' : Thunk (List α)} {ts us : List (Thunk (List α))} {e : Trace}
      (force : ∀ u, t' u = (y :: (t u).1, (t u).2 ++ [.payloadCons]))
      (rest : Wraps y ts us e) :
      Wraps y (t :: ts) (t' :: us)
        ([.outerDispatch false, .deferredPrepend] ++ e ++ [.outerCons])

inductive Ordinary (x : α) : List α → List (Thunk (List α)) → Trace → Prop
  | nil {t : Thunk (List α)} (force : ∀ u, t u = ([x], [.payloadCons])) :
      Ordinary x [] [t] [.input true, .thunk, .outerCons]
  | cons {y : α} {ys : List α} {t : Thunk (List α)}
      {ts us : List (Thunk (List α))} {e m : Trace}
      (force : ∀ u, t u = (x :: y :: ys, [.payloadCons]))
      (rest : Ordinary x ys ts e) (mapped : Wraps y ts us m) :
      Ordinary x (y :: ys) (t :: us)
        ([.input false, .thunk] ++ e ++ m ++ [.outerCons])

theorem wrap_models (y : α) (ts : List (Thunk (List α))) :
    Wraps y ts (wrap y ts).1 (wrap y ts).2 := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .cons (fun u => by cases u; rfl) ih

theorem ordinary_models (x : α) (xs : List α) :
    Ordinary x xs (ordinary x xs).1 (ordinary x xs).2 := by
  induction xs with
  | nil => exact .nil (fun u => by cases u; rfl)
  | cons y ys ih => exact .cons (fun u => by cases u; rfl) ih (wrap_models _ _)

theorem wrap_length (y : α) (ts : List (Thunk (List α))) :
    (wrap y ts).1.length = ts.length := by
  induction ts <;> simp_all [wrap]

theorem ordinary_length (x : α) (xs : List α) :
    (ordinary x xs).1.length = xs.length + 1 := by
  induction xs <;> simp_all [ordinary, wrap_length]

theorem outerCells_append (a b : Trace) :
    outerCells (a ++ b) = outerCells a + outerCells b := by
  induction a with
  | nil => simp [outerCells]
  | cons e es ih => cases e <;> simp_all [outerCells, Nat.add_assoc]

theorem wrap_outerCells (y : α) (ts : List (Thunk (List α))) :
    outerCells (wrap y ts).2 = ts.length := by
  induction ts <;> simp_all [wrap, outerCells_append, outerCells]

theorem ordinary_outerCells (x : α) (xs : List α) :
    outerCells (ordinary x xs).2 = PositionalPermutations.triangle (xs.length + 1) := by
  induction xs with
  | nil => simp [ordinary, outerCells, PositionalPermutations.triangle]
  | cons y ys ih =>
    change outerCells ([.input false, .thunk] ++ (ordinary x ys).2 ++
      (wrap y (ordinary x ys).1).2 ++ [.outerCons]) = _
    rw [outerCells_append, outerCells_append, outerCells_append, ih,
      wrap_outerCells, ordinary_length]
    simp only [outerCells, List.length_cons, PositionalPermutations.triangle_succ]
    omega

/-- Invoke one recipe, then its callback exactly once. -/
def force (f : List α → Measured β Nat) (t : Thunk (List α)) : Measured β Trace :=
  let a := t ()
  let b := f a.1
  (b.1, a.2 ++ [.callback b.2])

def forceAll (f : List α → Measured β Nat) :
    List (Thunk (List α)) → Measured (List β) Trace
  | [] => ([], [.outerDispatch true])
  | t :: ts =>
    let h := force f t
    let r := forceAll f ts
    (h.1 :: r.1, [.outerDispatch false] ++ h.2 ++ r.2 ++ [.outerCons])

def readout (ts : List (Thunk α)) : List α := ts.map (fun t => (t ()).1)

theorem wrap_readout (y : α) (ts : List (Thunk (List α))) :
    readout (wrap y ts).1 = (readout ts).map (List.cons y) := by
  induction ts <;> simp_all [wrap, readout, prepend]

theorem ordinary_readout (x : α) (xs : List α) :
    readout (ordinary x xs).1 = List.permutations'Aux x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    change (x :: y :: ys) :: readout (wrap y (ordinary x ys).1).1 = _
    rw [wrap_readout, ih]
    rfl

theorem forceAll_values (f : List α → Measured β Nat) (ts : List (Thunk (List α))) :
    (forceAll f ts).1 = (readout ts).map (fun ys => (f ys).1) := by
  induction ts <;> simp_all [forceAll, force, readout]

theorem ordinary_values (f : List α → Measured β Nat) (x : α) (xs : List α) :
    (forceAll f (ordinary x xs).1).1 =
      Sequences.Permutations.insertsWith (fun ys => (f ys).1) x xs := by
  rw [forceAll_values, ordinary_readout, Sequences.Permutations.insertsWith_eq_map]

/-- The measured continuation remains open throughout the recursion. -/
def accumulate (k : List α → Measured β Trace) (x : α) :
    List α → Measured (List (Thunk β)) Trace
  | [] =>
    ([fun _ => let r := k [x]; (r.1, [.payloadCons] ++ r.2)],
      [.input true, .thunk, .outerCons])
  | suffix@(y :: ys) =>
    let h := fun (_ : Unit) => let r := k (x :: suffix); (r.1, [.payloadCons] ++ r.2)
    let next := fun zs => let r := k (y :: zs); (r.1, [.payloadCons] ++ r.2)
    let r := accumulate next x ys
    (h :: r.1, [.input false, .thunk, .continuation] ++ r.2 ++ [.outerCons])

def accumulating (f : List α → Measured β Nat) (x : α) (xs : List α) :=
  accumulate (fun ys => let r := f ys; (r.1, [.callback r.2])) x xs

theorem accumulate_readout (k : List α → Measured β Trace) (x : α) (xs : List α) :
    readout (accumulate k x xs).1 =
      Sequences.Permutations.insertsWith (fun ys => (k ys).1) x xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons y ys ih =>
    simp only [accumulate, readout, List.map_cons, Sequences.Permutations.insertsWith]
    exact congrArg (List.cons _) (ih _)

theorem accumulate_length (k : List α → Measured β Trace) (x : α) (xs : List α) :
    (accumulate k x xs).1.length = xs.length + 1 := by
  induction xs generalizing k <;> simp_all [accumulate]

theorem accumulate_outerCells (k : List α → Measured β Trace) (x : α) (xs : List α) :
    outerCells (accumulate k x xs).2 = xs.length + 1 := by
  induction xs generalizing k <;>
    simp_all [accumulate, outerCells_append, outerCells, Nat.add_comm]

theorem accumulating_tail (x : α) (xs tail : List α) :
    readout (accumulating (fun ys => (ys ++ tail, 0)) x xs).1 =
      (List.permutations'Aux x xs).map (fun ys => ys ++ tail) := by
  exact (accumulate_readout _ x xs).trans
    (Sequences.Permutations.insertsWith_eq_map _ x xs)

/-- The independent position semantics preserves occurrences, not value classes. -/
def insertAt (x : α) (xs : List α) (i : Nat) := xs.take i ++ x :: xs.drop i

theorem insertIdx_eq_insertAt (x : α) (xs : List α) (i : Nat) (h : i ≤ xs.length) :
    xs.insertIdx i x = insertAt x xs i := by
  induction xs generalizing i with
  | nil =>
    have : i = 0 := by simpa using h
    subst i
    rfl
  | cons y ys ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [List.insertIdx, insertAt] using congrArg (List.cons y) (ih i (by simpa using h))

theorem ordinary_position (x : α) (xs : List α) (i : Nat)
    (h : i < (ordinary x xs).1.length) :
    (((ordinary x xs).1[i]) ()).1 = insertAt x xs i := by
  have hi : i < (readout (ordinary x xs).1).length := by simpa [readout] using h
  have he := congrArg (fun l : List (List α) => l[i]?) (ordinary_readout x xs)
  have hp : i < (List.permutations'Aux x xs).length := by
    simpa [List.length_permutations'Aux, ordinary_length] using h
  simp only [readout, List.getElem?_map, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem hp, Option.map_some, Option.some.injEq] at he
  rw [he, List.getElem_permutations'Aux, insertIdx_eq_insertAt]
  rw [ordinary_length] at h
  omega

theorem wrap_body (y : α) (ts : List (Thunk (List α))) (i : Nat)
    (h : i < (wrap y ts).1.length) :
    ((wrap y ts).1[i]) () =
      (y :: ((ts[i]'(by simpa [wrap_length] using h)) ()).1,
        ((ts[i]'(by simpa [wrap_length] using h)) ()).2 ++ [.payloadCons]) := by
  induction ts generalizing i with
  | nil => simp [wrap] at h
  | cons t ts ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa [wrap] using h)

theorem ordinary_body (x : α) (xs : List α) (i : Nat)
    (h : i < (ordinary x xs).1.length) :
    (((ordinary x xs).1[i]) ()).2 = List.replicate (i+1) Event.payloadCons := by
  induction xs generalizing i with
  | nil =>
    have : i = 0 := by simpa [ordinary] using h
    subst i
    rfl
  | cons y ys ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (((wrap y (ordinary x ys).1).1[i]'(by simpa only [ordinary, List.length_cons, Nat.add_lt_add_iff_right] using h)) ()).2 = _
      rw [wrap_body, ih]
      simp [List.replicate_add, Nat.add_assoc]

/-- Primitive continuation relation, independent of the implementing recursion. -/
inductive Accumulates (x : α) : (List α → Measured β Trace) → List α →
    List (Thunk β) → Trace → Prop
  | nil {k : List α → Measured β Trace} {t : Thunk β}
      (force : ∀ u, t u = ((k [x]).1, [.payloadCons] ++ (k [x]).2)) :
      Accumulates x k [] [t] [.input true, .thunk, .outerCons]
  | cons {k next : List α → Measured β Trace} {y : α} {ys : List α}
      {t : Thunk β} {ts : List (Thunk β)} {e : Trace}
      (force : ∀ u, t u = ((k (x :: y :: ys)).1, [.payloadCons] ++ (k (x :: y :: ys)).2))
      (continuation : ∀ zs, next zs = ((k (y :: zs)).1, [.payloadCons] ++ (k (y :: zs)).2))
      (rest : Accumulates x next ys ts e) :
      Accumulates x k (y :: ys) (t :: ts)
        ([.input false, .thunk, .continuation] ++ e ++ [.outerCons])

theorem accumulate_models (k : List α → Measured β Trace) (x : α) (xs : List α) :
    Accumulates x k xs (accumulate k x xs).1 (accumulate k x xs).2 := by
  induction xs generalizing k with
  | nil => exact .nil (fun _ => rfl)
  | cons y ys ih => exact .cons (fun _ => rfl) (fun _ => rfl) (ih _)

theorem accumulate_position (k : List α → Measured β Trace) (x : α) (xs : List α)
    (i : Nat) (h : i < (accumulate k x xs).1.length) :
    ((accumulate k x xs).1[i]) () =
      ((k (insertAt x xs i)).1,
        List.replicate (i+1) Event.payloadCons ++ (k (insertAt x xs i)).2) := by
  induction xs generalizing k i with
  | nil =>
    have : i = 0 := by simpa [accumulate] using h
    subst i
    rfl
  | cons y ys ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change ((accumulate _ x ys).1[i]'(by simpa only [accumulate, List.length_cons, Nat.add_lt_add_iff_right] using h)) () = _
      rw [ih]
      simp [insertAt, List.replicate_add, List.append_assoc, Nat.add_assoc]

/-- Selection visits only the prefix ending at the requested cell; bounds are erased. -/
def select : (ts : List α) → Fin ts.length → Measured α Nat
  | [], i => Fin.elim0 i
  | t :: ts, i => Fin.cases (t, 1)
      (fun j => let r := select ts j; (r.1, r.2 + 1)) i

theorem select_value (ts : List α) (i : Fin ts.length) :
    (select ts i).1 = ts[i] := by
  induction ts with
  | nil => exact Fin.elim0 i
  | cons t ts ih => induction i using Fin.cases <;> simp [select, ih]

theorem select_cost (ts : List α) (i : Fin ts.length) :
    (select ts i).2 = i.val + 1 := by
  induction ts with
  | nil => exact Fin.elim0 i
  | cons t ts ih => induction i using Fin.cases <;> simp [select, ih]

theorem countOuter_eq (built : Measured (List (Thunk β)) Trace) :
    countOuter built = (built.1.length, built.2 ++ [.outerObserve (built.1.length+1)]) := by
  simp [countOuter, ListExecution.foldl_value, ListExecution.foldl_work]

/-- The executable size comes from the charged fold, not from a fresh length pass. -/
structure Counted (α : Type u) where
  size : Nat
  recipes : List (Thunk (List α))
  length_eq : recipes.length = size

def prepare (built : Measured (List (Thunk (List α))) Trace) : Measured (Counted α) Trace :=
  let n := countOuter built
  (⟨n.1, built.1, by simp [n, countOuter_eq]⟩, n.2)

def selected (table : Counted α) (i : Fin table.size) : Measured (Thunk (List α)) Nat :=
  select table.recipes ⟨i.val, by rw [table.length_eq]; exact i.isLt⟩

def delayedBody (table : Counted α) (f : List α → Measured β Nat) (i : Fin table.size) :
    Measured β Trace :=
  let t := selected table i
  let b := force f t.1
  (b.1, [.selection t.2] ++ b.2)

def delayed (table : Counted α) (f : List α → Measured β Nat) (i : Fin table.size) :
    Measured β Trace :=
  let b := delayedBody table f i
  (b.1, [.request i.val] ++ b.2 ++ [.delivery i.val])

theorem selected_cost (table : Counted α) (i : Fin table.size) :
    (selected table i).2 = i.val+1 := select_cost _ _

open Applications.Memoization

/-- Native slots retain the entire measured result, including its callback bill.
    A hit ignores the stored trace; no trace is emitted as fresh work. -/
abbrev Cache (n : Nat) (β : Type) := (Slots.storage n).State (Measured β Trace)

def setup {β : Type} (table : Counted α) : Measured (Cache table.size β) Trace :=
  let s := Slots.setup (V := Measured β Trace) table.size
  (s.1, [.setupCells s.2])

def cacheBody {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) : (Slots.storage table.size).Result (Measured β Trace) :=
  ((delayedBody table f i, s), 0)

def nativeCall {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) :=
  (Slots.storage table.size).call i (cacheBody table f i) s

/-- One native call. Its returned hit count guides reporting without another read
    or callback. On a miss, the body trace is already in the returned result. -/
def retained {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) :
    Measured (β × Cache table.size β × Storage.Cost) Trace :=
  let r := nativeCall table f i s
  let branch := if r.2.1 = 1 then [.hit] else [.miss] ++ r.1.1.2 ++ [.update r.2.2.2.2]
  ((r.1.1.1, r.1.2, r.2), [.request i.val, .lookup r.2.2.2.1] ++ branch ++ [.delivery i.val])

def Valid {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (s : Cache table.size β) : Prop :=
  (Slots.storage table.size).Valid (delayedBody table f) s

theorem setup_valid {β : Type} (table : Counted α) (f : List α → Measured β Nat) :
    Valid table f (setup (β := β) table).1 := by
  change (Slots.storage table.size).Valid _ (Slots.setup table.size).1
  rw [Slots.setup_empty]
  exact Storage.empty_valid _ _

theorem native_correct {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) (h : Valid table f s) :
    (nativeCall table f i s).1.1 = delayedBody table f i ∧
      Valid table f (nativeCall table f i s).1.2 ∧
      (Slots.storage table.size).representation.lookup (nativeCall table f i s).1.2 i =
        some (delayedBody table f i) :=
  Storage.call_correct _ _ _ _ (fun _ hs => ⟨rfl, hs⟩) _ h

theorem native_retains {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) :
    (Slots.storage table.size).Retains s (nativeCall table f i s).1.2 :=
  Storage.call_retains _ _ _ (fun _ _ _ h => h) _

theorem native_repeat {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) (h : Valid table f s) :
    nativeCall table f i (nativeCall table f i s).1.2 =
      ((delayedBody table f i, (nativeCall table f i s).1.2), (1,0,i.val+1,0)) := by
  exact (Storage.repeat_hit (Slots.storage table.size) _ _ _
    (fun _ hs => ⟨rfl, hs⟩) _ h).trans (by rw [Slots.storage_read_cost]; rfl)

theorem retained_projection {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) :
    (retained table f i s).1 =
      ((nativeCall table f i s).1.1.1, (nativeCall table f i s).1.2,
        (nativeCall table f i s).2) := rfl

/-- Primitive force relation: selection, one complete recipe, then one callback. -/
inductive Body (table : Counted α) (f : List α → Measured β Nat) (i : Fin table.size) :
    Measured β Trace → Prop
  | intro {ys : List α} {e : Trace} {v : β} {bill : Nat}
      (recipe : (table.recipes[i.val]'(by rw [table.length_eq]; exact i.isLt)) () = (ys,e))
      (callback : f ys = (v,bill)) :
      Body table f i (v, [.selection (i.val+1)] ++ e ++ [.callback bill])

theorem body_models (table : Counted α) (f : List α → Measured β Nat) (i : Fin table.size) :
    Body table f i (delayedBody table f i) := by
  dsimp only [delayedBody, force, selected]
  rw [select_value, select_cost]
  exact .intro rfl rfl

/-- Native read/write equations specify the transition and all four counters.
    The miss body relation does not consult the adapter's reported trace. -/
inductive Request {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) : Cache table.size β →
      (β × Cache table.size β × Storage.Cost) → Trace → Prop
  | hit {s : Cache table.size β} {b : Measured β Trace} {visits : Nat}
      (read : Slots.read s i = (some b,visits)) :
      Request table f i s (b.1,s,(1,0,visits,0))
        [.request i.val, .lookup visits, .hit, .delivery i.val]
  | miss {s t : Cache table.size β} {b : Measured β Trace} {visits rebuilt : Nat}
      (read : Slots.read s i = (none,visits)) (body : Body table f i b)
      (write : Slots.write s i (some b) = (t,rebuilt)) :
      Request table f i s (b.1,t,(0,1,visits,rebuilt))
        ([.request i.val, .lookup visits, .miss] ++ b.2 ++ [.update rebuilt, .delivery i.val])

theorem retained_models {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) :
    Request table f i s (retained table f i s).1 (retained table f i s).2 := by
  cases hr : Slots.read s i with
  | mk v visits =>
    cases v with
    | none =>
      have hc : nativeCall table f i s =
          (((delayedBody table f i), (Slots.write s i (some (delayedBody table f i))).1),
            (0,1,visits,(Slots.write s i (some (delayedBody table f i))).2)) := by
        simp [nativeCall, Storage.call, Slots.storage, hr, cacheBody]
        rfl
      simp only [retained, hc]
      simp only [Nat.zero_ne_one, ↓reduceIte, List.append_assoc, List.cons_append,
        List.nil_append]
      exact .miss hr (body_models _ _ _) rfl
    | some b =>
      have hc : nativeCall table f i s = ((b,s),(1,0,visits,0)) := by
        simp [nativeCall, Storage.call, Slots.storage, hr]
        rfl
      simp only [retained, hc, ↓reduceIte]
      exact .hit hr

theorem retained_repeat_trace {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) (s : Cache table.size β) (h : Valid table f s) :
    (retained table f i (nativeCall table f i s).1.2).2 =
      [.request i.val, .lookup (i.val+1), .hit, .delivery i.val] := by
  simp [retained, native_repeat _ _ _ _ h]

/-- Direct consumer recurrence, threading the returned cache and result order. -/
def retainedRun {β : Type} (table : Counted α) (f : List α → Measured β Nat) :
    List (Fin table.size) → Cache table.size β →
    Measured (List β × Cache table.size β × Storage.Cost) Trace
  | [], s => (([],s,0), [.outerDispatch true])
  | i :: is, s =>
    let a := retained table f i s
    let r := retainedRun table f is a.1.2.1
    ((a.1.1 :: r.1.1, r.1.2.1, a.1.2.2 + r.1.2.2),
      [.outerDispatch false] ++ a.2 ++ r.2 ++ [.outerCons])

def delayedRun (table : Counted α) (f : List α → Measured β Nat) :
    List (Fin table.size) → Measured (List β) Trace
  | [] => ([], [.outerDispatch true])
  | i :: is =>
    let a := delayed table f i
    let r := delayedRun table f is
    (a.1 :: r.1, [.outerDispatch false] ++ a.2 ++ r.2 ++ [.outerCons])

theorem delayedRun_values (table : Counted α) (f : List α → Measured β Nat)
    (is : List (Fin table.size)) :
    (delayedRun table f is).1 = is.map (fun i => (delayedBody table f i).1) := by
  induction is <;> simp_all [delayedRun, delayed]

theorem retainedRun_correct {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (is : List (Fin table.size)) (s : Cache table.size β) (h : Valid table f s) :
    (retainedRun table f is s).1.1 = is.map (fun i => (delayedBody table f i).1) ∧
      Valid table f (retainedRun table f is s).1.2.1 := by
  induction is generalizing s with
  | nil => exact ⟨rfl, h⟩
  | cons i is ih =>
    have hc := native_correct table f i s h
    have ht := ih (nativeCall table f i s).1.2 hc.2.1
    exact ⟨congrArg₂ List.cons (congrArg Prod.fst hc.1) ht.1, ht.2⟩

/-- Observer runs on the actual delivered lists. Its charge is appended even for hits. -/
def observe {γ : Type v} (r : Measured (List (List γ)) Trace) :
    Measured (List (List γ)) Trace :=
  let o := PositionalPermutations.observeSpines r.1
  (o.1, r.2 ++ [.innerObserve o.2])

theorem observe_eq {γ : Type v} (r : Measured (List (List γ)) Trace) :
    observe r = (r.1, r.2 ++ [.innerObserve (r.1.flatten.length + 3*r.1.length + 1)]) := by
  simp [observe, PositionalPermutations.observeSpines_eq]

/-- Complete ordinary execution retains construction, count, requests and observation. -/
def complete (x : α) (xs : List α) (f : List α → Measured (List β) Nat) :
    Measured (List (List β)) Trace :=
  let t := prepare (ordinary x xs)
  let r := delayedRun t.1 f (List.finRange t.1.size)
  observe (r.1, t.2 ++ [.identities t.1.size] ++ r.2)

theorem retainedRun_projection {β : Type} (table : Counted α) (f : List α → Measured β Nat)
    (is : List (Fin table.size)) (s : Cache table.size β) :
    ((retainedRun table f is s).1.2.1, (retainedRun table f is s).1.2.2) =
      Resources.run (fun i s => ((nativeCall table f i s).1.2, (nativeCall table f i s).2)) is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    change ((retainedRun table f is (nativeCall table f i s).1.2).1.2.1,
      (nativeCall table f i s).2 + (retainedRun table f is (nativeCall table f i s).1.2).1.2.2) = _
    rw [Resources.run_cons]
    have h := ih (nativeCall table f i s).1.2
    exact congrArg (fun r => (r.1, (nativeCall table f i s).2 + r.2)) h

def forceThunks : List (Thunk β) → Measured (List β) Trace
  | [] => ([], [.outerDispatch true])
  | t :: ts => let b := t (); let r := forceThunks ts
              (b.1 :: r.1, [.outerDispatch false] ++ b.2 ++ r.2 ++ [.outerCons])

theorem forceThunks_values (ts : List (Thunk β)) : (forceThunks ts).1 = readout ts := by
  induction ts <;> simp_all [forceThunks, readout]

def completeAccumulating (x : α) (xs : List α) (f : List α → Measured (List β) Nat) :
    Measured (List (List β)) Trace :=
  let b := accumulating f x xs
  let c := countOuter b
  let r := forceThunks b.1
  observe (r.1, c.2 ++ r.2)

def completeRetained {α β : Type} (x : α) (xs : List α)
    (f : List α → Measured (List β) Nat) :
    Measured (List (List β) × Cache (prepare (ordinary x xs)).1.size (List β) × Storage.Cost) Trace :=
  let t := prepare (ordinary x xs)
  let s := setup t.1
  let r := retainedRun t.1 f (List.finRange t.1.size) s.1
  let o := observe (r.1.1, t.2 ++ s.2 ++ [.identities t.1.size] ++ r.2)
  ((o.1,r.1.2),o.2)

theorem completeAccumulating_values (x : α) (xs : List α) (f : List α → Measured (List β) Nat) :
    (completeAccumulating x xs f).1 =
      Sequences.Permutations.insertsWith (fun ys => (f ys).1) x xs := by
  simp only [completeAccumulating, observe_eq, forceThunks_values, accumulating]
  exact accumulate_readout _ _ _

theorem callbackBills_append (a b : Trace) :
    callbackBills (a ++ b) = callbackBills a ++ callbackBills b := List.filterMap_append

theorem wrap_no_callback (y : α) (ts : List (Thunk (List α))) :
    callbackBills (wrap y ts).2 = [] := by
  induction ts <;> simp_all [wrap, callbackBills, List.filterMap_append]

theorem ordinary_no_callback (x : α) (xs : List α) :
    callbackBills (ordinary x xs).2 = [] := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [ordinary, callbackBills_append]
    rw [ih, wrap_no_callback]
    rfl

theorem accumulate_no_callback (k : List α → Measured β Trace) (x : α) (xs : List α) :
    callbackBills (accumulate k x xs).2 = [] := by
  induction xs generalizing k with
  | nil => rfl
  | cons y ys ih =>
    simp only [accumulate, callbackBills_append]
    rw [ih]
    rfl

theorem countOuter_callback (built : Measured (List (Thunk β)) Trace) :
    callbackBills (countOuter built).2 = callbackBills built.2 := by
  rw [countOuter_eq, callbackBills_append]
  exact List.append_nil _

/-- Repeated delayed calls concatenate their full declared work; no retention occurs. -/
theorem delayed_twice (table : Counted α) (f : List α → Measured β Nat)
    (i : Fin table.size) :
    (delayedRun table f [i,i]).2 =
      [.outerDispatch false] ++ (delayed table f i).2 ++
      [.outerDispatch false] ++ (delayed table f i).2 ++
      [.outerDispatch true,.outerCons,.outerCons] := by
  simp [delayedRun, List.append_assoc]

section Repricing
variable {C D : Type*}
local instance : Zero Trace := ⟨[]⟩
local instance : Add Trace := ⟨List.append⟩
local instance : AddMonoid Trace where
  zero := []
  add := List.append
  add_assoc := List.append_assoc
  zero_add := List.nil_append
  add_zero := List.append_nil
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

/-- A tariff may target any additive monoid; order is retained until projected. -/
def price [AddMonoid C] (tariff : Event → C) (events : Trace) : C :=
  (events.map tariff).sum

def priceHom [AddMonoid C] (tariff : Event → C) : Trace →+ C where
  toFun := price tariff
  map_zero' := rfl
  map_add' a b := by
    change ((a ++ b).map tariff).sum = _
    simp [List.map_append, List.sum_append, price]

theorem reprice_sequence [AddMonoid C] (tariff : Event → C)
    (step : Nat → β → Measured β Trace) (ids : List Nat) (s : β) :
    reweight (priceHom tariff) (run step ids s) =
      run (fun i st => reweight (priceHom tariff) (step i st)) ids s :=
  reweight_run _ _ _ _
end Repricing

theorem insertAt_length (x : α) (xs : List α) (i : Nat) (h : i ≤ xs.length) :
    (insertAt x xs i).length = xs.length+1 := by
  simp [insertAt, List.length_take, Nat.min_eq_left h]
  omega

theorem delayed_all_values (table : Counted α) (f : List α → Measured β Nat) :
    (delayedRun table f (List.finRange table.size)).1 =
      (readout table.recipes).map (fun ys => (f ys).1) := by
  rw [delayedRun_values]
  rcases table with ⟨n,ts,h⟩
  subst n
  simp [delayedBody, selected, select_value, force, List.finRange, List.map_ofFn,
    Function.comp_def, readout, List.map_map]
  exact List.ofFn_getElem_eq_map ts (fun t => (f (t ()).1).1)

theorem complete_values (x : α) (xs : List α) (f : List α → Measured (List β) Nat) :
    (complete x xs f).1 = Sequences.Permutations.insertsWith (fun ys => (f ys).1) x xs := by
  simp only [complete, observe_eq, delayed_all_values]
  change (readout (ordinary x xs).1).map _ = _
  rw [ordinary_readout, Sequences.Permutations.insertsWith_eq_map]

theorem delayedBody_ordinary (x : α) (xs : List α) (f : List α → Measured β Nat)
    (i : Fin (prepare (ordinary x xs)).1.size) :
    delayedBody (prepare (ordinary x xs)).1 f i =
      ((f (insertAt x xs i.val)).1,
        [.selection (i.val+1)] ++ List.replicate (i.val+1) .payloadCons ++
        [.callback (f (insertAt x xs i.val)).2]) := by
  have hi : i.val < (ordinary x xs).1.length := by
    simpa [prepare, countOuter_eq] using i.isLt
  simp only [delayedBody, selected, select_value, select_cost, force]
  change ((f (((ordinary x xs).1[i.val]) ()).1).1,
    [.selection (i.val+1)] ++ (((ordinary x xs).1[i.val]) ()).2 ++
      [.callback (f (((ordinary x xs).1[i.val]) ()).1).2]) = _
  rw [ordinary_position, ordinary_body]

theorem callbackBills_replicate_payload (n : Nat) :
    callbackBills (List.replicate n .payloadCons) = [] := by
  induction n <;> simp_all [List.replicate_succ, callbackBills]

theorem delayedBody_ordinary_callback (x : α) (xs : List α) (f : List α → Measured β Nat)
    (i : Fin (prepare (ordinary x xs)).1.size) :
    callbackBills (delayedBody (prepare (ordinary x xs)).1 f i).2 =
      [(f (insertAt x xs i.val)).2] := by
  rw [delayedBody_ordinary]
  simp [callbackBills]

theorem forceAll_callbacks (f : List α → Measured β Nat) (ts : List (Thunk (List α)))
    (h : ∀ t ∈ ts, callbackBills (t ()).2 = []) :
    callbackBills (forceAll f ts).2 = (readout ts).map (fun ys => (f ys).2) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := h t (by simp)
    have hs := ih (fun t hm => h t (by simp [hm]))
    simp only [forceAll, force, callbackBills_append]
    rw [ht, hs]
    simp [callbackBills, readout]

theorem ordinary_all_callbacks (f : List α → Measured β Nat) (x : α) (xs : List α) :
    callbackBills (forceAll f (ordinary x xs).1).2 =
      (List.permutations'Aux x xs).map (fun ys => (f ys).2) := by
  rw [forceAll_callbacks, ordinary_readout]
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  rw [ordinary_body, callbackBills_replicate_payload]

def payloadCells (events : Trace) : Nat := events.count .payloadCons

theorem forceAll_payloadCells (f : List α → Measured β Nat) (ts : List (Thunk (List α))) :
    payloadCells (forceAll f ts).2 = (ts.map (fun t => payloadCells (t ()).2)).sum := by
  induction ts <;> simp_all [forceAll, force, payloadCells, List.count_append]

theorem ordinary_all_payloadCells (f : List α → Measured β Nat) (x : α) (xs : List α) :
    payloadCells (forceAll f (ordinary x xs).1).2 =
      PositionalPermutations.triangle (xs.length+1) := by
  rw [forceAll_payloadCells, ← List.ofFn_getElem_eq_map]
  have he : (fun i : Fin (ordinary x xs).1.length =>
      payloadCells (((ordinary x xs).1[i.val]) ()).2) = (fun i => i.val+1) := by
    funext i
    rw [ordinary_body]
    simp [payloadCells]
  rw [he]
  rw [List.sum_ofFn]
  change (∑ i : Fin (ordinary x xs).1.length, (fun n : Nat => n+1) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : Nat => n+1) (ordinary x xs).1.length]
  simp only [ordinary_length, PositionalPermutations.triangle]

theorem completeRetained_values {α β : Type} (x : α) (xs : List α)
    (f : List α → Measured (List β) Nat) :
    (completeRetained x xs f).1.1 =
      Sequences.Permutations.insertsWith (fun ys => (f ys).1) x xs := by
  have h := (retainedRun_correct (prepare (ordinary x xs)).1 f
    (List.finRange _) _ (setup_valid _ f)).1
  have hd := delayed_all_values (prepare (ordinary x xs)).1 f
  rw [delayedRun_values] at hd
  simp only [completeRetained, observe_eq]
  rw [h, hd]
  change (readout (ordinary x xs).1).map _ = _
  rw [ordinary_readout, Sequences.Permutations.insertsWith_eq_map]

theorem forceThunks_callbacks (ts : List (Thunk β)) :
    callbackBills (forceThunks ts).2 = (ts.map (fun t => callbackBills (t ()).2)).flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [forceThunks, callbackBills_append]
    rw [ih]
    simp [callbackBills]

theorem accumulate_callbackLists (k : List α → Measured β Trace) (x : α) (xs : List α) :
    (accumulate k x xs).1.map (fun t => callbackBills (t ()).2) =
      Sequences.Permutations.insertsWith (fun ys => callbackBills (k ys).2) x xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons y ys ih =>
    simp only [accumulate, List.map_cons, Sequences.Permutations.insertsWith]
    rw [ih]
    rfl

theorem accumulating_all_callbacks (f : List α → Measured β Nat) (x : α) (xs : List α) :
    callbackBills (forceThunks (accumulating f x xs).1).2 =
      (List.permutations'Aux x xs).map (fun ys => (f ys).2) := by
  rw [forceThunks_callbacks, accumulating, accumulate_callbackLists,
    Sequences.Permutations.insertsWith_eq_map]
  generalize List.permutations'Aux x xs = zs
  induction zs <;> simp_all [callbackBills]

theorem forceThunks_payloadCells (ts : List (Thunk β)) :
    payloadCells (forceThunks ts).2 = (ts.map (fun t => payloadCells (t ()).2)).sum := by
  induction ts <;> simp_all [forceThunks, payloadCells, List.count_append]

theorem accumulating_all_payloadCells (f : List α → Measured β Nat) (x : α) (xs : List α) :
    payloadCells (forceThunks (accumulating f x xs).1).2 =
      PositionalPermutations.triangle (xs.length+1) := by
  rw [forceThunks_payloadCells, ← List.ofFn_getElem_eq_map]
  have he : (fun i : Fin (accumulating f x xs).1.length =>
      payloadCells (((accumulating f x xs).1[i.val]) ()).2) = (fun i => i.val+1) := by
    funext i
    have hh := accumulate_position (fun ys => ((f ys).1, [Event.callback (f ys).2])) x xs i.val i.isLt
    have hp : payloadCells (((accumulating f x xs).1[i.val]) ()).2 =
        payloadCells (List.replicate (i.val+1) .payloadCons ++
          [.callback (f (insertAt x xs i.val)).2]) := congrArg (fun r => payloadCells r.2) hh
    rw [hp]
    simp [payloadCells, List.count_append]
  rw [he, List.sum_ofFn]
  rw [Fin.sum_univ_eq_sum_range (fun n : Nat => n+1) (accumulating f x xs).1.length]
  simp only [accumulating, accumulate_length, PositionalPermutations.triangle]

/-- One-element forcing and outer recursion specify order independently. -/
inductive Forced (f : List α → Measured β Nat) :
    List (Thunk (List α)) → List β → Trace → Prop
  | nil : Forced f [] [] [.outerDispatch true]
  | cons {t : Thunk (List α)} {ts : List (Thunk (List α))} {ys : List α}
      {body rest : Trace} {v : β} {bill : Nat} {vs : List β}
      (recipe : t () = (ys,body)) (callback : f ys = (v,bill))
      (tail : Forced f ts vs rest) :
      Forced f (t :: ts) (v :: vs)
        ([.outerDispatch false] ++ body ++ [.callback bill] ++ rest ++ [.outerCons])

theorem forceAll_models (f : List α → Measured β Nat) (ts : List (Thunk (List α))) :
    Forced f ts (forceAll f ts).1 (forceAll f ts).2 := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .cons rfl rfl ih

/-- Prefix cons work plus the returned callback bill. Selection and cache costs
    remain distinct events and are not included in this projection. -/
def bodyWork (events : Trace) : Nat := payloadCells events + (callbackBills events).sum

theorem ordinary_full_bodyWork (f : List α → Measured β Nat) (x : α) (xs : List α) :
    bodyWork (forceAll f (ordinary x xs).1).2 =
      PositionalPermutations.triangle (xs.length+1) +
        ((List.permutations'Aux x xs).map (fun ys => (f ys).2)).sum := by
  rw [bodyWork, ordinary_all_payloadCells, ordinary_all_callbacks]

theorem accumulating_full_bodyWork (f : List α → Measured β Nat) (x : α) (xs : List α) :
    bodyWork (forceThunks (accumulating f x xs).1).2 =
      PositionalPermutations.triangle (xs.length+1) +
        ((List.permutations'Aux x xs).map (fun ys => (f ys).2)).sum := by
  rw [bodyWork, accumulating_all_payloadCells, accumulating_all_callbacks]

/-- Open accumulating recipes support the same identified request/cache adapter.
    The identity continuation adds no callback event and no outer mapping pass. -/
def accumulatingRecipes (x : α) (xs : List α) :
    Measured (List (Thunk (List α))) Trace := accumulate (fun ys => (ys, [])) x xs

theorem accumulatingRecipes_position (x : α) (xs : List α) (i : Nat)
    (h : i < (accumulatingRecipes x xs).1.length) :
    ((accumulatingRecipes x xs).1[i]) () =
      (insertAt x xs i, List.replicate (i+1) .payloadCons) := by
  exact (accumulate_position (fun ys => (ys, [])) x xs i h).trans (by simp)

theorem delayedBody_accumulating (x : α) (xs : List α) (f : List α → Measured β Nat)
    (i : Fin (prepare (accumulatingRecipes x xs)).1.size) :
    delayedBody (prepare (accumulatingRecipes x xs)).1 f i =
      ((f (insertAt x xs i.val)).1,
        [.selection (i.val+1)] ++ List.replicate (i.val+1) .payloadCons ++
        [.callback (f (insertAt x xs i.val)).2]) := by
  have hi : i.val < (accumulatingRecipes x xs).1.length := by
    simpa [prepare, countOuter_eq] using i.isLt
  simp only [delayedBody, selected, select_value, select_cost, force]
  change ((f (((accumulatingRecipes x xs).1[i.val]) ()).1).1,
    [.selection (i.val+1)] ++ (((accumulatingRecipes x xs).1[i.val]) ()).2 ++
      [.callback (f (((accumulatingRecipes x xs).1[i.val]) ()).1).2]) = _
  rw [accumulatingRecipes_position]

end Resources.DelayedInsertion
