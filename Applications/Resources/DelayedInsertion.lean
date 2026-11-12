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
  | innerObserve (visits : Nat)
  deriving DecidableEq, BEq, Repr

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
  | y :: ys =>
    let h := seed x (y :: ys)
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

end Resources.DelayedInsertion
