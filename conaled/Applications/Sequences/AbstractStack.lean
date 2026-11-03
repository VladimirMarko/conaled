import Applications.Resources.Measured
import SquareKit.Relations

/-!
# Stack operations and a representation-independent append

The PFDS stack interface retains empty-operation failure. Operations and their
list-observation laws are separate. The generic append only calls that interface;
its explicit recursion fuel is sufficient whenever it bounds the observed left
length. The measure counts stack primitive invocations, assigning one unit to
each call of `isEmpty`, `head`, `tail`, and `cons`. It is not machine time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.AbstractStack
universe u
variable {α S : Type u}

structure Ops (α S : Type u) where
  empty : S
  isEmpty : S → Bool
  cons : α → S → S
  head : S → Option α
  tail : S → Option S

/-- Optional tail distinguishes empty failure from a successful empty result. -/
def listTail : List α → Option (List α)
  | [] => none
  | _ :: xs => some xs

def lists (α : Type u) : Ops α (List α) where
  empty := []
  isEmpty := List.isEmpty
  cons := List.cons
  head := List.head?
  tail := listTail

/-- Laws permit representation invariants and need not choose a total decoder. -/
structure Laws (ops : Ops α S) (rel : S → List α → Prop) : Prop where
  empty : rel ops.empty []
  isEmpty : ∀ s xs, rel s xs → ops.isEmpty s = xs.isEmpty
  cons : ∀ x s xs, rel s xs → rel (ops.cons x s) (x :: xs)
  head : ∀ s xs, rel s xs → ops.head s = xs.head?
  tail_nil : ∀ s, rel s [] → ops.tail s = none
  tail_cons : ∀ s x xs, rel s (x :: xs) →
    ∃ t, ops.tail s = some t ∧ rel t xs

theorem lists_laws (α : Type u) : Laws (lists α) Eq where
  empty := rfl
  isEmpty _ _ h := congrArg List.isEmpty h
  cons _ _ _ h := congrArg _ h
  head _ _ h := congrArg List.head? h
  tail_nil _ h := by cases h; rfl
  tail_cons s x xs h := by cases h; exact ⟨xs, rfl, rfl⟩

/-- Actual operator execution. Fuel exhaustion is separate from empty success. -/
def appendRun (ops : Ops α S) : Nat → S → S → Resources.Measured (Option S) Nat
  | 0, s, t => if ops.isEmpty s then (some t, 1) else (none, 1)
  | n + 1, s, t =>
      if ops.isEmpty s then (some t, 1)
      else match ops.head s with
        | none => (none, 2)
        | some x => match ops.tail s with
          | none => (none, 3)
          | some q =>
              let out := appendRun ops n q t
              match out.1 with
              | none => (none, out.2 + 3)
              | some r => (some (ops.cons x r), out.2 + 4)

/-- Any sufficient bound terminates with the concatenated observation.
The count comes from the actual calls, including the final emptiness test. -/
theorem appendRun_correct {ops : Ops α S} {rel : S → List α → Prop}
    (laws : Laws ops rel) {s t : S} {xs ys : List α}
    (hs : rel s xs) (ht : rel t ys) {fuel : Nat} (enough : xs.length ≤ fuel) :
    ∃ r, appendRun ops fuel s t = (some r, 4 * xs.length + 1) ∧
      rel r (xs ++ ys) := by
  induction xs generalizing s fuel with
  | nil =>
      refine ⟨t, ?_, ht⟩
      have he := laws.isEmpty s [] hs
      cases fuel <;> simp [appendRun, he]
  | cons x xs ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          obtain ⟨q, hq, hr⟩ := laws.tail_cons s x xs hs
          obtain ⟨r, run, rep⟩ := ih hr (Nat.le_of_succ_le_succ enough)
          refine ⟨ops.cons x r, ?_, laws.cons x r (xs ++ ys) rep⟩
          have he := laws.isEmpty s (x :: xs) hs
          have hh := laws.head s (x :: xs) hs
          simp only [appendRun, he, List.isEmpty_cons, Bool.false_eq_true,
            ↓reduceIte, hh, List.head?_cons, hq, run, List.length_cons]
          congr 1

def representation (rel : S → List α → Prop) : Relational.RelRep := ⟨S, List α, rel⟩

def optionalRepresentation (rel : S → List α → Prop) : Relational.RelRep where
  R := Option S
  S := Option (List α)
  Rel out value := match out, value with
    | none, none => True
    | some r, some xs => rel r xs
    | _, _ => False

/-- The bound belongs to the input contract, not to a hidden decoder. -/
def appendInput (rel : S → List α → Prop) (fuel : Nat) : Relational.RelRep where
  R := S × S
  S := List α × List α
  Rel input value := rel input.1 value.1 ∧ rel input.2 value.2 ∧ value.1.length ≤ fuel

def appendSquare {ops : Ops α S} {rel : S → List α → Prop}
    (laws : Laws ops rel) (fuel : Nat) :
    Relational.RelSquare (appendInput rel fuel) (optionalRepresentation rel) where
  impl input := (appendRun ops fuel input.1 input.2).1
  spec value := some (value.1 ++ value.2)
  preserves := by
    intro input value h
    obtain ⟨r, run, rep⟩ := appendRun_correct laws h.1 h.2.1 h.2.2
    rw [run]
    exact rep

def headSquare {ops : Ops α S} {rel : S → List α → Prop} (laws : Laws ops rel) :
    Relational.RelSquare (optionalRepresentation rel) ⟨Option α, Option α, Eq⟩ where
  impl out := out.bind ops.head
  spec value := value.bind List.head?
  preserves := by
    intro out value h
    cases out with
    | none => cases value with
      | none => rfl
      | some xs => exact False.elim h
    | some r => cases value with
      | none => exact False.elim h
      | some xs => exact laws.head r xs h

/-- Pasting the two existing relational contracts gives an observable client. -/
theorem appendHead_correct {ops : Ops α S} {rel : S → List α → Prop}
    (laws : Laws ops rel) {s t : S} {xs ys : List α}
    (hs : rel s xs) (ht : rel t ys) {fuel : Nat} (enough : xs.length ≤ fuel) :
    ((appendRun ops fuel s t).1.bind ops.head) = (xs ++ ys).head? :=
  (Relational.compose (headSquare laws) (appendSquare laws fuel)).preserves
    (r := (s, t)) (s := (xs, ys)) ⟨hs, ht, enough⟩

/-- The direct pattern-matching realization is ordinary list concatenation. -/
def appendDirect : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: appendDirect xs ys

theorem appendDirect_eq (xs ys : List α) : appendDirect xs ys = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem lists_appendRun (xs ys : List α) {fuel : Nat} (enough : xs.length ≤ fuel) :
    appendRun (lists α) fuel xs ys = (some (appendDirect xs ys), 4 * xs.length + 1) := by
  obtain ⟨r, run, rep⟩ := appendRun_correct (lists_laws α) rfl rfl enough
  change r = xs ++ ys at rep
  simpa [rep, appendDirect_eq] using run

/-- The source's second stack realization, with no use of the List constructors. -/
inductive Stack (α : Type u) where
  | nil
  | cons (head : α) (tail : Stack α)
  deriving DecidableEq, Repr

def Stack.toList : Stack α → List α
  | .nil => []
  | .cons x s => x :: s.toList

def custom (α : Type u) : Ops α (Stack α) where
  empty := .nil
  isEmpty := fun s => match s with | .nil => true | .cons _ _ => false
  cons := .cons
  head := fun s => match s with | .nil => none | .cons x _ => some x
  tail := fun s => match s with | .nil => none | .cons _ s => some s

theorem custom_laws (α : Type u) : Laws (custom α) (fun s xs => s.toList = xs) where
  empty := rfl
  isEmpty s xs h := by cases h; cases s <;> rfl
  cons _ _ _ h := congrArg _ h
  head s xs h := by cases h; cases s <;> rfl
  tail_nil s h := by cases s with
    | nil => rfl
    | cons x s => cases h
  tail_cons s x xs h := by
    cases s with
    | nil => cases h
    | cons y s =>
        exact ⟨s, rfl, (List.cons.inj h).2⟩

theorem custom_appendRun {s t : Stack α} {fuel : Nat} (enough : s.toList.length ≤ fuel) :
    ∃ r, appendRun (custom α) fuel s t = (some r, 4 * s.toList.length + 1) ∧
      r.toList = appendDirect s.toList t.toList := by
  simpa only [appendDirect_eq] using appendRun_correct (custom_laws α) rfl rfl enough

end Sequences.AbstractStack
