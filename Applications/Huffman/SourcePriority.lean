import Applications.Huffman.Priority

/-! Exact source leftist specialization; the source tie choices are unchanged. -/
set_option autoImplicit false
set_option warningAsError true
namespace Huffman.SourcePriority
open Bracketing Search.LeftistQueue Search.PriorityInterface
universe u
variable {α : Type u}

/-- Literal checkpoint233 two-delete/one-insert recurrence. -/
def step (q : PQ (Tree α) Nat) : PQ (Tree α) Nat :=
  match deleteQ q with
  | none => q
  | some (a, r) => match deleteQ r with
    | none => q
    | some (b, s) => insertQ (Tree.fork a.1 b.1) (a.2 + b.2) s

def loop : Nat → PQ (Tree α) Nat → PQ (Tree α) Nat
  | 0, q => q
  | k + 1, q => if singleQ q then q else loop k (step q)

def huffman (w : α → Nat) (xs : List α) : Option (Tree α) :=
  (deleteQ (loop (xs.length - 1) (makeQ (xs.map (cachedLeaf w))))).map (fun z => z.1.1)

theorem step_eq (q : PQ (Tree α) Nat) : Priority.step exactLeftist q = step q := by
  simp only [Priority.step, step, exactLeftist, Priority.insert, addListQ,
    List.foldr_cons, List.foldr_nil]
  cases h : deleteQ q with
  | none => rfl
  | some z =>
    rcases z with ⟨a, r⟩
    simp only
    cases hr : deleteQ r <;> rfl

theorem singleQ_eq (q : PQ (Tree α) Nat) : Priority.singleQ exactLeftist q = singleQ q := by
  apply Bool.eq_iff_iff.mpr
  rw [Priority.singleQ_iff, singleQ_iff]
  change (entries q).length = 1 ↔ size q = 1
  rw [entries_length]

theorem loop_eq (k : Nat) (q : PQ (Tree α) Nat) :
    Priority.loop exactLeftist k q = loop k q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih => simp only [Priority.loop, loop, singleQ_eq, step_eq, ih]

theorem huffman_eq (w : α → Nat) (xs : List α) :
    Priority.huffman exactLeftist w xs = huffman w xs := by
  unfold Priority.huffman huffman
  rw [loop_eq]
  rfl

/-- Source output inherits the independent global optimum, not an enumerated bound. -/
theorem huffman_correct (w : α → Nat) (xs : List α) (t : Tree α)
    (h : huffman w xs = some t) : Optimal w xs t :=
  Priority.huffman_correct exactLeftist w xs t (by rw [huffman_eq]; exact h)
end Huffman.SourcePriority
