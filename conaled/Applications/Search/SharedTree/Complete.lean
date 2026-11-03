import Applications.Search.SharedTree.Basic

/-!
# Shared complete trees

The independent value specification unfolds both children. The execution
recurses only once, then stores the same returned root in both child fields.
Its observation counts recursive visits, including the empty case; fresh-cell
allocation is separately established by the exact change of the store frontier.
Each read, allocation and natural-number operation is a modeled primitive.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree

variable {α : Type}

def completeValue (x : α) : Nat → BinaryTree α
  | 0 => .nil
  | d + 1 => .node x (completeValue x d) (completeValue x d)

theorem completeValue_height (x : α) (d : Nat) :
    (completeValue x d).height = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [completeValue, ih]

/-- Unfolded occurrences, not distinct graph cells. -/
theorem completeValue_nodes (x : α) (d : Nat) :
    (completeValue x d).numNodes + 1 = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [completeValue, BinaryTree.numNodes]
      omega

def completeRun (x : α) : Nat → Store α → Resources.Measured (Store α × Root) Nat
  | 0, s => ((s, none), 1)
  | d + 1, s =>
      let q := completeRun x d s
      (allocate q.1.1 x q.1.2 q.1.2, q.2 + 1)

theorem completeRun_correct (x : α) (d : Nat) (s : Store α) :
    Represents (completeRun x d s).1.1.heap (completeRun x d s).1.2
      (completeValue x d) ∧
    Durability.Extends s.heap (completeRun x d s).1.1.heap ∧
    (completeRun x d s).1.1.next = s.next + d ∧
    (completeRun x d s).2 = d + 1 := by
  induction d generalizing s with
  | zero => exact ⟨.nil, .refl s.heap, by simp [completeRun], rfl⟩
  | succ d ih =>
      obtain ⟨rep, extension, frontier, visits⟩ := ih s
      refine ⟨allocate_represents rep rep x,
        extension.trans (allocate_extends _ _ _ _), ?_, ?_⟩
      · change (allocate _ x _ _).1.next = s.next + (d + 1)
        rw [allocate_next, frontier]
        omega
      · change (completeRun x d s).2 + 1 = d + 1 + 1
        rw [visits]

/-- Every separately retained old root remains observable after construction. -/
theorem completeRun_retains (x : α) (d : Nat) {s : Store α}
    {old : Root} {t : BinaryTree α} (h : Represents s.heap old t) :
    Represents (completeRun x d s).1.1.heap old t :=
  h.mono (completeRun_correct x d s).2.1

/-- Sharing is equality of the actual stored roots, not just equal tree values. -/
theorem completeRun_children (x : α) (d : Nat) (s : Store α) :
    read (completeRun x (d + 1) s).1.1 (completeRun x (d + 1) s).1.2 =
      some ((x, (completeRun x d s).1.2), (completeRun x d s).1.2) :=
  read_allocate _ x _ _

theorem completeRun_last_root (x : α) (d : Nat) (s : Store α) :
    (completeRun x (d + 1) s).1.2 = some (s.next + d) := by
  change (allocate _ x _ _).2 = some (s.next + d)
  rw [allocate_root, (completeRun_correct x d s).2.2.1]

end Search.SharedTree
