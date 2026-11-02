import Applications.Search.SharedTree.Complete
import Init.Data.Nat.Log2

/-!
# Paired construction of shared size-balanced trees

`create2Run x n` constructs roots for sizes `n` and `n + 1`. It recurses once
on half the predecessor size, and allocates two parents whose child roots
reuse that same recursive pair. The base pair uses one cell. Arithmetic,
parity tests and cell allocation are modeled unit operations; the counted
visits and allocations do not assert a Lean runtime bound.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree

variable {α : Type}

/-- Every node stores the supplied value. No order hypothesis is imposed. -/
def Uniform (x : α) : BinaryTree α → Prop
  | .nil => True
  | .node y l r => y = x ∧ Uniform x l ∧ Uniform x r

/-- Every pair of child subtrees differs by at most one unfolded node. -/
def SizeBalanced : BinaryTree α → Prop
  | .nil => True
  | .node _ l r =>
      l.numNodes ≤ r.numNodes + 1 ∧ r.numNodes ≤ l.numNodes + 1 ∧
        SizeBalanced l ∧ SizeBalanced r

/-- An independent specification of the requested size, contents and balance. -/
structure Fits (x : α) (n : Nat) (t : BinaryTree α) : Prop where
  nodes : t.numNodes = n
  uniform : Uniform x t
  balanced : SizeBalanced t

theorem Fits.nil (x : α) : Fits x 0 .nil := ⟨rfl, trivial, trivial⟩

theorem Fits.node {x : α} {m n k : Nat} {l r : BinaryTree α}
    (hl : Fits x m l) (hr : Fits x n r) (size : m + n + 1 = k)
    (leftClose : m ≤ n + 1) (rightClose : n ≤ m + 1) :
    Fits x k (.node x l r) := by
  refine ⟨?_, ⟨rfl, hl.uniform, hr.uniform⟩, ?_⟩
  · simpa only [BinaryTree.numNodes, hl.nodes, hr.nodes] using size
  · exact ⟨by simpa only [hl.nodes, hr.nodes] using leftClose,
      by simpa only [hl.nodes, hr.nodes] using rightClose, hl.balanced, hr.balanced⟩

def create2Value (x : α) : Nat → BinaryTree α × BinaryTree α
  | 0 => (.nil, .node x .nil .nil)
  | n + 1 =>
      let q := create2Value x (n / 2)
      if n % 2 = 0 then (.node x q.1 q.1, .node x q.1 q.2)
      else (.node x q.1 q.2, .node x q.2 q.2)
termination_by n => n
decreasing_by omega

theorem create2Value_fits (x : α) (n : Nat) :
    Fits x n (create2Value x n).1 ∧ Fits x (n + 1) (create2Value x n).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨Fits.nil x, Fits.node (Fits.nil x) (Fits.nil x) rfl (by omega) (by omega)⟩
      | succ n =>
          obtain ⟨ha, hb⟩ := ih (n / 2) (by omega)
          rw [create2Value]
          split_ifs with even
          · exact ⟨Fits.node ha ha (by omega) (by omega) (by omega),
              Fits.node ha hb (by omega) (by omega) (by omega)⟩
          · exact ⟨Fits.node ha hb (by omega) (by omega) (by omega),
              Fits.node hb hb (by omega) (by omega) (by omega)⟩

/-- Allocate two parents, sharing any child roots supplied more than once. -/
def allocatePair (s : Store α) (x : α) (l r u v : Root) : Store α × Root × Root :=
  let a := allocate s x l r
  let b := allocate a.1 x u v
  (b.1, a.2, b.2)

theorem allocatePair_extends (s : Store α) (x : α) (l r u v : Root) :
    Durability.Extends s.heap (allocatePair s x l r u v).1.heap :=
  (allocate_extends s x l r).trans (allocate_extends _ x u v)

@[simp] theorem allocatePair_next (s : Store α) (x : α) (l r u v : Root) :
    (allocatePair s x l r u v).1.next = s.next + 2 := by
  simp only [allocatePair, allocate_next]
  omega

theorem allocatePair_represents {s : Store α} {l r u v : Root}
    {lt rt ut vt : BinaryTree α}
    (hl : Represents s.heap l lt) (hr : Represents s.heap r rt)
    (hu : Represents s.heap u ut) (hv : Represents s.heap v vt) (x : α) :
    Represents (allocatePair s x l r u v).1.heap
        (allocatePair s x l r u v).2.1 (.node x lt rt) ∧
      Represents (allocatePair s x l r u v).1.heap
        (allocatePair s x l r u v).2.2 (.node x ut vt) := by
  constructor
  · exact (allocate_represents hl hr x).mono (allocate_extends _ x u v)
  · exact allocate_represents (hu.mono (allocate_extends s x l r))
      (hv.mono (allocate_extends s x l r)) x

/-- Both parent cells expose the original supplied child roots after allocation. -/
theorem read_allocatePair (s : Store α) (x : α) (l r u v : Root) :
    read (allocatePair s x l r u v).1 (allocatePair s x l r u v).2.1 =
        some ((x, l), r) ∧
      read (allocatePair s x l r u v).1 (allocatePair s x l r u v).2.2 =
        some ((x, u), v) := by
  constructor
  · have old := allocate_lookup s x l r
    have kept := allocate_extends (allocate s x l r).1 x u v s.next ((x, l), r) old
    simpa only [allocatePair, allocate_root, read, Option.bind_some] using kept
  · exact read_allocate _ x u v

def create2Run (x : α) : Nat → Store α →
    Resources.Measured (Store α × Root × Root) Nat
  | 0, s =>
      let q := allocate s x none none
      ((q.1, none, q.2), 1)
  | n + 1, s =>
      let q := create2Run x (n / 2) s
      if n % 2 = 0 then
        (allocatePair q.1.1 x q.1.2.1 q.1.2.1 q.1.2.1 q.1.2.2, q.2 + 1)
      else
        (allocatePair q.1.1 x q.1.2.1 q.1.2.2 q.1.2.2 q.1.2.2, q.2 + 1)
termination_by n => n
decreasing_by omega

private theorem log2_step (n : Nat) :
    Nat.log2 (n + 1 + 1) = Nat.log2 (n / 2 + 1) + 1 := by
  rw [Nat.log2_def]
  have h : 2 ≤ n + 1 + 1 := by omega
  have div : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
  simp only [if_pos h, div]

theorem create2Run_correct (x : α) (n : Nat) (s : Store α) :
    Represents (create2Run x n s).1.1.heap (create2Run x n s).1.2.1
        (create2Value x n).1 ∧
      Represents (create2Run x n s).1.1.heap (create2Run x n s).1.2.2
        (create2Value x n).2 ∧
      Durability.Extends s.heap (create2Run x n s).1.1.heap ∧
      (create2Run x n s).1.1.next = s.next + 2 * Nat.log2 (n + 1) + 1 ∧
      (create2Run x n s).2 = Nat.log2 (n + 1) + 1 := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨.nil, allocate_represents .nil .nil x,
            allocate_extends s x none none, rfl, rfl⟩
      | succ n =>
          obtain ⟨ha, hb, extension, frontier, visits⟩ := ih (n / 2) (by omega) s
          rw [create2Run, create2Value]
          split_ifs with even
          · have pair := allocatePair_represents ha ha ha hb x
            refine ⟨pair.1, pair.2, extension.trans (allocatePair_extends _ _ _ _ _ _),
              ?_, ?_⟩
            · rw [allocatePair_next, frontier, log2_step]
              omega
            · rw [visits, log2_step]
          · have pair := allocatePair_represents ha hb hb hb x
            refine ⟨pair.1, pair.2, extension.trans (allocatePair_extends _ _ _ _ _ _),
              ?_, ?_⟩
            · rw [allocatePair_next, frontier, log2_step]
              omega
            · rw [visits, log2_step]

/-- The whole old heap remains an immutable prefix of the final store. -/
theorem create2Run_retains (x : α) (n : Nat) {s : Store α} {old : Root}
    {t : BinaryTree α} (h : Represents s.heap old t) :
    Represents (create2Run x n s).1.1.heap old t :=
  h.mono (create2Run_correct x n s).2.2.1

/-- Return the first root of the pair for an arbitrary requested size. -/
def balancedRun (x : α) (n : Nat) (s : Store α) :
    Resources.Measured (Store α × Root) Nat :=
  let q := create2Run x n s
  ((q.1.1, q.1.2.1), q.2)

theorem balancedRun_correct (x : α) (n : Nat) (s : Store α) :
    ∃ t, Represents (balancedRun x n s).1.1.heap (balancedRun x n s).1.2 t ∧
      Fits x n t ∧
      Durability.Extends s.heap (balancedRun x n s).1.1.heap ∧
      (balancedRun x n s).1.1.next = s.next + 2 * Nat.log2 (n + 1) + 1 ∧
      (balancedRun x n s).2 = Nat.log2 (n + 1) + 1 :=
  ⟨(create2Value x n).1, (create2Run_correct x n s).1,
    (create2Value_fits x n).1, (create2Run_correct x n s).2.2⟩

end Search.SharedTree
