import Applications.Resources.PositivePaths
import Applications.Resources.ListAppend
import Applications.Resources.PositiveTrie.Traversal

/-!
# Actual finite-trie enumerations

Map enumeration evaluates the left child, then the right child, forms the root
cons on the returned right tail, and appends the returned left list. Each append
gets its own terminal offset. Set enumeration constructs right, root, left and
retains an arbitrary input tail without scanning it. These are distinct source
recurrences with distinct prefix and list work, despite related output orders.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.Enumeration

open Search.PositiveTrie Numerals.PositiveArithmetic Numerals.PositivePaths Traversal

universe u
variable {α : Type u}

namespace Map

/-- Entries, prefix entries/wrappers, append entries/copies, fresh occupied cons. -/
abbrev Counts := Nat × Nat × Nat × Nat × Nat × Nat

def prefixRun (p branch : PosNum) : Measured PosNum Counts :=
  reweight (fun cost => (0, cost.1, cost.2, 0, 0, 0)) (Resources.PositivePaths.appendRun p branch)

theorem prefixRun_value (p branch : PosNum) : (prefixRun p branch).1 = append p branch :=
  Resources.PositivePaths.appendRun_value p branch

theorem prefixRun_counts (p branch : PosNum) :
    (prefixRun p branch).2 = (0, bitLength p, bitLength p - 1, 0, 0, 0) := by
  simp only [prefixRun, reweight, Resources.PositivePaths.appendRun_cost]

/-- The affine terminal charge is applied to this invocation, not to summed copies. -/
def appendRun (left right : List (PosNum × α)) : Measured (List (PosNum × α)) Counts :=
  reweight (fun copies => (0, 0, 0, copies + 1, copies, 0)) (ListAppend.copies left right)

theorem appendRun_value (left right : List (PosNum × α)) : (appendRun left right).1 = left ++ right := by
  simp only [appendRun, reweight, ListAppend.copies_exact]

theorem appendRun_counts (left right : List (PosNum × α)) :
    (appendRun left right).2 = (0, 0, 0, left.length + 1, left.length, 0) := by
  simp only [appendRun, reweight, ListAppend.copies_exact]

def payloadRun (p : PosNum) (value : Option α) (tail : List (PosNum × α)) :
    Measured (List (PosNum × α)) Counts :=
  match value with
  | none => (tail, (0, 0, 0, 0, 0, 0))
  | some value => ((p, value) :: tail, (0, 0, 0, 0, 0, 1))

theorem payloadRun_counts (p : PosNum) (value : Option α) (tail : List (PosNum × α)) :
    (payloadRun p value tail).2 = (0, 0, 0, 0, 0, if value.isSome then 1 else 0) := by
  cases value <;> rfl

def runFrom : SparseMap α → PosNum → Measured (List (PosNum × α)) Counts
  | .nil, _ => ([], (1, 0, 0, 0, 0, 0))
  | .node value left right, p =>
      bind ((), (1, 0, 0, 0, 0, 0)) (fun _ =>
        bind (prefixRun p (.bit0 .one)) (fun leftKey =>
          bind (runFrom left leftKey) (fun leftList =>
            bind (prefixRun p (.bit1 .one)) (fun rightKey =>
              bind (runFrom right rightKey) (fun rightList =>
                bind (payloadRun p value rightList) (fun rootTail =>
                  appendRun leftList rootTail))))))

def run (tree : SparseMap α) : Measured (List (PosNum × α)) Counts := runFrom tree .one

theorem runFrom_value (tree : SparseMap α) (p : PosNum) :
    (runFrom tree p).1 = SparseMap.elementsFrom tree p := by
  induction tree generalizing p with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;> simp only [runFrom, bind_value, prefixRun_value, payloadRun,
        appendRun_value, SparseMap.elementsFrom, ihl, ihr]

theorem run_value (tree : SparseMap α) : (run tree).1 = SparseMap.elements tree :=
  runFrom_value tree .one

theorem runFrom_length (tree : SparseMap α) (p : PosNum) :
    (runFrom tree p).1.length = SparseMap.cardinal tree := by
  rw [runFrom_value, SparseMap.elementsFrom_eq_rawEntries, List.length_map, SparseMap.rawEntries_length]

theorem runFrom_counts_add (tree : SparseMap α) (p : PosNum) :
    let counts := (runFrom tree p).2
    (counts.1, counts.2.1, counts.2.2.1 + 2 * tree.numNodes,
      counts.2.2.2.1, counts.2.2.2.2.1, counts.2.2.2.2.2) =
      (2 * tree.numNodes + 1, 2 * prefixMass tree p, 2 * prefixMass tree p,
        copiedCells tree + tree.numNodes, copiedCells tree, SparseMap.cardinal tree) := by
  induction tree generalizing p with
  | nil => simp [runFrom, prefixMass_nil, BinaryTree.numNodes, SparseMap.cardinal, copiedCells]
  | node value left right ihl ihr =>
      have hl := ihl (append p (.bit0 .one))
      have hr := ihr (append p (.bit1 .one))
      simp only [Prod.mk.injEq] at hl hr
      have positive := bitLength_pos p
      simp only [runFrom, bind, prefixRun_value, prefixRun_counts, appendRun_counts,
        payloadRun_counts, runFrom_length, BinaryTree.numNodes, SparseMap.cardinal_node,
        prefixMass_node, copiedCells]
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem runFrom_counts (tree : SparseMap α) (p : PosNum) :
    (runFrom tree p).2 =
      (2 * tree.numNodes + 1, 2 * prefixMass tree p, 2 * (prefixMass tree p - tree.numNodes),
        copiedCells tree + tree.numNodes, copiedCells tree, SparseMap.cardinal tree) := by
  have h := runFrom_counts_add tree p
  have lower := numNodes_le_prefixMass tree p
  simp only [Prod.mk.injEq] at h
  ext <;> dsimp only <;> omega

theorem run_counts (tree : SparseMap α) :
    (run tree).2 =
      (2 * tree.numNodes + 1, 2 * prefixMass tree .one, 2 * (prefixMass tree .one - tree.numNodes),
        copiedCells tree + tree.numNodes, copiedCells tree, SparseMap.cardinal tree) :=
  runFrom_counts tree .one

def outerWork (counts : Counts) : Nat :=
  counts.1 + counts.2.1 + counts.2.2.1 + counts.2.2.2.1 + counts.2.2.2.2.1 + counts.2.2.2.2.2

theorem runFrom_outer_work (tree : SparseMap α) (p : PosNum) :
    outerWork (runFrom tree p).2 =
      4 * prefixMass tree p + tree.numNodes + 2 * copiedCells tree + SparseMap.cardinal tree + 1 := by
  have h := runFrom_counts_add tree p
  simp only [Prod.mk.injEq] at h
  dsimp only [outerWork]
  omega

theorem run_outer_work_le {tree : SparseMap α} (normal : SparseMap.Normalized tree) (bits : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bits) :
    outerWork (run tree).2 ≤
      4 * SparseMap.cardinal tree * bits ^ 2 + 3 * SparseMap.cardinal tree * bits + SparseMap.cardinal tree + 1 := by
  have hn := SparseMap.numNodes_le_cardinal_mul normal bits bounded
  have hm := map_prefixMass_one_le normal bits bounded
  have hc := copiedCells_le tree bits bounded
  rw [run, runFrom_outer_work]
  simp only [Nat.mul_assoc]
  omega

end Map

namespace Set

/-- Entries, direct prefix wrappers, reversal entries/wrappers, fresh cons. -/
abbrev Counts := Nat × Nat × Nat × Nat × Nat

def payloadRun (r : PosNum) (occupied : Bool) (tail : List PosNum) : Measured (List PosNum) Counts :=
  if occupied then
    bind (reweight (fun cost => (0, 0, cost.1, cost.2, 0)) (Resources.PositivePaths.reverseRun r))
      (fun key => (key :: tail, (0, 0, 0, 0, 1)))
  else (tail, (0, 0, 0, 0, 0))

theorem payloadRun_value (r : PosNum) (occupied : Bool) (tail : List PosNum) :
    (payloadRun r occupied tail).1 = if occupied then reverse r :: tail else tail := by
  cases occupied <;> simp only [payloadRun, Bool.false_eq_true, ↓reduceIte, bind_value,
    reweight_value, Resources.PositivePaths.reverseRun_value]

theorem payloadRun_counts (r : PosNum) (occupied : Bool) (tail : List PosNum) :
    (payloadRun r occupied tail).2 =
      (0, 0, if occupied then bitLength r else 0,
        if occupied then bitLength r - 1 else 0, if occupied then 1 else 0) := by
  cases occupied <;> simp only [payloadRun, Bool.false_eq_true, ↓reduceIte, bind, reweight,
    Resources.PositivePaths.reverseRun_cost, Prod.mk_add_mk, Nat.zero_add, Nat.add_zero]

def runFrom : KeySet → PosNum → List PosNum → Measured (List PosNum) Counts
  | .nil, _, tail => (tail, (1, 0, 0, 0, 0))
  | .node occupied left right, r, tail =>
      bind ((), (1, 0, 0, 0, 0)) (fun _ =>
        bind (.bit1 r, (0, 1, 0, 0, 0)) (fun rightKey =>
          bind (runFrom right rightKey tail) (fun rightTail =>
            bind (payloadRun r occupied rightTail) (fun rootTail =>
              bind (.bit0 r, (0, 1, 0, 0, 0)) (fun leftKey =>
                runFrom left leftKey rootTail)))))

def run (tree : KeySet) : Measured (List PosNum) Counts := runFrom tree .one []

theorem runFrom_value (tree : KeySet) (r : PosNum) (tail : List PosNum) :
    (runFrom tree r tail).1 = KeySet.elementsAcc tree r tail := by
  induction tree generalizing r tail with
  | nil => rfl
  | node occupied left right ihl ihr =>
      cases occupied <;> simp only [runFrom, bind_value, payloadRun_value,
        Bool.false_eq_true, ↓reduceIte, KeySet.elementsAcc, ihl, ihr]

theorem run_value (tree : KeySet) : (run tree).1 = KeySet.elements tree := runFrom_value tree .one []

theorem runFrom_length (tree : KeySet) (r : PosNum) (tail : List PosNum) :
    (runFrom tree r tail).1.length = KeySet.cardinal tree + tail.length := by
  rw [runFrom_value, KeySet.elementsAcc_eq_rawKeys, List.length_append, List.length_map,
    KeySet.rawKeys_length]

theorem runFrom_tail (tree : KeySet) (r : PosNum) (tail : List PosNum) :
    (runFrom tree r tail).1 = (runFrom tree r []).1 ++ tail := by
  simp only [runFrom_value, KeySet.elementsAcc_eq_rawKeys, List.append_nil]

theorem runFrom_counts_add (tree : KeySet) (r : PosNum) (tail : List PosNum) :
    let counts := (runFrom tree r tail).2
    (counts.1, counts.2.1, counts.2.2.1, counts.2.2.2.1 + KeySet.cardinal tree, counts.2.2.2.2) =
      (2 * tree.numNodes + 1, 2 * tree.numNodes, reversalMass tree r, reversalMass tree r, KeySet.cardinal tree) := by
  induction tree generalizing r tail with
  | nil => simp [runFrom, reversalMass_nil, BinaryTree.numNodes, KeySet.cardinal]
  | node occupied left right ihl ihr =>
      have hr := ihr (.bit1 r) tail
      have hl := ihl (.bit0 r) (payloadRun r occupied (runFrom right (.bit1 r) tail).1).1
      simp only [Prod.mk.injEq] at hl hr
      have positive := bitLength_pos r
      simp only [runFrom, bind, payloadRun_counts, BinaryTree.numNodes, KeySet.cardinal_node,
        reversalMass_node]
      cases occupied <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
        ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem runFrom_counts (tree : KeySet) (r : PosNum) (tail : List PosNum) :
    (runFrom tree r tail).2 =
      (2 * tree.numNodes + 1, 2 * tree.numNodes, reversalMass tree r,
        reversalMass tree r - KeySet.cardinal tree, KeySet.cardinal tree) := by
  have h := runFrom_counts_add tree r tail
  simp only [Prod.mk.injEq] at h
  ext <;> dsimp only <;> omega

theorem run_counts (tree : KeySet) :
    (run tree).2 =
      (2 * tree.numNodes + 1, 2 * tree.numNodes, KeySet.keyMass tree,
        KeySet.keyMass tree - KeySet.cardinal tree, KeySet.cardinal tree) := by
  rw [run, runFrom_counts, reversalMass_one]

theorem runFrom_cost_independent (tree : KeySet) (r : PosNum) (leftTail rightTail : List PosNum) :
    (runFrom tree r leftTail).2 = (runFrom tree r rightTail).2 := by rw [runFrom_counts, runFrom_counts]

def outerWork (counts : Counts) : Nat :=
  counts.1 + counts.2.1 + counts.2.2.1 + counts.2.2.2.1 + counts.2.2.2.2

theorem runFrom_outer_work (tree : KeySet) (r : PosNum) (tail : List PosNum) :
    outerWork (runFrom tree r tail).2 = 4 * tree.numNodes + 2 * reversalMass tree r + 1 := by
  have h := runFrom_counts_add tree r tail
  simp only [Prod.mk.injEq] at h
  dsimp only [outerWork]
  omega

theorem run_outer_work_le {tree : KeySet} (normal : KeySet.Normalized tree) (bits : Nat)
    (bounded : ∀ key, KeySet.mem key tree = true → bitLength key ≤ bits) :
    outerWork (run tree).2 ≤ 6 * KeySet.cardinal tree * bits + 1 := by
  have hn := KeySet.numNodes_le_cardinal_mul normal bits bounded
  have hm := KeySet.keyMass_le_cardinal_mul tree bits bounded
  rw [run, runFrom_outer_work, reversalMass_one]
  simp only [Nat.mul_assoc]
  omega

end Set
end Resources.PositiveTrie.Enumeration
