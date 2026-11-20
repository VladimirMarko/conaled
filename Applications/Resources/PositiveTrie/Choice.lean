import Applications.Resources.Measured
import Applications.Search.PositiveTrie.Normalized

/-!
# Actual root-first choice

Entries include nil calls. Path wrappers are constructed only when a successful
child answer is lifted; the fixed terminal one has zero wrapper tariff. A true
root skips both children, and a successful left answer skips the right child.
Raw padding can force a whole failed traversal. Normalization, proved separately
from raw semantics, removes precisely those nonempty failed subtrees.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.Choice

open Search.PositiveTrie Numerals.PositiveArithmetic

abbrev Cost := Nat × Nat

def run : KeySet → Measured (Option PosNum) Cost
  | .nil => (none, (1, 0))
  | .node true _ _ => (some .one, (1, 0))
  | .node false left right =>
      bind ((), (1, 0)) (fun _ =>
        bind (run left) (fun
          | some key => (some (.bit0 key), (0, 1))
          | none => bind (run right) (fun
              | some key => (some (.bit1 key), (0, 1))
              | none => (none, (0, 0)))))

theorem run_nil : run .nil = (none, (1, 0)) := rfl

theorem run_true_node (left right : KeySet) :
    run (.node true left right) = (some .one, (1, 0)) := rfl

theorem run_value (tree : KeySet) : (run tree).1 = KeySet.choose tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value with
      | true => rfl
      | false =>
          cases hl : KeySet.choose left <;> cases hr : KeySet.choose right <;>
            simp only [run, bind_value, ihl, ihr, KeySet.choose, hl, hr,
              Option.map_none, Option.map_some]

theorem run_false_of_left_some (left right : KeySet) {key : PosNum}
    (chosen : KeySet.choose left = some key) :
    run (.node false left right) =
      (some (.bit0 key), (1 + (run left).2.1, (run left).2.2 + 1)) := by
  simp only [run, bind, run_value, chosen]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [Prod.fst_add, Nat.add_zero]
    · simp only [Prod.snd_add, Nat.zero_add]

theorem calls_false_of_left_none (left right : KeySet)
    (absent : KeySet.choose left = none) :
    (run (.node false left right)).2.1 = 1 + (run left).2.1 + (run right).2.1 := by
  cases hr : KeySet.choose right <;>
    simp [run, bind, run_value, absent, hr, Nat.add_assoc]

theorem run_calls_le (tree : KeySet) : (run tree).2.1 ≤ 2 * tree.numNodes + 1 := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value with
      | true => simp [run]
      | false =>
          cases hl : KeySet.choose left with
          | some key =>
              rw [run_false_of_left_some left right hl]
              simp only [BinaryTree.numNodes]
              omega
          | none =>
              rw [calls_false_of_left_none left right hl]
              simp only [BinaryTree.numNodes]
              omega

theorem run_of_none {tree : KeySet} (absent : KeySet.choose tree = none) :
    run tree = (none, (2 * tree.numNodes + 1, 0)) := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value with
      | true => simp [KeySet.choose] at absent
      | false =>
          have allAbsent := (KeySet.choose_none_iff (.node false left right)).mp absent
          have hl : KeySet.choose left = none :=
            (KeySet.choose_none_iff left).mpr (fun key => allAbsent (.bit0 key))
          have hr : KeySet.choose right = none :=
            (KeySet.choose_none_iff right).mpr (fun key => allAbsent (.bit1 key))
          simp [run, bind, ihl hl, ihr hr, Prod.mk_add_mk, BinaryTree.numNodes,
            Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          omega

theorem run_wrappers {tree : KeySet} {key : PosNum} (chosen : KeySet.choose tree = some key) :
    (run tree).2.2 + 1 = bitLength key := by
  induction tree generalizing key with
  | nil => simp [KeySet.choose] at chosen
  | node value left right ihl ihr =>
      cases value with
      | true =>
          simp only [KeySet.choose, Option.some.injEq] at chosen
          subst key
          rfl
      | false =>
          cases hl : KeySet.choose left with
          | some next =>
              simp only [KeySet.choose, hl, Option.some.injEq] at chosen
              subst key
              rw [run_false_of_left_some left right hl]
              have h := ihl hl
              simp only [bitLength_bit0]
              omega
          | none =>
              cases hr : KeySet.choose right with
              | none => simp [KeySet.choose, hl, hr] at chosen
              | some next =>
                  simp only [KeySet.choose, hl, hr, Option.map_some, Option.some.injEq] at chosen
                  subst key
                  have h := ihr hr
                  simp only [run, bind, run_of_none hl, run_value, hr,
                    Prod.snd_add, Nat.zero_add, bitLength_bit1]
                  omega

theorem eq_nil_of_normalized_none {tree : KeySet} (normal : KeySet.Normalized tree)
    (absent : KeySet.choose tree = none) : tree = .nil := by
  by_contra nonempty
  obtain ⟨key, present⟩ := KeySet.exists_mem_of_normalized normal nonempty
  have missing := (KeySet.choose_none_iff tree).mp absent key
  rw [present] at missing
  cases missing

theorem run_calls_add_one_le_height {tree : KeySet} (normal : KeySet.Normalized tree)
    (nonempty : tree ≠ .nil) : (run tree).2.1 + 1 ≤ 2 * tree.height := by
  induction tree with
  | nil => exact (nonempty rfl).elim
  | node value left right ihl ihr =>
      cases value with
      | true =>
          change 1 + 1 ≤ 2 * (max left.height right.height + 1)
          omega
      | false =>
          by_cases emptyLeft : left = .nil
          · subst left
            have rightNonempty : right ≠ .nil := by
              rcases normal.2.2 with impossible | impossible | good
              · cases impossible
              · exact (impossible rfl).elim
              · exact good
            have h := ihr normal.2.1 rightNonempty
            rw [calls_false_of_left_none .nil right rfl, run_nil]
            simp only [BinaryTree.height, Nat.zero_max]
            omega
          · have h := ihl normal.1 emptyLeft
            cases selected : KeySet.choose left with
            | none => exact (emptyLeft (eq_nil_of_normalized_none normal.1 selected)).elim
            | some key =>
                rw [run_false_of_left_some left right selected]
                simp only [BinaryTree.height]
                have hm := Nat.le_max_left left.height right.height
                omega

theorem run_calls_le_height {tree : KeySet} (normal : KeySet.Normalized tree) :
    (run tree).2.1 ≤ 2 * tree.height + 1 := by
  by_cases empty : tree = .nil
  · subst tree
    exact Nat.le_refl 1
  · have h := run_calls_add_one_le_height normal empty
    omega

theorem run_calls_le_of_bitLength {tree : KeySet} (normal : KeySet.Normalized tree)
    (bound : Nat) (bounded : ∀ key, KeySet.mem key tree = true → bitLength key ≤ bound) :
    (run tree).2.1 ≤ 2 * bound + 1 := by
  have hh := KeySet.height_le_of_bitLength normal bound bounded
  have hc := run_calls_le_height normal
  omega

theorem run_calls_add_one_le_of_bitLength {tree : KeySet} (normal : KeySet.Normalized tree)
    (nonempty : tree ≠ .nil) (bound : Nat)
    (bounded : ∀ key, KeySet.mem key tree = true → bitLength key ≤ bound) :
    (run tree).2.1 + 1 ≤ 2 * bound := by
  have hh := KeySet.height_le_of_bitLength normal bound bounded
  have hc := run_calls_add_one_le_height normal nonempty
  omega

end Resources.PositiveTrie.Choice
