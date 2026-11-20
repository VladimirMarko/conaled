import Applications.Search.RedBlack.Depth
import Applications.Search.RedBlack.Ordering

/-!
# Parent colors and structural depth of source red-black trees

These examples keep color invariants separate from ordering. Their node counts
and path lengths describe immutable mathematical trees, not execution timings.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.RedBlackShapes

open RBTree RBTree.RBColor RBTree.RBNode Search.RedBlack

def redSingleton : Tree Nat Nat := .node .red .nil (4, 40) .nil

def blackSingleton : Tree Nat Nat := .node .black .nil (4, 40) .nil

theorem red_singleton_parent_colors :
    RB redSingleton .black 0 ∧ ¬ RB redSingleton .red 0 := by
  constructor
  · exact RB.red 4 40 (RB.nil .red) (RB.nil .red)
  · rw [redSingleton, RB_red_node_iff]
    rintro ⟨h, _, _⟩
    cases h

theorem nil_parent_colors : RB (.nil : Tree Nat Nat) .red 0 ∧
    RB (.nil : Tree Nat Nat) .black 0 :=
  ⟨RB.nil .red, RB.nil .black⟩

theorem nil_not_nearly : ¬ NearlyRB (.nil : Tree Nat Nat) 0 :=
  not_nearlyRB_nil 0

theorem black_singleton_parent_colors :
    RB blackSingleton .red 1 ∧ RB blackSingleton .black 1 ∧
      ¬ RB blackSingleton .red 0 := by
  have h : RB blackSingleton .red 1 :=
    RB.black .red 4 40 (RB.nil .black) (RB.nil .black)
  refine ⟨h, RB_blacken_parent h, ?_⟩
  rw [blackSingleton, RB_black_node_iff]
  rintro ⟨n, bad, _, _⟩
  exact Nat.noConfusion bad

def bothRedChildren : Tree Nat Nat :=
  .node .red (.node .red .nil (1, 10) .nil) (2, 20)
    (.node .red .nil (3, 30) .nil)

theorem both_red_children_nearly : NearlyRB bothRedChildren 0 :=
  NearlyRB.red 2 20 (RB.red 1 10 (RB.nil .red) (RB.nil .red))
    (RB.red 3 30 (RB.nil .red) (RB.nil .red))

theorem both_red_children_not_RB : ¬ RB bothRedChildren .black 0 := by
  intro h
  have hl := (RB_red_node_iff.mp h).2.1
  have bad := (RB_red_node_iff.mp hl).1
  cases bad

theorem root_blackening_changes_height : (∃ n, RB (makeBlack redSingleton) .red n) ∧
    RB (makeBlack redSingleton) .red 1 ∧ ¬ RB (makeBlack redSingleton) .red 0 := by
  refine ⟨RB_blacken_root red_singleton_parent_colors.1, ?_, ?_⟩
  · rw [redSingleton, makeBlack_node]
    exact RB.black .red 4 40 (RB.nil .black) (RB.nil .black)
  · rw [redSingleton, makeBlack_node, RB_black_node_iff]
    rintro ⟨n, bad, _, _⟩
    exact Nat.noConfusion bad

theorem root_blackening_nil : RB (makeBlack (.nil : Tree Nat Nat)) .red 0 ∧
    ∃ n, RB (makeBlack (.nil : Tree Nat Nat)) .red n := by
  constructor
  · rw [makeBlack_nil]
    exact RB.nil .red
  · exact RB_blacken_root (RB.nil .black)

theorem insertion_shape_components :
    NearlyRB (ins (fun _ _ => true) 7 70 redSingleton) 0 ∧
      RB (ins (fun _ _ => true) 7 70 blackSingleton) .black 1 :=
  ⟨(ins_RB (fun _ _ => true) 7 70 redSingleton 0).1 red_singleton_parent_colors.1,
    (ins_RB (fun _ _ => true) 7 70 blackSingleton 1).2 black_singleton_parent_colors.1⟩

theorem raw_insertion_can_need_root_repair :
    ¬ RB (ins (fun _ _ => true) 7 70 redSingleton) .black 0 := by
  intro h
  change RB (.node .red (.node .red .nil (7, 70) .nil) (4, 40) .nil : Tree Nat Nat)
    .black 0 at h
  have bad := (RB_red_node_iff.mp (RB_red_node_iff.mp h).2.1).1
  cases bad

theorem insertion_restores_black_root :
    (∃ n, RB (insert (fun _ _ => true) 7 70 blackSingleton) .red n) ∧
      ∃ n, RB (insert (fun _ _ => false) 7 70 (.nil : Tree Nat Nat)) .red n :=
  ⟨insert_RB (fun _ _ => true) 7 70 black_singleton_parent_colors.1,
    insert_RB (fun _ _ => false) 7 70 (RB.nil .red)⟩

def duplicateLeft : Tree Int Nat :=
  .node .black (.node .red .nil (0, 10) .nil) (0, 20) .nil

theorem duplicate_left_shape : RB duplicateLeft .red 1 :=
  RB.black .red 0 20 (RB.red 0 10 (RB.nil .red) (RB.nil .red)) (RB.nil .black)

theorem duplicate_left_not_BST : ¬ BST (fun key : Int => key) duplicateLeft := by
  intro h
  have bounds := (bst_node_iff (fun key : Int => key) .black
    (.node .red .nil (0, 10) .nil) 0 20 .nil).mp h
  have bad := (forallT_node (fun key (_ : Nat) => key < (0 : Int))
    .red .nil 0 10 .nil).mp bounds.2.2.1
  exact (lt_irrefl (0 : Int)) bad.1

theorem shape_does_not_imply_order :
    RB duplicateLeft .red 1 ∧ ¬ BST (fun key : Int => key) duplicateLeft :=
  ⟨duplicate_left_shape, duplicate_left_not_BST⟩

theorem repair_right_overlap :
    RB (balance .black .nil 0 0 bothRedChildren) .black 1 :=
  balance_black_right 0 0 (RB.nil .black) both_red_children_nearly

theorem repair_left_overlap :
    RB (balance .black bothRedChildren 4 40 .nil) .black 1 :=
  balance_black_left 4 40 both_red_children_nearly (RB.nil .black)

def shorterRight : Tree Nat Nat :=
  .node .black (.node .red .nil (1, 10) .nil) (2, 20) .nil

theorem shorter_right_RB : RB shorterRight .red 1 :=
  RB.black .red 2 20 (RB.red 1 10 (RB.nil .red) (RB.nil .red)) (RB.nil .black)

theorem shorter_right_depths : mindepth shorterRight = 1 ∧ height shorterRight = 2 := by
  constructor
  · simp only [shorterRight, mindepth_node, mindepth_nil]
    rfl
  · simp only [shorterRight, height_node, height_nil]
    rfl

theorem shorter_right_bounds : 1 ≤ mindepth shorterRight ∧ height shorterRight ≤ 2 * 1 ∧
    height shorterRight ≤ 2 * mindepth shorterRight + 1 :=
  ⟨shorter_right_RB.blackHeight_le_mindepth, shorter_right_RB.height_le_twice_blackHeight,
    redblack_balanced shorter_right_RB⟩

theorem erased_shorter_right : BinaryTree.height (eraseColors shorterRight) = 2 ∧
    BinaryTree.numNodes (eraseColors shorterRight) = 2 ∧
    BinaryTree.height (eraseColors shorterRight) ≤
      2 * (BinaryTree.numNodes (eraseColors shorterRight) + 1).log2 := by
  refine ⟨?_, ?_, shorter_right_RB.erased_height_log_bound⟩
  · rw [eraseColors_height]
    exact shorter_right_depths.2
  · rw [eraseColors_numNodes]
    rfl

theorem red_singleton_height : height redSingleton = 1 ∧ height redSingleton ≤ 2 * 0 + 1 := by
  constructor
  · rw [redSingleton, height_node, height_nil]
    rfl
  · exact red_singleton_parent_colors.1.height_le_blackHeight

theorem empty_depths : mindepth (.nil : Tree Nat Nat) = 0 ∧
    height (.nil : Tree Nat Nat) = 0 := ⟨mindepth_nil, height_nil⟩

theorem black_singleton_depths : mindepth blackSingleton = 1 ∧ height blackSingleton = 1 := by
  constructor
  · rw [blackSingleton, mindepth_node, mindepth_nil]
    rfl
  · rw [blackSingleton, height_node, height_nil]
    rfl

theorem empty_log_endpoint :
    height (.nil : Tree Nat Nat) ≤ 2 * ((.nil : Tree Nat Nat).size + 1).log2 ∧
      2 * ((.nil : Tree Nat Nat).size + 1).log2 = 0 :=
  ⟨(RB.nil .red).height_log_bound, rfl⟩

theorem red_singleton_log_endpoint :
    height redSingleton ≤ 2 * (redSingleton.size + 1).log2 ∧
      2 * (redSingleton.size + 1).log2 = 2 :=
  ⟨red_singleton_parent_colors.1.height_log_bound, rfl⟩

theorem black_singleton_log_endpoint :
    height blackSingleton ≤ 2 * (blackSingleton.size + 1).log2 ∧
      2 ^ 1 ≤ blackSingleton.size + 1 :=
  ⟨black_singleton_parent_colors.1.height_log_bound,
    black_singleton_parent_colors.1.power_blackHeight_le_size⟩

end Examples.RedBlackShapes
