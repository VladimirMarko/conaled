import Applications.Search.RedBlack.Ordering
import Applications.Search.RedBlack.Models
import Applications.Search.RedBlack.Shape

/-!
# Source colored-map ordering and observations

The cases connect the source operations to strict subtree bounds and the
accepted map observations. Key decoding is separate from payload structure.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RedBlackMaps
open Search.RedBlack RBTree.RBColor

/-- Independently chosen signed keys lie on their respective sides of zero. -/
def signedTree : Tree Int Nat :=
  .node black (.node red .nil (-2, 7) .nil) (0, 0)
    (.node red .nil (3, 9) .nil)

theorem signed_tree_bst : BST id signedTree := by
  simp [signedTree, bst_node_iff, ForallT, RBTree.RBNode.All]

theorem signed_tree_erasure_bst :
    Search.OrderedMap.DecodedKeys.BST id (eraseColors signedTree) :=
  (bst_iff_eraseColors id signedTree).mp signed_tree_bst

/-- The grandchild key crosses the root's bound despite ordered adjacent roots. -/
def hiddenRight : Tree Int Nat :=
  .node black (.node red .nil (-2, 7) (.node red .nil (1, 8) .nil)) (0, 0) .nil

theorem child_root_order_is_insufficient :
    (-2 : Int) < 0 ∧ (-2 : Int) < 1 ∧ ¬ BST id hiddenRight := by
  simp [hiddenRight, bst_node_iff, ForallT, RBTree.RBNode.All]

/-- Source transitivity lemmas constrain every payload-bearing node. -/
theorem signed_tree_weakened_bounds :
    ForallT (fun key _ => (-4 : Int) < key) signedTree ∧
      ForallT (fun key _ => key < (5 : Int)) signedTree := by
  have lower : ForallT (fun key _ => (-3 : Int) < key) signedTree := by
    simp [signedTree]
  have upper : ForallT (fun key _ => key < (4 : Int)) signedTree := by
    simp [signedTree]
  exact ⟨forallT_greater id signedTree (-3) (-4) lower (by decide),
    forallT_less id signedTree 4 5 upper (by decide)⟩

/-- Adjacent red nodes are irrelevant to the strict key-order predicate. -/
def redChain : Tree Int Nat :=
  .node red (.node red .nil (-2, 7) .nil) (0, 0) .nil

theorem red_chain_bst : BST id redChain := by
  simp [redChain, bst_node_iff, ForallT, RBTree.RBNode.All]

theorem recolored_red_chain_bst : BST id (makeBlack redChain) :=
  makeBlack_bst id red_chain_bst

theorem red_chain_not_rb (parent : RBTree.RBColor) (n : Nat) :
    ¬ RB redChain parent n := by
  intro valid
  have child := (rb_red_node_iff.mp valid).2.1
  have impossible := (rb_red_node_iff.mp child).1
  cases impossible

/-- BST balancing applies even though the input child violates red adjacency. -/
theorem balanced_red_chain_bst : BST id (balance black redChain 3 9 .nil) := by
  apply balance_bst id black redChain 3 9 .nil red_chain_bst (bst_nil id)
  · simp [redChain, ForallT, RBTree.RBNode.All]
  · exact forallT_nil _

open Search.RedBlack Representations.SignedComparison

/-- A stored zero and an absent key have different optional observations. -/
def storedDefault : Tree Int Nat := insert intLtb 0 0 empty

theorem stored_default_presence :
    lookup? intLtb 0 (empty : Tree Int Nat) = none ∧
      lookup? intLtb 0 storedDefault = some 0 ∧
      bound intLtb 0 storedDefault = true ∧
      lookup intLtb 0 0 (empty : Tree Int Nat) = lookup intLtb 0 0 storedDefault := by
  decide

theorem stored_default_witness :
    ∃ value : Nat, ∀ default : Nat, lookup intLtb default 0 storedDefault = value :=
  bound_value intLtb 0 storedDefault stored_default_presence.2.2.1

theorem absent_uses_caller_default (default : Nat) :
    lookup intLtb default 0 (empty : Tree Int Nat) = default :=
  bound_default intLtb default 0 empty (bound_nil intLtb 0)

theorem balance_red_chain_observations :
    lookup intLtb 99 (-2) (balance black redChain 3 9 .nil) = 7 ∧
      lookup intLtb 99 0 (balance black redChain 3 9 .nil) = 0 ∧
      lookup intLtb 99 3 (balance black redChain 3 9 .nil) = 9 ∧
      lookup intLtb 99 2 (balance black redChain 3 9 .nil) = 99 := by
  have lower : ForallT (fun child _ => child < (3 : Int)) redChain := by
    simp [redChain, ForallT, RBTree.RBNode.All]
  have equation (query : Int) := balance_lookup id intLtb intLtb_true_iff
    99 query black redChain 3 9 .nil red_chain_bst (bst_nil id) lower (forallT_nil _)
  simp only [equation]
  simp [redChain, lookup_node, lookup_nil, intLtb]

open Search.RedBlack RBTree.RBColor Representations.SignedComparison
universe v

def collidingTree : Tree Bool Nat := .node black .nil (false, 1) .nil

theorem colliding_tree_bst : BST (fun _ : Bool => (0 : Int)) collidingTree := by
  simp [collidingTree, bst_node_iff, ForallT, RBTree.RBNode.All]

theorem colliding_same_key :
    lookup (fun _ _ : Bool => false) 99 true
      (insert (fun _ _ : Bool => false) true 2 collidingTree) = 2 :=
  lookup_insert_eq (fun _ : Bool => (0 : Int)) (fun _ _ : Bool => false)
    Search.OrderedMap.DecodedKeys.colliding_decode_reflects 99 colliding_tree_bst true 2

theorem colliding_original_key_boundary :
    ¬ Function.Injective (fun _ : Bool => (0 : Int)) ∧
      lookup (fun _ _ : Bool => false) 99 false collidingTree = 1 ∧
      lookup (fun _ _ : Bool => false) 99 false
        (insert (fun _ _ : Bool => false) true 2 collidingTree) = 2 ∧
      elements (insert (fun _ _ : Bool => false) true 2 collidingTree) = [(true, 2)] := by
  constructor
  · intro injective
    have impossible : false = true := injective rfl
    cases impossible
  · decide

theorem type_payload_same_key (default value : Type v) (key : Int)
    {t : Tree Int (Type v)} (valid : BST id t) :
    lookup intLtb default key (insert intLtb key value t) = value :=
  lookup_insert_eq id intLtb intLtb_true_iff default valid key value

theorem distinct_original_binding_preserved :
    lookup intLtb 99 (-2) (insert intLtb 3 9 redChain) = 7 := by
  have preserved := lookup_insert_neq id intLtb int_decode_injective intLtb_true_iff
    99 red_chain_bst 3 (-2) 9 (by decide)
  simpa [redChain, lookup_node, lookup_nil, intLtb] using preserved

open Search.RedBlack Representations.SignedComparison

def overwriteTree : Tree Int Nat :=
  insert intLtb 3 333 (insert intLtb (-2) 202 (insert intLtb 3 303 empty))

theorem overwrite_tree_bst : BST id overwriteTree := by
  apply insert_bst id intLtb intLtb_true_iff
  apply insert_bst id intLtb intLtb_true_iff
  apply insert_bst id intLtb intLtb_true_iff
  exact bst_nil id

theorem overwrite_elements : elements overwriteTree = [(-2, 202), (3, 333)] := by
  have initial : BST id (empty : Tree Int Nat) := bst_nil id
  have first := insert_bst id intLtb intLtb_true_iff initial 3 303
  have second := insert_bst id intLtb intLtb_true_iff first (-2) 202
  unfold overwriteTree
  rw [elements_insert id intLtb int_decode_injective intLtb_true_iff second,
    elements_insert id intLtb int_decode_injective intLtb_true_iff first,
    elements_insert id intLtb int_decode_injective intLtb_true_iff initial]
  decide

theorem overwrite_enumeration_contract :
    bound intLtb (-2) overwriteTree = true ∧
      (∀ default : Nat, lookup intLtb default (-2) overwriteTree = 202) ∧
      ((elements overwriteTree).map Prod.fst).Pairwise (fun a b : Int => a < b) ∧
      ((elements overwriteTree).map Prod.fst).Nodup := by
  have member : ((-2 : Int), 202) ∈ elements overwriteTree := by
    rw [overwrite_elements]
    simp
  have sound := elements_sound id intLtb intLtb_true_iff overwrite_tree_bst member
  exact ⟨sound.1, sound.2, keys_pairwise id overwrite_tree_bst,
    keys_nodup id overwrite_tree_bst⟩

theorem overwrite_absent : bound intLtb 7 overwriteTree = false := by
  apply no_entry_absent id intLtb int_decode_injective intLtb_true_iff
  intro value
  rw [overwrite_elements]
  simp

theorem malformed_enumeration_boundary :
    ((1 : Int), 8) ∈ elements hiddenRight ∧ bound intLtb 1 hiddenRight = false := by
  decide

theorem raw_relation_membership :
    ∀ binding ∈ elements hiddenRight, binding.1 ≤ (1 : Int) := by
  apply relation_elements (· ≤ ·) 1
  simp [hiddenRight, ForallT, RBTree.RBNode.All]

theorem overwrite_models_agree :
    enumAbs id intLtb int_decode_injective intLtb_true_iff overwriteTree =
        mapOfTree id intLtb int_decode_injective intLtb_true_iff overwriteTree ∧
      listAbs id intLtb int_decode_injective intLtb_true_iff (elements overwriteTree) =
        mapOfTree id intLtb int_decode_injective intLtb_true_iff overwriteTree :=
  ⟨enumAbs_eq_mapOfTree id intLtb int_decode_injective intLtb_true_iff overwrite_tree_bst,
    elements_relate_structural id intLtb int_decode_injective intLtb_true_iff overwrite_tree_bst⟩

theorem overwrite_partial_values :
    enumAbs id intLtb int_decode_injective intLtb_true_iff overwriteTree (-2) = some 202 ∧
      enumAbs id intLtb int_decode_injective intLtb_true_iff overwriteTree 3 = some 333 ∧
      enumAbs id intLtb int_decode_injective intLtb_true_iff overwriteTree 0 = none := by
  simp only [enumAbs_lookup id intLtb int_decode_injective intLtb_true_iff overwrite_tree_bst]
  decide

theorem structural_stored_default :
    mapOfTree id intLtb int_decode_injective intLtb_true_iff
      (insert intLtb 0 0 overwriteTree) 0 = some 0 := by
  have updated := mapOfTree_insert id intLtb int_decode_injective intLtb_true_iff
    overwrite_tree_bst 0 0
  simpa [Search.OrderedMap.write] using congrFun updated 0

def canonicalPeer : Tree Int Nat := insert intLtb 3 333 (insert intLtb (-2) 202 empty)

theorem canonical_peer_bst : BST id canonicalPeer := by
  apply insert_bst id intLtb intLtb_true_iff
  apply insert_bst id intLtb intLtb_true_iff
  exact bst_nil id

/-- Equality of the full meanings follows from source updates, not an assumed list equality. -/
theorem canonical_peer_meaning :
    enumAbs id intLtb int_decode_injective intLtb_true_iff overwriteTree =
      enumAbs id intLtb int_decode_injective intLtb_true_iff canonicalPeer := by
  have initial : BST id (empty : Tree Int Nat) := bst_nil id
  have first := insert_bst id intLtb intLtb_true_iff initial 3 303
  have second := insert_bst id intLtb intLtb_true_iff first (-2) 202
  have otherFirst := insert_bst id intLtb intLtb_true_iff initial (-2) 202
  unfold overwriteTree canonicalPeer
  rw [enumAbs_insert id intLtb int_decode_injective intLtb_true_iff second,
    enumAbs_insert id intLtb int_decode_injective intLtb_true_iff first,
    enumAbs_insert id intLtb int_decode_injective intLtb_true_iff initial,
    enumAbs_insert id intLtb int_decode_injective intLtb_true_iff otherFirst,
    enumAbs_insert id intLtb int_decode_injective intLtb_true_iff initial]
  funext query
  by_cases high : query = 3
  · simp [Search.OrderedMap.write, high]
  · by_cases low : query = -2 <;> simp [Search.OrderedMap.write, high, low]

theorem canonical_peer_elements : elements overwriteTree = elements canonicalPeer :=
  elements_eq_of_enumAbs_eq id intLtb int_decode_injective intLtb_true_iff
    overwrite_tree_bst canonical_peer_bst canonical_peer_meaning

/-- Propositional shape inequality observes root keys, never the provider's inorder BEq. -/
theorem canonical_peer_different_shape : overwriteTree ≠ canonicalPeer := by
  intro same
  have roots := congrArg (fun t : Tree Int Nat =>
    match t with | .nil => 0 | .node _ _ binding _ => binding.1) same
  change (3 : Int) = -2 at roots
  exact (by decide : (3 : Int) ≠ -2) roots

theorem one_default_not_canonical :
    (∀ query : Int, lookup intLtb 0 query (empty : Tree Int Nat) =
      lookup intLtb 0 query storedDefault) ∧
      elements (empty : Tree Int Nat) ≠ elements storedDefault := by
  constructor
  · intro query
    simp [storedDefault, lookup_node]
  · decide
open Search.RedBlack Representations.SignedComparison

/-- The supplied signed-word comparator orders negative, zero and positive endpoints. -/
def fourBitTree : Tree (BitVec 4) Nat :=
  insert wordLtb (BitVec.ofInt 4 7) 3
    (insert wordLtb (BitVec.ofInt 4 0) 2 (insert wordLtb (BitVec.ofInt 4 (-8)) 1 empty))

theorem four_bit_tree_bst : BST BitVec.toInt fourBitTree := by
  apply insert_bst BitVec.toInt wordLtb wordLtb_true_iff
  apply insert_bst BitVec.toInt wordLtb wordLtb_true_iff
  apply insert_bst BitVec.toInt wordLtb wordLtb_true_iff
  exact bst_nil BitVec.toInt

theorem four_bit_signed_values :
    (elements fourBitTree).map (fun binding => (binding.1.toInt, binding.2)) =
      [(-8, 1), (0, 2), (7, 3)] := by
  have initial : BST BitVec.toInt (empty : Tree (BitVec 4) Nat) := bst_nil BitVec.toInt
  have first := insert_bst BitVec.toInt wordLtb wordLtb_true_iff
    initial (BitVec.ofInt 4 (-8)) 1
  have second := insert_bst BitVec.toInt wordLtb wordLtb_true_iff
    first (BitVec.ofInt 4 0) 2
  unfold fourBitTree
  rw [elements_insert BitVec.toInt wordLtb (word_decode_injective 4) wordLtb_true_iff second,
    elements_insert BitVec.toInt wordLtb (word_decode_injective 4) wordLtb_true_iff first,
    elements_insert BitVec.toInt wordLtb (word_decode_injective 4) wordLtb_true_iff initial]
  decide

theorem four_bit_written_lookup : lookup wordLtb 99 (BitVec.ofInt 4 7) fourBitTree = 3 := by
  apply lookup_insert_eq BitVec.toInt wordLtb wordLtb_true_iff
  apply insert_bst BitVec.toInt wordLtb wordLtb_true_iff
  apply insert_bst BitVec.toInt wordLtb wordLtb_true_iff
  exact bst_nil BitVec.toInt


open Search.RedBlack Representations.SignedComparison

/-- The accepted Int64 comparator is used on both signed endpoints and zero. -/
def int64Tree : Tree Int64 Nat :=
  insert int64Ltb (Int64.ofInt ((2 : Int) ^ 63 - 1)) 3
    (insert int64Ltb (Int64.ofInt 0) 2
      (insert int64Ltb (Int64.ofInt (-((2 : Int) ^ 63))) 1 empty))

theorem int64_tree_bst : BST Int64.toInt int64Tree := by
  apply insert_bst Int64.toInt int64Ltb int64Ltb_true_iff
  apply insert_bst Int64.toInt int64Ltb int64Ltb_true_iff
  apply insert_bst Int64.toInt int64Ltb int64Ltb_true_iff
  exact bst_nil Int64.toInt

theorem int64_signed_values :
    (elements int64Tree).map (fun binding => (binding.1.toInt, binding.2)) =
      [(-((2 : Int) ^ 63), 1), (0, 2), ((2 : Int) ^ 63 - 1, 3)] := by
  have initial : BST Int64.toInt (empty : Tree Int64 Nat) := bst_nil Int64.toInt
  have first := insert_bst Int64.toInt int64Ltb int64Ltb_true_iff
    initial (Int64.ofInt (-((2 : Int) ^ 63))) 1
  have second := insert_bst Int64.toInt int64Ltb int64Ltb_true_iff
    first (Int64.ofInt 0) 2
  unfold int64Tree
  rw [elements_insert Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff second,
    elements_insert Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff first,
    elements_insert Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff initial]
  decide

theorem int64_written_lookup :
    lookup int64Ltb 99 (Int64.ofInt ((2 : Int) ^ 63 - 1)) int64Tree = 3 := by
  apply lookup_insert_eq Int64.toInt int64Ltb int64Ltb_true_iff
  apply insert_bst Int64.toInt int64Ltb int64Ltb_true_iff
  apply insert_bst Int64.toInt int64Ltb int64Ltb_true_iff
  exact bst_nil Int64.toInt

end Examples.RedBlackMaps
