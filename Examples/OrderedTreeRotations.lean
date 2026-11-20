import Applications.Search.OrderedTree.Rotations
import Examples.TreeRotations

/-! Ordered, enumerated and larger-universe clients of the same raw operations. -/
set_option autoImplicit false
set_option warningAsError true

namespace OrderedTreeRotationsExample
open Trees Trees.Rotations Search.OrderedTree TreeRotationsExample

theorem balanced_ordered : Ordered balancedThree := by
  simp [Ordered, OrderedBy, All, balancedThree, leaf]

theorem left_chain_ordered : Ordered leftThree := by
  simp [Ordered, OrderedBy, All, leftThree, leaf]

theorem rotated_ordered : Ordered rightThree :=
  ordered_rotateRight? balanced_rotates balanced_ordered

theorem inverse_ordered : Ordered balancedThree :=
  ordered_rotateLeft? balanced_recovers rotated_ordered

theorem positioned_ordered : Ordered balancedThree :=
  ordered_applyAt? rotateRight? rotateRight?_inorder [] left_chain_first_step left_chain_ordered

theorem sequential_ordered : Ordered rightThree :=
  ordered_applyAts? rotateRight? rotateRight?_inorder
    [[.left], [], [.right]] longer_legal_trace left_chain_ordered

theorem normalized_ordered : Ordered (listOf balancedSeven) :=
  ordered_listOf (by simp [Ordered, OrderedBy, All, balancedSeven, balancedThree,
    balancedRight, leaf])

theorem malformed_is_not_ordered : ¬ Ordered malformed := by
  simp [Ordered, OrderedBy, All, malformed, leaf]

theorem repeated_key_is_not_strictly_ordered : ¬ Ordered duplicateLeft := by
  simp [Ordered, OrderedBy, All, duplicateLeft, leaf]

theorem balanced_enumerated : balancedThree ∈ enumTree [1, 2, 3] :=
  (mem_enumTree_iff _ _).mpr rfl

theorem left_chain_enumerated : leftThree ∈ enumTree [1, 2, 3] :=
  (mem_enumTree_iff _ _).mpr rfl

theorem rotated_enumerated : rightThree ∈ enumTree [1, 2, 3] :=
  mem_enumTree_of_right_trace [1, 2, 3] [[]] balanced_enumerated rfl

theorem enumerated_connection :
    (applyAts? rotateRight? (rightPositions balancedThree) balancedThree).bind
      (applyAts? rotateLeft? (rightPositions leftThree).reverse) = some leftThree :=
  connect_enumTree [1, 2, 3] balanced_enumerated left_chain_enumerated

theorem repeated_labels_enumerated : duplicateLeft ∈ enumTree [7, 7] ∧
    duplicateRight ∈ enumTree [7, 7] :=
  ⟨(mem_enumTree_iff _ _).mpr rfl, (mem_enumTree_iff _ _).mpr rfl⟩

/-- This is Type 1; the key is Nat and the retained payload is a function. -/
abbrev Payload := Nat × ULift.{1} (Nat → Nat)

def entry (key offset : Nat) : Payload := (key, ⟨fun n => n + offset⟩)

def keyedBalanced : BinaryTree Payload := .node (entry 2 20)
  (.node (entry 1 10) .nil .nil) (.node (entry 3 30) .nil .nil)

def keyedRight : BinaryTree Payload := .node (entry 1 10) .nil
  (.node (entry 2 20) .nil (.node (entry 3 30) .nil .nil))

theorem keyed_rotation : rotateRight? keyedBalanced = some keyedRight := rfl

theorem keyed_inverse : rotateLeft? keyedRight = some keyedBalanced := rfl

theorem keyed_ordered : OrderedBy Prod.fst keyedBalanced := by
  simp [OrderedBy, All, keyedBalanced, entry]

theorem keyed_rotated_ordered : OrderedBy Prod.fst keyedRight :=
  orderedBy_rotateRight? Prod.fst keyed_rotation keyed_ordered

theorem keyed_inverse_ordered : OrderedBy Prod.fst keyedBalanced :=
  orderedBy_rotateLeft? Prod.fst keyed_inverse keyed_rotated_ordered

theorem keyed_positioned_ordered : OrderedBy Prod.fst keyedRight :=
  orderedBy_applyAt? Prod.fst rotateRight? rotateRight?_inorder [] keyed_rotation keyed_ordered

theorem keyed_sequential_ordered : OrderedBy Prod.fst keyedRight :=
  orderedBy_applyAts? Prod.fst rotateRight? rotateRight?_inorder [[]] rfl keyed_ordered

theorem keyed_normalized_ordered : OrderedBy Prod.fst (listOf keyedBalanced) :=
  orderedBy_listOf Prod.fst keyed_ordered

theorem keyed_source_algorithms :
    listOf keyedBalanced = keyedRight ∧ rightPositions keyedBalanced = [[]] ∧
      countRots keyedBalanced = 1 := by
  simp [keyedBalanced, keyedRight]

theorem complete_payload_sequence_retained :
    inorder keyedRight = inorder keyedBalanced ∧
      inorder keyedRight = [entry 1 10, entry 2 20, entry 3 30] := ⟨rfl, rfl⟩

theorem payload_functions_retained :
    (inorder keyedRight).map (fun v => v.2.down 4) = [14, 24, 34] := rfl

theorem key_projection_is_not_injective : ¬ Function.Injective (Prod.fst : Payload → Nat) := by
  intro injective
  have same : entry 1 10 = entry 1 20 := injective rfl
  have impossible := congrArg (fun v : Payload => v.2.down 4) same
  change (14 : Nat) = 24 at impossible
  omega

#eval ((inorder (listOf keyedBalanced)).map Prod.fst,
  (inorder (listOf keyedBalanced)).map (fun v => v.2.down 4),
  countRots keyedBalanced, rightPositions keyedBalanced |>.length)

#eval ([0, 1, 2, 3, 4].map (fun x => Search.SharedTree.searchPathBy id x balancedThree)
  |>.map (List.map (fun d => match d with | .left => 0 | .right => 1)))

end OrderedTreeRotationsExample
