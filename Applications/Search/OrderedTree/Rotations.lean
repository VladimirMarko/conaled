import Applications.Search.OrderedTree.Observations
import Applications.Trees.Rotations.Bounds

/-!
# Ordered clients of raw tree rotations

The existing inorder characterizations transport order through the primitive
and sequential operations. Keys alone have a preorder; payloads may live in a
different universe and need neither an order nor decidable equality.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
open Trees.Rotations
open Search.SharedTree (Branch)
universe u v
variable {α : Type u} {κ : Type v}

theorem ordered_of_inorder_eq [Preorder α] {s t : BinaryTree α}
    (same : Trees.inorder t = Trees.inorder s) (ordered : Ordered s) : Ordered t := by
  rw [ordered_iff_inorder_pairwise, same]
  exact (ordered_iff_inorder_pairwise s).mp ordered

theorem orderedBy_of_inorder_eq [Preorder κ] (key : α → κ) {s t : BinaryTree α}
    (same : Trees.inorder t = Trees.inorder s) (ordered : OrderedBy key s) :
    OrderedBy key t := by
  rw [orderedBy_iff_inorder_pairwise, same]
  exact (orderedBy_iff_inorder_pairwise key s).mp ordered

theorem ordered_rotateRight? [Preorder α] {s t : BinaryTree α}
    (run : rotateRight? s = some t) (ordered : Ordered s) : Ordered t :=
  ordered_of_inorder_eq (rotateRight?_inorder run) ordered

theorem ordered_rotateLeft? [Preorder α] {s t : BinaryTree α}
    (run : rotateLeft? s = some t) (ordered : Ordered s) : Ordered t :=
  ordered_of_inorder_eq (rotateLeft?_inorder run) ordered

theorem orderedBy_rotateRight? [Preorder κ] (key : α → κ) {s t : BinaryTree α}
    (run : rotateRight? s = some t) (ordered : OrderedBy key s) : OrderedBy key t :=
  orderedBy_of_inorder_eq key (rotateRight?_inorder run) ordered

theorem orderedBy_rotateLeft? [Preorder κ] (key : α → κ) {s t : BinaryTree α}
    (run : rotateLeft? s = some t) (ordered : OrderedBy key s) : OrderedBy key t :=
  orderedBy_of_inorder_eq key (rotateLeft?_inorder run) ordered

theorem ordered_applyAt? [Preorder α] (f : BinaryTree α → Option (BinaryTree α))
    (preserves : ∀ {s t}, f s = some t → Trees.inorder t = Trees.inorder s)
    (p : List Branch) {s t : BinaryTree α}
    (run : applyAt? f p s = some t) (ordered : Ordered s) : Ordered t :=
  ordered_of_inorder_eq (applyAt?_inorder f preserves p run) ordered

theorem ordered_applyAts? [Preorder α] (f : BinaryTree α → Option (BinaryTree α))
    (preserves : ∀ {s t}, f s = some t → Trees.inorder t = Trees.inorder s)
    (ps : List (List Branch)) {s t : BinaryTree α}
    (run : applyAts? f ps s = some t) (ordered : Ordered s) : Ordered t :=
  ordered_of_inorder_eq (applyAts?_inorder f preserves ps run) ordered

theorem orderedBy_applyAt? [Preorder κ] (key : α → κ)
    (f : BinaryTree α → Option (BinaryTree α))
    (preserves : ∀ {s t}, f s = some t → Trees.inorder t = Trees.inorder s)
    (p : List Branch) {s t : BinaryTree α}
    (run : applyAt? f p s = some t) (ordered : OrderedBy key s) : OrderedBy key t :=
  orderedBy_of_inorder_eq key (applyAt?_inorder f preserves p run) ordered

theorem orderedBy_applyAts? [Preorder κ] (key : α → κ)
    (f : BinaryTree α → Option (BinaryTree α))
    (preserves : ∀ {s t}, f s = some t → Trees.inorder t = Trees.inorder s)
    (ps : List (List Branch)) {s t : BinaryTree α}
    (run : applyAts? f ps s = some t) (ordered : OrderedBy key s) : OrderedBy key t :=
  orderedBy_of_inorder_eq key (applyAts?_inorder f preserves ps run) ordered

theorem ordered_listOf [Preorder α] {t : BinaryTree α} (ordered : Ordered t) :
    Ordered (listOf t) := ordered_of_inorder_eq (listOf_inorder t) ordered

theorem orderedBy_listOf [Preorder κ] (key : α → κ) {t : BinaryTree α}
    (ordered : OrderedBy key t) : OrderedBy key (listOf t) :=
  orderedBy_of_inorder_eq key (listOf_inorder t) ordered

end Search.OrderedTree
