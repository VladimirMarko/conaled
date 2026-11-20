import Applications.Search.RedBlack.Basic
import Applications.Search.OrderedMap.DecodedKeys
import Batteries.Recycling.RBTree.Lemmas
import Batteries.Recycling.RBTree.Depth

/-!
# Observations of raw colored search trees

The ordinary-tree bridges erase colors only. They do not require sorted keys,
red-black shape, reflection laws, or an injective key representation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RedBlack

universe u v
variable {κ : Type u} {ν : Type v}

/-- The accumulator's suffix is retained after every original binding. -/
theorem elementsAux_eq (t : Tree κ ν) (suffix : List (κ × ν)) :
    elementsAux t suffix = elements t ++ suffix :=
  RBTree.RBNode.foldr_cons t suffix

theorem elements_node (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    elements (.node color left (key, value) right) =
      elements left ++ (key, value) :: elements right :=
  RBTree.RBNode.toList_node

/-- Every priority branch retains the exact in-order binding sequence. -/
theorem balance_elements (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    elements (balance color left key value right) =
      elements left ++ (key, value) :: elements right := by
  unfold balance
  split
  · exact RBTree.RBNode.toList_node
  · split
    · simp [elements, List.append_assoc]
    · simp [elements, List.append_assoc]
    · split <;> simp [elements, List.append_assoc]

theorem forallT_elements_iff (P : κ → ν → Prop) (t : Tree κ ν) :
    ForallT P t ↔ ∀ binding ∈ elements t, P binding.1 binding.2 := by
  simp only [ForallT, RBTree.RBNode.All_def, elements, RBTree.RBNode.mem_toList]

/-- Predicate weakening reuses the provider's all-node implication theorem. -/
theorem forallT_imp {P Q : κ → ν → Prop} {t : Tree κ ν}
    (implication : ∀ key value, P key value → Q key value) (all : ForallT P t) :
    ForallT Q t :=
  RBTree.RBNode.All.imp (fun h => implication _ _ h) all

/-- Balancing preserves and reflects every all-binding predicate. -/
theorem balance_forallT (P : κ → ν → Prop) (color : RBTree.RBColor)
    (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν) :
    ForallT P (balance color left key value right) ↔
      P key value ∧ ForallT P left ∧ ForallT P right := by
  simp only [forallT_elements_iff, balance_elements, List.forall_mem_append,
    List.forall_mem_cons, and_left_comm]

theorem makeBlack_forallT (P : κ → ν → Prop) (t : Tree κ ν) :
    ForallT P (makeBlack t) ↔ ForallT P t := by
  cases t <;> rfl

/-- Any raw insertion preserves a predicate satisfied by all old and new bindings. -/
theorem ins_forallT (ltb : κ → κ → Bool) (P : κ → ν → Prop)
    (key : κ) (value : ν) (t : Tree κ ν) (written : P key value) (all : ForallT P t) :
    ForallT P (ins ltb key value t) := by
  revert all
  induction t with
  | nil =>
      intro _
      exact ⟨written, trivial, trivial⟩
  | node color left binding right ihl ihr =>
      cases binding with
      | mk old previous =>
          intro all
          obtain ⟨hprevious, hl, hr⟩ := (forallT_node P color left old previous right).mp all
          rw [ins_node]
          split
          · exact (balance_forallT P color _ old previous right).mpr
              ⟨hprevious, ihl hl, hr⟩
          · split
            · exact (balance_forallT P color left old previous _).mpr
                ⟨hprevious, hl, ihr hr⟩
            · exact ⟨written, hl, hr⟩

theorem insert_forallT (ltb : κ → κ → Bool) (P : κ → ν → Prop)
    (key : κ) (value : ν) (t : Tree κ ν) (written : P key value) (all : ForallT P t) :
    ForallT P (insert ltb key value t) :=
  (makeBlack_forallT P _).mpr (ins_forallT ltb P key value t written all)

/-- Root recoloring cannot affect a directed search. -/
theorem lookup?_makeBlack (ltb : κ → κ → Bool) (query : κ) (t : Tree κ ν) :
    lookup? ltb query (makeBlack t) = lookup? ltb query t := by
  cases t <;> rfl

theorem lookup_makeBlack (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (t : Tree κ ν) : lookup ltb default query (makeBlack t) = lookup ltb default query t := by
  unfold lookup
  rw [lookup?_makeBlack]

/-- The provider's root recoloring retains the entire in-order list. -/
theorem makeBlack_elements (t : Tree κ ν) : elements (makeBlack t) = elements t :=
  RBTree.RBNode.setBlack_toList

theorem makeBlack_elementsAux (t : Tree κ ν) (suffix : List (κ × ν)) :
    elementsAux (makeBlack t) suffix = elementsAux t suffix := by
  rw [elementsAux_eq, elementsAux_eq, makeBlack_elements]

theorem eraseColors_makeBlack (t : Tree κ ν) : eraseColors (makeBlack t) = eraseColors t := by
  cases t <;> rfl

/-- Color erasure preserves the source predicate on every stored binding. -/
theorem eraseColors_forallT (P : κ → ν → Prop) (t : Tree κ ν) :
    Search.OrderedMap.DecodedKeys.ForallT P (eraseColors t) ↔ ForallT P t := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      cases binding with
      | mk key value =>
          simp only [eraseColors_node, Search.OrderedMap.DecodedKeys.ForallT,
            Search.OrderedTree.All, forallT_node] at *
          rw [ihl, ihr]

/-- Erasing colors leaves every supplied Boolean search branch unchanged. -/
theorem eraseColors_lookup? (ltb : κ → κ → Bool) (query : κ) (t : Tree κ ν) :
    Search.OrderedMap.DecodedKeys.lookup? ltb query (eraseColors t) =
      lookup? ltb query t := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      cases binding with
      | mk key value =>
          simp only [eraseColors_node, Search.OrderedMap.DecodedKeys.lookup?_node,
            lookup?_node, ihl, ihr]

theorem eraseColors_lookup (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (t : Tree κ ν) :
    Search.OrderedMap.DecodedKeys.lookup ltb default query (eraseColors t) =
      lookup ltb default query t := by
  unfold Search.OrderedMap.DecodedKeys.lookup lookup
  rw [eraseColors_lookup?]

/-- The raw accumulator bridge preserves both original pairs and an arbitrary suffix. -/
theorem eraseColors_elementsAux (t : Tree κ ν) (suffix : List (κ × ν)) :
    Search.OrderedMap.DecodedKeys.elementsAux (eraseColors t) suffix =
      elementsAux t suffix := by
  induction t generalizing suffix with
  | nil => rfl
  | node color left binding right ihl ihr =>
      cases binding with
      | mk key value =>
          rw [eraseColors_node, Search.OrderedMap.DecodedKeys.elementsAux_node,
            elementsAux_node, ihr, ihl]

theorem eraseColors_elements (t : Tree κ ν) :
    Search.OrderedMap.DecodedKeys.elements (eraseColors t) = elements t :=
  eraseColors_elementsAux t []

/-- Ordinary height agrees with the provider's raw maximum node depth. -/
theorem eraseColors_height (t : Tree κ ν) :
    BinaryTree.height (eraseColors t) = RBTree.RBNode.depth t := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      cases binding with
      | mk key value =>
          simp only [eraseColors_node, BinaryTree.height, RBTree.RBNode.depth, ihl, ihr]

/-- Color erasure preserves the number of internal nodes, excluding empty leaves. -/
theorem eraseColors_numNodes (t : Tree κ ν) :
    BinaryTree.numNodes (eraseColors t) = RBTree.RBNode.size t := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      cases binding with
      | mk key value =>
          simp only [eraseColors_node, BinaryTree.numNodes, RBTree.RBNode.size, ihl, ihr]

end Search.RedBlack
