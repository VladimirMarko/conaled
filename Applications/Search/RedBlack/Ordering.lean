import Applications.Search.RedBlack.Observations
import Applications.Search.OrderedTree.Observations
import Applications.Search.OrderedMap.DecodedKeysModels

/-!
# Decoded ordering for the source colored trees

Ordering is the accepted strict all-descendant invariant on color erasure.
Payloads have no order, and the decoder need not be injective. The source
Boolean operations retain their own computation; decoding is a proof parameter.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RedBlack

universe u v
variable {κ : Type u} {ν : Type v}

/-- Color-independent strict bounds on every descendant, through the accepted tree. -/
def BST (decode : κ → Int) (t : Tree κ ν) : Prop :=
  OrderedMap.DecodedKeys.BST decode (eraseColors t)

theorem bst_iff_eraseColors (decode : κ → Int) (t : Tree κ ν) :
    BST decode t ↔ OrderedMap.DecodedKeys.BST decode (eraseColors t) := Iff.rfl

@[simp] theorem bst_nil (decode : κ → Int) : BST decode (.nil : Tree κ ν) := trivial

/-- Both strict separators range over complete subtrees, independently of color. -/
theorem bst_node_iff (decode : κ → Int) (color : RBTree.RBColor)
    (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν) :
    BST decode (.node color left (key, value) right) ↔
      BST decode left ∧ BST decode right ∧
        ForallT (fun child _ => decode child < decode key) left ∧
        ForallT (fun child _ => decode key < decode child) right := by
  change
    (BST decode left ∧ BST decode right ∧
      OrderedMap.DecodedKeys.ForallT (fun child _ => decode child < decode key)
        (eraseColors left) ∧
      OrderedMap.DecodedKeys.ForallT (fun child _ => decode key < decode child)
        (eraseColors right)) ↔ _
  rw [eraseColors_forallT, eraseColors_forallT]

/-- Root recoloring preserves the decoded invariant without a shape premise. -/
theorem makeBlack_bst (decode : κ → Int) {t : Tree κ ν} (valid : BST decode t) :
    BST decode (makeBlack t) := by
  cases t <;> exact valid

/-- Strict decoded inorder is equivalent to the full structural invariant. -/
theorem bst_iff_elements_pairwise (decode : κ → Int) (t : Tree κ ν) :
    BST decode t ↔
      (elements t).Pairwise (fun a b => decode a.1 < decode b.1) := by
  change OrderedTree.OrderedBy (fun binding : κ × ν => decode binding.1)
    (eraseColors t) ↔ _
  rw [OrderedTree.orderedBy_iff_inorder_pairwise]
  change (OrderedTree.entries (eraseColors t)).Pairwise
    (fun a b => decode a.1 < decode b.1) ↔ _
  rw [← OrderedMap.DecodedKeys.elements_eq, eraseColors_elements]

/-- Exact inorder preservation transports the four source subtree premises. -/
theorem balance_bst (decode : κ → Int) (color : RBTree.RBColor)
    (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν)
    (hl : BST decode left) (hr : BST decode right)
    (lower : ForallT (fun child _ => decode child < decode key) left)
    (upper : ForallT (fun child _ => decode key < decode child) right) :
    BST decode (balance color left key value right) := by
  apply (bst_iff_elements_pairwise decode _).mpr
  rw [balance_elements]
  have ordered := (bst_iff_elements_pairwise decode
    (.node color left (key, value) right)).mp
      ((bst_node_iff decode color left key value right).mpr ⟨hl, hr, lower, upper⟩)
  simpa only [elements_node] using ordered

/-- Lower bounds weaken by transitivity at every stored node. -/
theorem forallT_greater (decode : κ → Int) (t : Tree κ ν) (key lower : κ)
    (all : ForallT (fun child _ => decode key < decode child) t)
    (bound : decode lower < decode key) :
    ForallT (fun child _ => decode lower < decode child) t :=
  RBTree.RBNode.All.imp
    (fun {binding} h => show decode lower < decode binding.1 from lt_trans bound h) all

/-- Upper bounds weaken by transitivity at every stored node. -/
theorem forallT_less (decode : κ → Int) (t : Tree κ ν) (key upper : κ)
    (all : ForallT (fun child _ => decode child < decode key) t)
    (bound : decode key < decode upper) :
    ForallT (fun child _ => decode child < decode upper) t :=
  RBTree.RBNode.All.imp
    (fun {binding} h => show decode binding.1 < decode upper from lt_trans h bound) all

section StrictReflection
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hlt

/-- Equal inorder contents determine lookup under decoded ordering, even when
different original keys have the same decoder value. -/
theorem lookup?_eq_of_elements_eq {left right : Tree κ ν}
    (hl : BST decode left) (hr : BST decode right)
    (same : elements left = elements right) (query : κ) :
    lookup? ltb query left = lookup? ltb query right := by
  have decodedSame :
      OrderedTree.entries (OrderedMap.DecodedKeys.mapKeys decode (eraseColors left)) =
        OrderedTree.entries (OrderedMap.DecodedKeys.mapKeys decode (eraseColors right)) := by
    rw [OrderedMap.DecodedKeys.entries_mapKeys, OrderedMap.DecodedKeys.entries_mapKeys,
      ← OrderedMap.DecodedKeys.elements_eq, ← OrderedMap.DecodedKeys.elements_eq,
      eraseColors_elements, eraseColors_elements, same]
  calc
    lookup? ltb query left = OrderedMap.DecodedKeys.lookup? ltb query (eraseColors left) :=
      (eraseColors_lookup? ltb query left).symm
    _ = OrderedMap.lookup (decode query)
        (OrderedMap.DecodedKeys.mapKeys decode (eraseColors left)) :=
      (OrderedMap.DecodedKeys.lookup?_decode decode ltb hlt query _).symm
    _ = OrderedMap.SourceModel.enumAbs
        (OrderedMap.DecodedKeys.mapKeys decode (eraseColors left)) (decode query) :=
      (OrderedMap.SourceModel.enumAbs_eq_lookup
        ((OrderedMap.DecodedKeys.bst_iff_mapKeys decode _).mp hl) _).symm
    _ = OrderedMap.SourceModel.enumAbs
        (OrderedMap.DecodedKeys.mapKeys decode (eraseColors right)) (decode query) := by
      simp only [OrderedMap.SourceModel.enumAbs, decodedSame]
    _ = OrderedMap.lookup (decode query)
        (OrderedMap.DecodedKeys.mapKeys decode (eraseColors right)) :=
      OrderedMap.SourceModel.enumAbs_eq_lookup
        ((OrderedMap.DecodedKeys.bst_iff_mapKeys decode _).mp hr) _
    _ = OrderedMap.DecodedKeys.lookup? ltb query (eraseColors right) :=
      OrderedMap.DecodedKeys.lookup?_decode decode ltb hlt query _
    _ = lookup? ltb query right := eraseColors_lookup? ltb query right

/-- The source Boolean branch equation after balancing, with no shape or
decoder-injectivity premise. -/
theorem lookup?_balance (query : κ) (color : RBTree.RBColor)
    (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν)
    (hl : BST decode left) (hr : BST decode right)
    (lower : ForallT (fun child _ => decode child < decode key) left)
    (upper : ForallT (fun child _ => decode key < decode child) right) :
    lookup? ltb query (balance color left key value right) =
      if ltb query key then lookup? ltb query left
      else if ltb key query then lookup? ltb query right else some value := by
  have same := lookup?_eq_of_elements_eq decode ltb hlt
    (balance_bst decode color left key value right hl hr lower upper)
    ((bst_node_iff decode color left key value right).mpr ⟨hl, hr, lower, upper⟩)
    (by rw [balance_elements, elements_node]) query
  exact same.trans (lookup?_node ltb query color left key value right)

/-- The textbook's displayed decoded-Int equation for arbitrary caller defaults. -/
theorem balance_lookup (default : ν) (query : κ) (color : RBTree.RBColor)
    (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν)
    (hl : BST decode left) (hr : BST decode right)
    (lower : ForallT (fun child _ => decode child < decode key) left)
    (upper : ForallT (fun child _ => decode key < decode child) right) :
    lookup ltb default query (balance color left key value right) =
      if decode query < decode key then lookup ltb default query left
      else if decode key < decode query then lookup ltb default query right else value := by
  unfold lookup
  rw [lookup?_balance decode ltb hlt query color left key value right hl hr lower upper]
  simp only [hlt]
  split
  · rfl
  · split <;> rfl

/-- Both recursive source branches preserve full subtree bounds. Replacement
needs equality of decoded keys, not equality of the original keys. -/
theorem ins_bst {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    BST decode (ins ltb key value t) := by
  revert valid
  induction t with
  | nil =>
      intro _
      exact (bst_node_iff decode .red .nil key value .nil).mpr
        ⟨bst_nil decode, bst_nil decode, forallT_nil _, forallT_nil _⟩
  | node color left binding right ihl ihr =>
      cases binding with
      | mk old previous =>
          intro valid
          obtain ⟨hl, hr, lower, upper⟩ :=
            (bst_node_iff decode color left old previous right).mp valid
          rw [ins_node]
          split
          · rename_i before
            exact balance_bst decode color (ins ltb key value left) old previous right
              (ihl hl) hr
              (ins_forallT ltb (fun child _ => decode child < decode old)
                key value left ((hlt key old).mp before) lower) upper
          · rename_i notBefore
            split
            · rename_i after
              exact balance_bst decode color left old previous (ins ltb key value right)
                hl (ihr hr) lower
                (ins_forallT ltb (fun child _ => decode old < decode child)
                  key value right ((hlt old key).mp after) upper)
            · rename_i notAfter
              have same : decode key = decode old :=
                le_antisymm (le_of_not_gt (mt (hlt old key).mpr notAfter))
                  (le_of_not_gt (mt (hlt key old).mpr notBefore))
              exact (bst_node_iff decode color left key value right).mpr
                ⟨hl, hr, by simpa only [same] using lower,
                  by simpa only [same] using upper⟩

theorem insert_bst {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    BST decode (insert ltb key value t) :=
  makeBlack_bst decode (ins_bst decode ltb hlt valid key value)

/-- Source insertion and ordinary insertion have equal search observations on
valid input. This is a semantic equation, not a structural erasure equation. -/
theorem lookup?_ins_eq_unbalanced {t : Tree κ ν} (valid : BST decode t)
    (key : κ) (value : ν) (query : κ) :
    lookup? ltb query (ins ltb key value t) =
      OrderedMap.DecodedKeys.lookup? ltb query
        (OrderedMap.DecodedKeys.insert ltb key value (eraseColors t)) := by
  revert valid
  induction t with
  | nil =>
      intro _
      simp only [ins_nil, eraseColors_nil, OrderedMap.DecodedKeys.insert_empty,
        lookup?_node, OrderedMap.DecodedKeys.lookup?_node,
        lookup?_nil, OrderedMap.DecodedKeys.lookup?_empty]
  | node color left binding right ihl ihr =>
      cases binding with
      | mk old previous =>
          intro valid
          obtain ⟨hl, hr, lower, upper⟩ :=
            (bst_node_iff decode color left old previous right).mp valid
          by_cases before : ltb key old = true
          · rw [ins_node, ite_eq_left before, eraseColors_node,
              OrderedMap.DecodedKeys.insert_node, ite_eq_left before,
              lookup?_balance decode ltb hlt query color _ old previous right
                (ins_bst decode ltb hlt hl key value) hr
                (ins_forallT ltb (fun child _ => decode child < decode old)
                  key value left ((hlt key old).mp before) lower) upper]
            simp only [OrderedMap.DecodedKeys.lookup?_node, ihl hl, eraseColors_lookup?]
          · by_cases after : ltb old key = true
            · rw [ins_node, ite_eq_right before, ite_eq_left after, eraseColors_node,
                OrderedMap.DecodedKeys.insert_node, ite_eq_right before, ite_eq_left after,
                lookup?_balance decode ltb hlt query color left old previous _
                  hl (ins_bst decode ltb hlt hr key value) lower
                  (ins_forallT ltb (fun child _ => decode old < decode child)
                    key value right ((hlt old key).mp after) upper)]
              simp only [OrderedMap.DecodedKeys.lookup?_node, ihr hr, eraseColors_lookup?]
            · rw [ins_node, ite_eq_right before, ite_eq_right after, eraseColors_node,
                OrderedMap.DecodedKeys.insert_node, ite_eq_right before, ite_eq_right after]
              simp only [lookup?_node, OrderedMap.DecodedKeys.lookup?_node,
                eraseColors_lookup?]

theorem lookup?_ins_eq {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    lookup? ltb key (ins ltb key value t) = some value := by
  rw [lookup?_ins_eq_unbalanced decode ltb hlt valid key value key,
    OrderedMap.DecodedKeys.lookup?_insert_eq decode ltb hlt]

theorem lookup_ins_eq (default : ν) {t : Tree κ ν} (valid : BST decode t)
    (key : κ) (value : ν) : lookup ltb default key (ins ltb key value t) = value :=
  congrArg (fun result => result.getD default)
    (lookup?_ins_eq decode ltb hlt valid key value)

theorem lookup?_insert_eq {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    lookup? ltb key (insert ltb key value t) = some value := by
  rw [insert_eq_makeBlack_ins, lookup?_makeBlack, lookup?_ins_eq decode ltb hlt valid]

theorem lookup_insert_eq (default : ν) {t : Tree κ ν} (valid : BST decode t)
    (key : κ) (value : ν) : lookup ltb default key (insert ltb key value t) = value :=
  congrArg (fun result => result.getD default)
    (lookup?_insert_eq decode ltb hlt valid key value)

end StrictReflection

section InjectiveReflection
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hinj : Function.Injective decode)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hinj hlt

/-- Original-key distinctness needs injective decoding; BST remains the only
tree invariant used by this semantic preservation theorem. -/
theorem lookup?_ins_neq {t : Tree κ ν} (valid : BST decode t)
    (key query : κ) (value : ν) (different : key ≠ query) :
    lookup? ltb query (ins ltb key value t) = lookup? ltb query t := by
  rw [lookup?_ins_eq_unbalanced decode ltb hlt valid key value query,
    OrderedMap.DecodedKeys.lookup?_insert_neq decode ltb hinj hlt
      key query value (eraseColors t) different,
    eraseColors_lookup?]

theorem lookup_ins_neq (default : ν) {t : Tree κ ν} (valid : BST decode t)
    (key query : κ) (value : ν) (different : key ≠ query) :
    lookup ltb default query (ins ltb key value t) = lookup ltb default query t :=
  congrArg (fun result => result.getD default)
    (lookup?_ins_neq decode ltb hinj hlt valid key query value different)

theorem lookup?_insert_neq {t : Tree κ ν} (valid : BST decode t)
    (key query : κ) (value : ν) (different : key ≠ query) :
    lookup? ltb query (insert ltb key value t) = lookup? ltb query t := by
  rw [insert_eq_makeBlack_ins, lookup?_makeBlack,
    lookup?_ins_neq decode ltb hinj hlt valid key query value different]

theorem lookup_insert_neq (default : ν) {t : Tree κ ν} (valid : BST decode t)
    (key query : κ) (value : ν) (different : key ≠ query) :
    lookup ltb default query (insert ltb key value t) = lookup ltb default query t :=
  congrArg (fun result => result.getD default)
    (lookup?_insert_neq decode ltb hinj hlt valid key query value different)

end InjectiveReflection

end Search.RedBlack
