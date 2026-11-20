import Applications.Search.OrderedTree.Observations

/-!
# Strict pivot splitting and structural tree union

Splitting excludes equality from both results. Union recurses on the first
tree and splits the second at that root; its actual shape is retained. No
balance, allocation, or asymptotic guarantee is inferred from these laws.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u
variable {α : Type u} [LinearOrder α]

def split (x : α) : BinaryTree α → BinaryTree α × BinaryTree α
  | .nil => (.nil, .nil)
  | .node a l r =>
      if x < a then
        let p := split x l
        (p.1, .node a p.2 r)
      else if a < x then
        let p := split x r
        (.node a l p.1, p.2)
      else (l, r)

theorem split_subset (x : α) (t : BinaryTree α) :
    (∀ z, Contains z (split x t).1 → Contains z t) ∧
    (∀ z, Contains z (split x t).2 → Contains z t) := by
  induction t with
  | nil => exact ⟨fun _ => id, fun _ => id⟩
  | node a l r ihl ihr =>
      by_cases hlt : x < a
      · simp only [split, ite_eq_left hlt]
        constructor
        · exact fun z hz => Or.inr (Or.inl (ihl.1 z hz))
        · intro z hz
          rcases hz with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (ihl.2 z h))
          · exact Or.inr (Or.inr h)
      · by_cases hgt : a < x
        · simp only [split, ite_eq_right hlt, ite_eq_left hgt]
          constructor
          · intro z hz
            rcases hz with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (ihr.1 z h))
          · exact fun z hz => Or.inr (Or.inr (ihr.2 z hz))
        · simp only [split, ite_eq_right hlt, ite_eq_right hgt]
          exact ⟨fun _ hz => Or.inr (Or.inl hz), fun _ hz => Or.inr (Or.inr hz)⟩

theorem all_split (x : α) {t : BinaryTree α} {P : α → Prop} (h : All P t) :
    All P (split x t).1 ∧ All P (split x t).2 :=
  ⟨(all_iff _ _).mpr (fun z hz => h.of_contains ((split_subset x t).1 z hz)),
    (all_iff _ _).mpr (fun z hz => h.of_contains ((split_subset x t).2 z hz))⟩

theorem ordered_split (x : α) {t : BinaryTree α} (ordered : Ordered t) :
    Ordered (split x t).1 ∧ Ordered (split x t).2 := by
  induction t with
  | nil => exact ⟨trivial, trivial⟩
  | node a l r ihl ihr =>
      by_cases hlt : x < a
      · simp only [split, ite_eq_left hlt]
        exact ⟨(ihl ordered.1).1,
          (ihl ordered.1).2, ordered.2.1, (all_split x ordered.2.2.1).2, ordered.2.2.2⟩
      · by_cases hgt : a < x
        · simp only [split, ite_eq_right hlt, ite_eq_left hgt]
          exact ⟨⟨ordered.1, (ihr ordered.2.1).1, ordered.2.2.1,
            (all_split x ordered.2.2.2).1⟩, (ihr ordered.2.1).2⟩
        · rw [split, ite_eq_right hlt, ite_eq_right hgt]
          exact ⟨ordered.1, ordered.2.1⟩

theorem contains_split (x z : α) {t : BinaryTree α} (ordered : Ordered t) :
    (Contains z (split x t).1 ↔ Contains z t ∧ z < x) ∧
    (Contains z (split x t).2 ↔ Contains z t ∧ x < z) := by
  induction t with
  | nil => simp [split, Contains]
  | node a l r ihl ihr =>
      by_cases hlt : x < a
      · have ih := ihl ordered.1
        simp only [split, ite_eq_left hlt, Contains, ih.1, ih.2]
        constructor
        · constructor
          · rintro ⟨hz, hzx⟩
            exact ⟨Or.inr (Or.inl hz), hzx⟩
          · rintro ⟨(rfl | hz | hz), hzx⟩
            · exact False.elim (lt_asymm hlt hzx)
            · exact ⟨hz, hzx⟩
            · exact False.elim (lt_asymm (lt_trans hlt (ordered.2.2.2.of_contains hz)) hzx)
        · constructor
          · rintro (rfl | ⟨hz, hxz⟩ | hz)
            · exact ⟨Or.inl rfl, hlt⟩
            · exact ⟨Or.inr (Or.inl hz), hxz⟩
            · exact ⟨Or.inr (Or.inr hz), lt_trans hlt (ordered.2.2.2.of_contains hz)⟩
          · rintro ⟨(hz | hz | hz), hxz⟩
            · exact Or.inl hz
            · exact Or.inr (Or.inl ⟨hz, hxz⟩)
            · exact Or.inr (Or.inr hz)
      · by_cases hgt : a < x
        · have ih := ihr ordered.2.1
          simp only [split, ite_eq_right hlt, ite_eq_left hgt, Contains, ih.1, ih.2]
          constructor
          · constructor
            · rintro (rfl | hz | ⟨hz, hzx⟩)
              · exact ⟨Or.inl rfl, hgt⟩
              · exact ⟨Or.inr (Or.inl hz), lt_trans (ordered.2.2.1.of_contains hz) hgt⟩
              · exact ⟨Or.inr (Or.inr hz), hzx⟩
            · rintro ⟨(hz | hz | hz), hzx⟩
              · exact Or.inl hz
              · exact Or.inr (Or.inl hz)
              · exact Or.inr (Or.inr ⟨hz, hzx⟩)
          · constructor
            · rintro ⟨hz, hxz⟩
              exact ⟨Or.inr (Or.inr hz), hxz⟩
            · rintro ⟨(rfl | hz | hz), hxz⟩
              · exact False.elim (lt_asymm hgt hxz)
              · exact False.elim (lt_asymm (lt_trans (ordered.2.2.1.of_contains hz) hgt) hxz)
              · exact ⟨hz, hxz⟩
        · have heq : x = a := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
          subst x
          simp only [split, lt_self_iff_false, ite_false, Contains]
          constructor
          · constructor
            · intro hz
              exact ⟨Or.inr (Or.inl hz), ordered.2.2.1.of_contains hz⟩
            · rintro ⟨(rfl | hz | hz), hza⟩
              · exact False.elim (lt_irrefl _ hza)
              · exact hz
              · exact False.elim (lt_asymm hza (ordered.2.2.2.of_contains hz))
          · constructor
            · intro hz
              exact ⟨Or.inr (Or.inr hz), ordered.2.2.2.of_contains hz⟩
            · rintro ⟨(rfl | hz | hz), haz⟩
              · exact False.elim (lt_irrefl _ haz)
              · exact False.elim (lt_asymm haz (ordered.2.2.1.of_contains hz))
              · exact hz

theorem split_bounds (x : α) {t : BinaryTree α} (ordered : Ordered t) :
    All (· < x) (split x t).1 ∧ All (x < ·) (split x t).2 :=
  ⟨(all_iff _ _).mpr (fun z hz => ((contains_split x z ordered).1.mp hz).2),
    (all_iff _ _).mpr (fun z hz => ((contains_split x z ordered).2.mp hz).2)⟩

theorem setTree_split (x : α) {t : BinaryTree α} (ordered : Ordered t) :
    Trees.setTree (split x t).1 = {z | z ∈ Trees.setTree t ∧ z < x} ∧
    Trees.setTree (split x t).2 = {z | z ∈ Trees.setTree t ∧ x < z} := by
  constructor
  · ext z
    simpa only [← contains_iff_mem_setTree, Set.mem_ofPred_eq] using
      (contains_split x z ordered).1
  · ext z
    simpa only [← contains_iff_mem_setTree, Set.mem_ofPred_eq] using
      (contains_split x z ordered).2

def union : BinaryTree α → BinaryTree α → BinaryTree α
  | .nil, s => s
  | .node a l r, s =>
      let p := split a s
      .node a (union l p.1) (union r p.2)

@[simp] theorem union_nil (s : BinaryTree α) : union .nil s = s := rfl

theorem union_node (a : α) (l r s : BinaryTree α) :
    union (.node a l r) s = .node a (union l (split a s).1) (union r (split a s).2) := rfl

theorem contains_union (l r : BinaryTree α) (hr : Ordered r) (z : α) :
    Contains z (union l r) ↔ Contains z l ∨ Contains z r := by
  induction l generalizing r with
  | nil => simp [union, Contains]
  | node a l m ihl ihm =>
      have hs := ordered_split a hr
      simp only [union, Contains, ihl _ hs.1, ihm _ hs.2,
        (contains_split a z hr).1, (contains_split a z hr).2]
      constructor
      · rintro (h | (h | ⟨h, _⟩) | (h | ⟨h, _⟩))
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr h
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr h
      · rintro ((h | h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
        · rcases lt_trichotomy z a with hlt | heq | hgt
          · exact Or.inr (Or.inl (Or.inr ⟨h, hlt⟩))
          · exact Or.inl heq
          · exact Or.inr (Or.inr (Or.inr ⟨h, hgt⟩))

theorem all_union {P : α → Prop} {l r : BinaryTree α} (hr : Ordered r)
    (hlp : All P l) (hrp : All P r) : All P (union l r) := by
  apply (all_iff _ _).mpr
  intro z hz
  rcases (contains_union l r hr z).mp hz with h | h
  · exact hlp.of_contains h
  · exact hrp.of_contains h

theorem ordered_union {l r : BinaryTree α} (hl : Ordered l) (hr : Ordered r) :
    Ordered (union l r) := by
  induction l generalizing r with
  | nil => exact hr
  | node a l m ihl ihm =>
      have hs := ordered_split a hr
      have bounds := split_bounds a hr
      exact ⟨ihl hl.1 hs.1, ihm hl.2.1 hs.2,
        all_union hs.1 hl.2.2.1 bounds.1, all_union hs.2 hl.2.2.2 bounds.2⟩

theorem setTree_union (l r : BinaryTree α) (hr : Ordered r) :
    Trees.setTree (union l r) = Trees.setTree l ∪ Trees.setTree r := by
  ext z
  simpa only [contains_iff_mem_setTree, Set.mem_union] using contains_union l r hr z

end Search.OrderedTree
