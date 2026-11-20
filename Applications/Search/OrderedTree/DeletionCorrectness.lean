import Applications.Search.OrderedTree.Deletion
import Applications.Search.OrderedTree.Observations

/-!
# Structural correctness of extraction, joins and both deletions

This proof route uses recursive `Contains`, `All`, and `OrderedBy`. Helper
contents laws are their structural set laws. In particular it does not use
the later list update/refinement proofs. Keyed deletion preserves complete
surviving labels, with no order on payloads or global injectivity of keys.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u v
variable {α : Type u} {κ : Type v}

def Cross [LT κ] (key : α → κ) (l r : BinaryTree α) : Prop :=
  ∀ x, Contains x l → ∀ y, Contains y r → key x < key y

theorem contains_joinLeftmost (l r : BinaryTree α) (z : α) :
    Contains z (Trees.joinLeftmost l r) ↔ Contains z l ∨ Contains z r := by
  simpa only [contains_iff_mem_setTree] using Trees.mem_setTree_joinLeftmost l r z

theorem contains_join (l r : BinaryTree α) (z : α) :
    Contains z (Trees.join l r) ↔ Contains z l ∨ Contains z r := by
  simpa only [contains_iff_mem_setTree] using Trees.mem_setTree_join l r z

theorem contains_join0 (l r : BinaryTree α) (z : α) :
    Contains z (Trees.join0 l r) ↔ Contains z l ∨ Contains z r := by
  simpa only [contains_iff_mem_setTree] using Trees.mem_setTree_join0 l r z

theorem all_join (P : α → Prop) (l r : BinaryTree α) :
    All P (Trees.join l r) ↔ All P l ∧ All P r := by
  simpa only [all_iff_mem_setTree] using Trees.forall_mem_join P l r

theorem all_join0 (P : α → Prop) (l r : BinaryTree α) :
    All P (Trees.join0 l r) ↔ All P l ∧ All P r := by
  simpa only [all_iff_mem_setTree] using Trees.forall_mem_join0 P l r

theorem extractLeftmost_contains {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (found : Trees.extractLeftmost t = some (x, s)) (z : α) :
    Contains z t ↔ z = x ∨ Contains z s := by
  simpa only [contains_iff_mem_setTree] using Trees.extractLeftmost_mem found z

theorem extractLeftmost_all {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (found : Trees.extractLeftmost t = some (x, s)) (P : α → Prop) :
    All P t ↔ P x ∧ All P s := by
  simpa only [all_iff_mem_setTree] using Trees.extractLeftmost_forall found P

section OrderedHelpers
variable [Preorder κ] {key : α → κ}

/-- Strictness of the residual contains the leastness information needed by
successor replacement; no linear-order or decidability premise is used. -/
theorem extractLeftmost_ordered {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (ordered : OrderedBy key t) (found : Trees.extractLeftmost t = some (x, s)) :
    OrderedBy key s ∧ All (fun z => key x < key z) s := by
  induction t generalizing x s with
  | nil => cases found
  | node a l r ihl _ =>
      cases l with
      | nil =>
          simp only [Trees.extractLeftmost, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact ⟨ordered.2.1, ordered.2.2.2⟩
      | node b ll lr =>
          obtain ⟨y, s', hy⟩ := Trees.extractLeftmost_exists
            (t := .node b ll lr) (by intro h; cases h)
          simp only [Trees.extractLeftmost, hy, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          have residual := ihl ordered.1 hy
          have upper := (extractLeftmost_all hy (fun z => key z < key a)).mp
            ordered.2.2.1
          exact ⟨⟨residual.1, ordered.2.1, upper.2, ordered.2.2.2⟩,
            upper.1, residual.2,
            ordered.2.2.2.mono (fun _ h => lt_trans upper.1 h)⟩

theorem extractLeftmost_least {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (ordered : OrderedBy key t) (found : Trees.extractLeftmost t = some (x, s)) :
    Contains x t ∧ ∀ z, Contains z t → key x ≤ key z := by
  refine ⟨(extractLeftmost_contains found x).mpr (Or.inl rfl), ?_⟩
  intro z hz
  rcases (extractLeftmost_contains found z).mp hz with rfl | hz
  · exact le_refl _
  · exact le_of_lt ((extractLeftmost_ordered ordered found).2.of_contains hz)

theorem extractLeftmost_removal {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (ordered : OrderedBy key t) (found : Trees.extractLeftmost t = some (x, s)) (z : α) :
    Contains z s ↔ Contains z t ∧ key z ≠ key x := by
  constructor
  · intro hz
    exact ⟨(extractLeftmost_contains found z).mpr (Or.inr hz),
      ne_of_gt ((extractLeftmost_ordered ordered found).2.of_contains hz)⟩
  · rintro ⟨hz, hne⟩
    rcases (extractLeftmost_contains found z).mp hz with rfl | hz
    · exact False.elim (hne rfl)
    · exact hz

theorem orderedBy_joinLeftmost {l r : BinaryTree α}
    (hl : OrderedBy key l) (hr : OrderedBy key r) (cross : Cross key l r) :
    OrderedBy key (Trees.joinLeftmost l r) := by
  cases r with
  | nil => exact hl
  | node a rl rr =>
      obtain ⟨x, s, found⟩ := Trees.extractLeftmost_exists
        (t := .node a rl rr) (by intro h; cases h)
      have hx := (extractLeftmost_contains found x).mpr (Or.inl rfl)
      have residual := extractLeftmost_ordered hr found
      rw [Trees.joinLeftmost_of_extract found]
      exact ⟨hl, residual.1, (all_iff _ _).mpr (fun z hz => cross z hz x hx), residual.2⟩

theorem orderedBy_join {l r : BinaryTree α}
    (hl : OrderedBy key l) (hr : OrderedBy key r) (cross : Cross key l r) :
    OrderedBy key (Trees.join l r) := by
  induction l generalizing r with
  | nil => exact hr
  | node a l m _ ihm =>
      cases r with
      | nil => simpa only [Trees.join_nil_right] using hl
      | node b n r =>
          have hab : key a < key b := cross a (Or.inl rfl) b (Or.inl rfl)
          have hmiddle := ihm hl.2.1 hr.1
            (fun z hz w hw => cross z (Or.inr (Or.inr hz)) w (Or.inr (Or.inl hw)))
          have middleBounds : All (fun z => key a < key z ∧ key z < key b)
              (Trees.join m n) := by
            apply (all_join _ m n).mpr
            constructor
            · exact (all_iff _ _).mpr fun z hz => ⟨hl.2.2.2.of_contains hz,
                cross z (Or.inr (Or.inr hz)) b (Or.inl rfl)⟩
            · exact (all_iff _ _).mpr fun z hz =>
                ⟨cross a (Or.inl rfl) z (Or.inr (Or.inl hz)), hr.2.2.1.of_contains hz⟩
          cases h : Trees.join m n with
          | nil =>
              rw [Trees.join_node_node, h]
              exact ⟨hl.1, ⟨trivial, hr.2.1, trivial, hr.2.2.2⟩, hl.2.2.1,
                hab, trivial, hr.2.2.2.mono (fun _ hbr => lt_trans hab hbr)⟩
          | node x p q =>
              rw [h] at hmiddle middleBounds
              rw [Trees.join_node_node, h]
              exact ⟨⟨hl.1, hmiddle.1, hl.2.2.1,
                  middleBounds.2.1.mono (fun _ hz => hz.1)⟩,
                ⟨hmiddle.2.1, hr.2.1, middleBounds.2.2.mono (fun _ hz => hz.2),
                  hr.2.2.2⟩,
                ⟨middleBounds.1.1,
                  hl.2.2.1.mono (fun _ hz => lt_trans hz middleBounds.1.1),
                  hmiddle.2.2.1⟩,
                middleBounds.1.2, hmiddle.2.2.2,
                hr.2.2.2.mono (fun _ hz => lt_trans middleBounds.1.2 hz)⟩

theorem orderedBy_join0 {l r : BinaryTree α}
    (hl : OrderedBy key l) (hr : OrderedBy key r) (cross : Cross key l r) :
    OrderedBy key (Trees.join0 l r) := by
  induction l generalizing r with
  | nil => exact hr
  | node a l m _ ihm =>
      cases r with
      | nil => simpa only [Trees.join0_nil_right] using hl
      | node b n r =>
          have hab : key a < key b := cross a (Or.inl rfl) b (Or.inl rfl)
          have hmiddle := ihm hl.2.1 hr.1
            (fun z hz w hw => cross z (Or.inr (Or.inr hz)) w (Or.inr (Or.inl hw)))
          have middleBounds : All (fun z => key a < key z ∧ key z < key b)
              (Trees.join0 m n) := by
            apply (all_join0 _ m n).mpr
            constructor
            · exact (all_iff _ _).mpr fun z hz => ⟨hl.2.2.2.of_contains hz,
                cross z (Or.inr (Or.inr hz)) b (Or.inl rfl)⟩
            · exact (all_iff _ _).mpr fun z hz =>
                ⟨cross a (Or.inl rfl) z (Or.inr (Or.inl hz)), hr.2.2.1.of_contains hz⟩
          rw [Trees.join0_node_node]
          exact ⟨hl.1,
            ⟨hmiddle, hr.2.1, middleBounds.mono (fun _ hz => hz.2), hr.2.2.2⟩,
            hl.2.2.1, hab, middleBounds.mono (fun _ hz => hz.1),
            hr.2.2.2.mono (fun _ hz => lt_trans hab hz)⟩

end OrderedHelpers

section RawDeletion
variable [LT κ] [DecidableLT κ]

theorem contains_deleteWith_subset
    (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (contents : ∀ l r z, Contains z (combine l r) ↔ Contains z l ∨ Contains z r)
    (key : α → κ) (q : κ) (t : BinaryTree α) (z : α) :
    Contains z (deleteWith combine key q t) → Contains z t := by
  induction t with
  | nil => exact id
  | node a l r ihl ihr =>
      simp only [deleteWith]
      split
      · simp only [Contains]
        tauto
      · split
        · simp only [Contains]
          tauto
        · rw [contents]
          intro h
          exact Or.inr h

theorem all_deleteWith
    (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (contents : ∀ l r z, Contains z (combine l r) ↔ Contains z l ∨ Contains z r)
    (key : α → κ) (q : κ) {t : BinaryTree α} {P : α → Prop} (h : All P t) :
    All P (deleteWith combine key q t) :=
  (all_iff _ _).mpr fun z hz =>
    h.of_contains (contains_deleteWith_subset combine contents key q t z hz)

end RawDeletion

section OrderedDeletion
variable [LinearOrder κ]

theorem orderedBy_deleteWith
    (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (contents : ∀ l r z, Contains z (combine l r) ↔ Contains z l ∨ Contains z r)
    (key : α → κ)
    (preserves : ∀ l r, OrderedBy key l → OrderedBy key r → Cross key l r →
      OrderedBy key (combine l r))
    (q : κ) {t : BinaryTree α} (ordered : OrderedBy key t) :
    OrderedBy key (deleteWith combine key q t) := by
  induction t with
  | nil => trivial
  | node a l r ihl ihr =>
      simp only [deleteWith]
      split
      · exact ⟨ihl ordered.1, ordered.2.1,
          all_deleteWith combine contents key q ordered.2.2.1, ordered.2.2.2⟩
      · split
        · exact ⟨ordered.1, ihr ordered.2.1, ordered.2.2.1,
            all_deleteWith combine contents key q ordered.2.2.2⟩
        · exact preserves l r ordered.1 ordered.2.1
            (fun z hz w hw => lt_trans (ordered.2.2.1.of_contains hz)
              (ordered.2.2.2.of_contains hw))

/-- Full-label semantics, not merely a key-set statement. -/
theorem contains_deleteWith
    (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (contents : ∀ l r z, Contains z (combine l r) ↔ Contains z l ∨ Contains z r)
    (key : α → κ) (q : κ) {t : BinaryTree α} (ordered : OrderedBy key t) (z : α) :
    Contains z (deleteWith combine key q t) ↔ Contains z t ∧ key z ≠ q := by
  induction t with
  | nil => simp [deleteWith, Contains]
  | node a l r ihl ihr =>
      by_cases hlt : q < key a
      · have hroot : z = a → key z ≠ q := by
          rintro rfl
          exact ne_of_gt hlt
        have hright : Contains z r → key z ≠ q :=
          fun hz => ne_of_gt (lt_trans hlt (ordered.2.2.2.of_contains hz))
        simp only [deleteWith, ite_eq_left hlt, Contains, ihl ordered.1]
        constructor
        · rintro (h | ⟨h, hne⟩ | h)
          · exact ⟨Or.inl h, hroot h⟩
          · exact ⟨Or.inr (Or.inl h), hne⟩
          · exact ⟨Or.inr (Or.inr h), hright h⟩
        · rintro ⟨(h | h | h), hne⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨h, hne⟩)
          · exact Or.inr (Or.inr h)
      · by_cases hgt : key a < q
        · have hroot : z = a → key z ≠ q := by
            rintro rfl
            exact ne_of_lt hgt
          have hleft : Contains z l → key z ≠ q :=
            fun hz => ne_of_lt (lt_trans (ordered.2.2.1.of_contains hz) hgt)
          simp only [deleteWith, ite_eq_right hlt, ite_eq_left hgt, Contains, ihr ordered.2.1]
          constructor
          · rintro (h | h | ⟨h, hne⟩)
            · exact ⟨Or.inl h, hroot h⟩
            · exact ⟨Or.inr (Or.inl h), hleft h⟩
            · exact ⟨Or.inr (Or.inr h), hne⟩
          · rintro ⟨(h | h | h), hne⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨h, hne⟩)
        · have heq : q = key a := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
          have hroot : z = a → ¬ key z ≠ q := by
            rintro rfl
            exact not_not.mpr heq.symm
          have hleft : Contains z l → key z ≠ q := by
            intro hz
            rw [heq]
            exact ne_of_lt (ordered.2.2.1.of_contains hz)
          have hright : Contains z r → key z ≠ q := by
            intro hz
            rw [heq]
            exact ne_of_gt (ordered.2.2.2.of_contains hz)
          simp only [deleteWith, ite_eq_right hlt, ite_eq_right hgt, contents, Contains]
          constructor
          · rintro (h | h)
            · exact ⟨Or.inr (Or.inl h), hleft h⟩
            · exact ⟨Or.inr (Or.inr h), hright h⟩
          · rintro ⟨(h | h | h), hne⟩
            · exact False.elim (hroot h hne)
            · exact Or.inl h
            · exact Or.inr h

theorem orderedBy_deleteBy (key : α → κ) (q : κ) {t : BinaryTree α}
    (ordered : OrderedBy key t) : OrderedBy key (deleteBy key q t) :=
  orderedBy_deleteWith Trees.joinLeftmost contains_joinLeftmost key
    (fun _ _ => orderedBy_joinLeftmost) q ordered

theorem orderedBy_deleteJoinBy (key : α → κ) (q : κ) {t : BinaryTree α}
    (ordered : OrderedBy key t) : OrderedBy key (deleteJoinBy key q t) :=
  orderedBy_deleteWith Trees.join contains_join key (fun _ _ => orderedBy_join) q ordered

theorem contains_deleteBy (key : α → κ) (q : κ) {t : BinaryTree α}
    (ordered : OrderedBy key t) (z : α) :
    Contains z (deleteBy key q t) ↔ Contains z t ∧ key z ≠ q :=
  contains_deleteWith Trees.joinLeftmost contains_joinLeftmost key q ordered z

theorem contains_deleteJoinBy (key : α → κ) (q : κ) {t : BinaryTree α}
    (ordered : OrderedBy key t) (z : α) :
    Contains z (deleteJoinBy key q t) ↔ Contains z t ∧ key z ≠ q :=
  contains_deleteWith Trees.join contains_join key q ordered z

end OrderedDeletion

section Sets
variable [LinearOrder α]

theorem ordered_delete {t : BinaryTree α} (ordered : Ordered t) (x : α) :
    Ordered (delete x t) := orderedBy_deleteBy id x ordered

theorem ordered_deleteJoin {t : BinaryTree α} (ordered : Ordered t) (x : α) :
    Ordered (deleteJoin x t) := orderedBy_deleteJoinBy id x ordered

theorem contains_delete {t : BinaryTree α} (ordered : Ordered t) (x z : α) :
    Contains z (delete x t) ↔ z ≠ x ∧ Contains z t :=
  (contains_deleteBy id x ordered z).trans and_comm

theorem contains_deleteJoin {t : BinaryTree α} (ordered : Ordered t) (x z : α) :
    Contains z (deleteJoin x t) ↔ z ≠ x ∧ Contains z t :=
  (contains_deleteJoinBy id x ordered z).trans and_comm

end Sets
end Search.OrderedTree
