import Applications.Trees.BasicObservations
import Applications.Trees.Enumeration

/-!
# Leftmost extraction with an explicit empty domain

The paired operation executes the source's single left-spine traversal. It
returns no arbitrary label at nil. Its remainder recovers the existing
`removeFirst` operation and its successful pairs characterize the existing
`insertFirst` clients. Contents and height proofs are structural; leastness
belongs to the separate ordered-tree owner.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

def extractLeftmost : BinaryTree α → Option (α × BinaryTree α)
  | .nil => none
  | .node a .nil r => some (a, r)
  | .node a (.node b ll lr) r =>
      (extractLeftmost (.node b ll lr)).map fun p => (p.1, .node a p.2 r)

@[simp] theorem extractLeftmost_nil :
    extractLeftmost (.nil : BinaryTree α) = none := rfl

@[simp] theorem extractLeftmost_node_nil (a : α) (r : BinaryTree α) :
    extractLeftmost (.node a .nil r) = some (a, r) := rfl

theorem extractLeftmost_node_of_ne_nil (a : α) (l r : BinaryTree α) (hl : l ≠ .nil) :
    extractLeftmost (.node a l r) =
      (extractLeftmost l).map (fun p => (p.1, .node a p.2 r)) := by
  cases l <;> simp_all [extractLeftmost]

@[simp] theorem extractLeftmost_eq_none_iff (t : BinaryTree α) :
    extractLeftmost t = none ↔ t = .nil := by
  induction t with
  | nil => simp
  | node a l r ihl _ =>
      cases l <;> simp_all [extractLeftmost]

theorem extractLeftmost_exists {t : BinaryTree α} (hne : t ≠ .nil) :
    ∃ x s, extractLeftmost t = some (x, s) := by
  cases h : extractLeftmost t with
  | none => exact False.elim (hne ((extractLeftmost_eq_none_iff t).mp h))
  | some p => exact ⟨p.1, p.2, rfl⟩

/-- A source call with a proved nonempty input returns a pair without a default. -/
def extractLeftmostNonempty (t : BinaryTree α) (hne : t ≠ .nil) : α × BinaryTree α :=
  (extractLeftmost t).get (by
    apply Option.isSome_iff_exists.mpr
    obtain ⟨x, s, h⟩ := extractLeftmost_exists hne
    exact ⟨(x, s), h⟩)

theorem extractLeftmostNonempty_spec (t : BinaryTree α) (hne : t ≠ .nil) :
    extractLeftmost t = some (extractLeftmostNonempty t hne) := by
  simp only [extractLeftmostNonempty, Option.some_get]

theorem extractLeftmostNonempty_eq {t : BinaryTree α} (hne : t ≠ .nil)
    {x : α} {s : BinaryTree α} (found : extractLeftmost t = some (x, s)) :
    extractLeftmostNonempty t hne = (x, s) :=
  Option.some.inj ((extractLeftmostNonempty_spec t hne).symm.trans found)

theorem extractLeftmost_inorder {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (found : extractLeftmost t = some (x, s)) : x :: inorder s = inorder t := by
  induction t generalizing x s with
  | nil => cases found
  | node a l r ihl _ =>
      cases l with
      | nil =>
          simp only [extractLeftmost, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          rfl
      | node b ll lr =>
          obtain ⟨y, s', hy⟩ := extractLeftmost_exists
            (t := .node b ll lr) (by intro h; cases h)
          simp only [extractLeftmost, hy, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          simpa only [inorder_node, List.cons_append] using
            congrArg (fun xs => xs ++ a :: inorder r) (ihl hy)

/-- This contents decomposition is proved from the recursive label set,
independently of the inorder theorem. Repeated labels remain possible. -/
theorem extractLeftmost_mem {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (found : extractLeftmost t = some (x, s)) (z : α) :
    z ∈ setTree t ↔ z = x ∨ z ∈ setTree s := by
  induction t generalizing x s with
  | nil => cases found
  | node a l r ihl _ =>
      cases l with
      | nil =>
          simp only [extractLeftmost, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          simp only [setTree_node, setTree_nil, Set.mem_union,
            Set.mem_empty_iff_false, Set.mem_singleton_iff, false_or]
      | node b ll lr =>
          obtain ⟨y, s', hy⟩ := extractLeftmost_exists
            (t := .node b ll lr) (by intro h; cases h)
          simp only [extractLeftmost, hy, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          change ((z ∈ setTree (.node b ll lr) ∨ z = a) ∨ z ∈ setTree r) ↔
            z = y ∨ ((z ∈ setTree s' ∨ z = a) ∨ z ∈ setTree r)
          rw [ihl hy]
          tauto

theorem extractLeftmost_forall {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (found : extractLeftmost t = some (x, s)) (P : α → Prop) :
    (∀ z ∈ setTree t, P z) ↔ P x ∧ ∀ z ∈ setTree s, P z := by
  constructor
  · intro h
    exact ⟨h x ((extractLeftmost_mem found x).mpr (Or.inl rfl)),
      fun z hz => h z ((extractLeftmost_mem found z).mpr (Or.inr hz))⟩
  · rintro ⟨hx, hs⟩ z hz
    rcases (extractLeftmost_mem found z).mp hz with rfl | hz
    · exact hx
    · exact hs z hz

theorem extractLeftmost_height_le {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (found : extractLeftmost t = some (x, s)) : s.height ≤ t.height := by
  induction t generalizing x s with
  | nil => cases found
  | node a l r ihl _ =>
      cases l with
      | nil =>
          simp only [extractLeftmost, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          simp [BinaryTree.height]
      | node b ll lr =>
          obtain ⟨y, s', hy⟩ := extractLeftmost_exists
            (t := .node b ll lr) (by intro h; cases h)
          simp only [extractLeftmost, hy, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          have hheight := ihl hy
          simp only [BinaryTree.height] at hheight ⊢
          omega

/-- The paired execution recovers the old residual for every successful call. -/
theorem extractLeftmost_remainder {t : BinaryTree α} {x : α} {s : BinaryTree α}
    (found : extractLeftmost t = some (x, s)) : s = removeFirst t := by
  induction t generalizing x s with
  | nil => cases found
  | node a l r ihl _ =>
      cases l with
      | nil =>
          simp only [extractLeftmost, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          rfl
      | node b ll lr =>
          obtain ⟨y, s', hy⟩ := extractLeftmost_exists
            (t := .node b ll lr) (by intro h; cases h)
          simp only [extractLeftmost, hy, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          simp only [removeFirst, ihl hy]

/-- Nil failure and successful residuals together recover the old total API. -/
theorem extractLeftmost_remainder_projection (t : BinaryTree α) :
    ((extractLeftmost t).map Prod.snd).getD .nil = removeFirst t := by
  cases h : extractLeftmost t with
  | none =>
      have ht := (extractLeftmost_eq_none_iff t).mp h
      subst t
      rfl
  | some p =>
      simpa only [Option.map_some, Option.getD_some] using extractLeftmost_remainder h

/-- Existing first-insertion clients recover both the removed label and tree. -/
theorem extractLeftmost_of_mem_insertFirst (x : α) {s t : BinaryTree α}
    (ht : t ∈ insertFirst x s) : extractLeftmost t = some (x, s) := by
  have hne : t ≠ .nil := fun h => nil_not_mem_insertFirst x s (h ▸ ht)
  obtain ⟨y, u, hu⟩ := extractLeftmost_exists hne
  have hus : u = s := (extractLeftmost_remainder hu).trans
    (removeFirst_of_mem_insertFirst x ht)
  subst u
  have hyx : y = x := (List.cons.inj
    ((extractLeftmost_inorder hu).trans (inorder_of_mem_insertFirst x ht))).1
  subst y
  exact hu

/-- Recovery is a relation to the original insertion choices, not an inverse
recovering an arbitrary original shape from only the extracted pair. -/
theorem mem_insertFirst_iff_extractLeftmost (x : α) (s t : BinaryTree α) :
    t ∈ insertFirst x s ↔ extractLeftmost t = some (x, s) := by
  constructor
  · exact extractLeftmost_of_mem_insertFirst x
  · intro h
    obtain ⟨u, _, hu⟩ := exists_insertFirst_of_inorder_cons x (inorder s) t
      (extractLeftmost_inorder h).symm
    have hsu : s = u := (extractLeftmost_remainder h).trans
      (removeFirst_of_mem_insertFirst x hu)
    subst u
    exact hu

/-- The equality branch of successor deletion. Extraction is called only on
a nonempty right input; all complete labels, including payloads, are retained. -/
def joinLeftmost (l : BinaryTree α) : BinaryTree α → BinaryTree α
  | .nil => l
  | .node a rl rr =>
      let p := extractLeftmostNonempty (.node a rl rr) (by intro h; cases h)
      .node p.1 l p.2

@[simp] theorem joinLeftmost_nil_right (l : BinaryTree α) : joinLeftmost l .nil = l := rfl

theorem joinLeftmost_of_extract {l r s : BinaryTree α} {x : α}
    (found : extractLeftmost r = some (x, s)) : joinLeftmost l r = .node x l s := by
  cases r with
  | nil => cases found
  | node a rl rr =>
      simp only [joinLeftmost, extractLeftmostNonempty_eq (by intro h; cases h) found]

theorem inorder_joinLeftmost (l r : BinaryTree α) :
    inorder (joinLeftmost l r) = inorder l ++ inorder r := by
  cases r with
  | nil => simp
  | node a rl rr =>
      obtain ⟨x, s, h⟩ := extractLeftmost_exists
        (t := .node a rl rr) (by intro h; cases h)
      rw [joinLeftmost_of_extract h, inorder_node, extractLeftmost_inorder h]

theorem mem_setTree_joinLeftmost (l r : BinaryTree α) (z : α) :
    z ∈ setTree (joinLeftmost l r) ↔ z ∈ setTree l ∨ z ∈ setTree r := by
  cases r with
  | nil => simp
  | node a rl rr =>
      obtain ⟨x, s, h⟩ := extractLeftmost_exists
        (t := .node a rl rr) (by intro h; cases h)
      rw [joinLeftmost_of_extract h, extractLeftmost_mem h z]
      change ((z ∈ setTree l ∨ z = x) ∨ z ∈ setTree s) ↔
        z ∈ setTree l ∨ z = x ∨ z ∈ setTree s
      tauto

theorem setTree_joinLeftmost (l r : BinaryTree α) :
    setTree (joinLeftmost l r) = setTree l ∪ setTree r := by
  ext z
  exact mem_setTree_joinLeftmost l r z

theorem height_joinLeftmost_le (l r : BinaryTree α) :
    (joinLeftmost l r).height ≤ max l.height r.height + 1 := by
  cases r with
  | nil => simp [BinaryTree.height]
  | node a rl rr =>
      obtain ⟨x, s, h⟩ := extractLeftmost_exists
        (t := .node a rl rr) (by intro h; cases h)
      have hs := extractLeftmost_height_le h
      rw [joinLeftmost_of_extract h]
      simp only [BinaryTree.height] at hs ⊢
      omega

theorem numNodes_joinLeftmost (l r : BinaryTree α) :
    (joinLeftmost l r).numNodes = l.numNodes + r.numNodes := by
  rw [← inorder_length (joinLeftmost l r), inorder_joinLeftmost, List.length_append,
    inorder_length, inorder_length]

end Trees
