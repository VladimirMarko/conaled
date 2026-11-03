import Applications.Trees.Shape

/-! Braun's left-biased recursive shape invariant on the ordinary node-labelled
binary tree. Labels are never inspected. The invariant, erased-shape uniqueness
and almost-complete bridge follow the source mathematics recorded with its
attribution and retained notice in `docs/research/fdsa-braun-shape.md`.
No array indexing, heap ordering, executable shape checker or cost is asserted.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v
variable {α : Type u} {β : Type v}

/-- Both children are Braun, and the left has either the same node count as
the right or exactly one more. Nil needs no label or inhabitance assumption. -/
def Braun : BinaryTree α → Prop
  | .nil => True
  | .node _ l r =>
      (l.numNodes = r.numNodes ∨ l.numNodes = r.numNodes + 1) ∧ Braun l ∧ Braun r

@[simp] theorem braun_nil : Braun (.nil : BinaryTree α) := True.intro

@[simp] theorem braun_node (a : α) (l r : BinaryTree α) :
    Braun (.node a l r) ↔
      (l.numNodes = r.numNodes ∨ l.numNodes = r.numNodes + 1) ∧ Braun l ∧ Braun r :=
  Iff.rfl

/-- The inequality form retains Braun validity of both children. -/
theorem braun_node_iff (a : α) (l r : BinaryTree α) :
    Braun (.node a l r) ↔
      r.numNodes ≤ l.numNodes ∧ l.numNodes ≤ r.numNodes + 1 ∧ Braun l ∧ Braun r := by
  rw [braun_node]
  constructor
  · rintro ⟨hsize, hl, hr⟩
    exact ⟨by omega, by omega, hl, hr⟩
  · rintro ⟨hrl, hlr, hl, hr⟩
    exact ⟨by omega, hl, hr⟩

/-- Every label map preserves and reflects Braun shape, independently of
injectivity and of the input and output payload universes. -/
theorem braun_map (label : α → β) (t : BinaryTree α) :
    Braun (t.map label) ↔ Braun t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [BinaryTree.map, braun_node, numNodes_map, ihl, ihr]

/-- Equal node counts determine the same Unit-erased shape for two Braun
trees. This does not identify their payloads or their inorder observations. -/
theorem braun_shape_eq (s : BinaryTree α) (t : BinaryTree β)
    (hs : Braun s) (ht : Braun t) (hsize : s.numNodes = t.numNodes) :
    s.map (fun _ : α => ()) = t.map (fun _ : β => ()) := by
  revert hs ht hsize
  induction s generalizing t with
  | nil =>
      intro _ _ hn
      cases t with
      | nil => rfl
      | node b tl tr =>
          simp only [BinaryTree.numNodes] at hn
          omega
  | node a sl sr ihl ihr =>
      intro hs ht hn
      cases t with
      | nil =>
          simp only [BinaryTree.numNodes] at hn
          omega
      | node b tl tr =>
          rcases (braun_node_iff a sl sr).1 hs with ⟨hsrl, hslr, hsl, hsr⟩
          rcases (braun_node_iff b tl tr).1 ht with ⟨htrl, htlr, htl, htr⟩
          have hcounts : sl.numNodes = tl.numNodes ∧ sr.numNodes = tr.numNodes := by
            simp only [BinaryTree.numNodes] at hn
            omega
          simp only [BinaryTree.map,
            ihl tl hsl htl hcounts.1, ihr tr hsr htr hcounts.2]

/-- The source Unit-labelled uniqueness statement is a specialization of
erased-shape uniqueness, without a canonical-tree construction. -/
theorem braun_eq_of_numNodes_eq (s t : BinaryTree Unit)
    (hs : Braun s) (ht : Braun t) (hsize : s.numNodes = t.numNodes) : s = t := by
  have hid : (fun _ : Unit => ()) = id := by
    funext a
    cases a
    rfl
  simpa only [hid, BinaryTree.id_map] using braun_shape_eq s t hs ht hsize

/-- Braun's recursive size condition makes the tree almost complete. Exact
logarithmic heights and height optimality then use the existing shape API. -/
theorem braun_almostComplete (t : BinaryTree α) (ht : Braun t) :
    AlmostComplete t := by
  revert ht
  induction t with
  | nil =>
      intro _
      exact almostComplete_nil
  | node a l r ihl ihr =>
      intro ht
      rcases (braun_node_iff a l r).1 ht with ⟨hrl, hlr, hl, hr⟩
      exact almostComplete_node_of_numNodes_balance a l r (ihl hl) (ihr hr)
        hlr (hrl.trans (Nat.le_succ l.numNodes))

end Trees
