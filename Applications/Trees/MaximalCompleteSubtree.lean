import Applications.Trees.Completeness

/-! One-fold selection of a maximal-height complete structural subtree.
The executable state retains the original subtree, the shared completeness
summary, and the selected descendant with its height. A node uses only the
supplied child summaries. It selects the whole reconstructed node when its
flag is true, otherwise the taller child selection, breaking ties to the left.
No label or tree equality, subtree enumeration, or child traversal is used.

Correctness concerns states actually produced by the fold; arbitrary raw
states need not have correct selections or heights. Structural containment
and reconstruction do not establish allocation or physical-sharing claims.
Source and statement assessment: `docs/research/fdsa-tree-completeness.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.MaximalCompleteSubtree
universe u
variable {α : Type u}

/-- Concrete state for this algorithm, using the existing tree carrier. -/
structure State (α : Type u) where
  original : BinaryTree α
  shape : Bool × Nat
  selected : BinaryTree α
  selectedHeight : Nat

def empty : State α := ⟨.nil, Completeness.empty, .nil, 0⟩

/-- Reconstruct once and select using the shared flag and cached natural heights. -/
def combine (left : State α) (a : α) (right : State α) : State α :=
  let original := BinaryTree.node a left.original right.original
  let shape := Completeness.combine left.shape a right.shape
  let best :=
    if shape.1 then (original, shape.2)
    else if right.selectedHeight ≤ left.selectedHeight then
      (left.selected, left.selectedHeight)
    else (right.selected, right.selectedHeight)
  ⟨original, shape, best.1, best.2⟩

/-- The only input-tree recursion in the algorithm. -/
def summary (t : BinaryTree α) : State α := Trees.fold empty combine t

def select (t : BinaryTree α) : BinaryTree α := (summary t).selected

@[simp] theorem summary_nil : summary (.nil : BinaryTree α) = empty := rfl

theorem summary_node (a : α) (l r : BinaryTree α) :
    summary (.node a l r) = combine (summary l) a (summary r) := rfl

/-- Reconstruction is an unconditional homomorphic projection of raw states. -/
theorem summary_original (t : BinaryTree α) : (summary t).original = t := by
  calc
    (summary t).original =
        Trees.fold (.nil : BinaryTree α) (fun l a r => .node a l r) t :=
      Trees.fold_fusion empty combine (.nil : BinaryTree α) (fun l a r => .node a l r)
        State.original rfl (fun _ _ _ => rfl) t
    _ = t := by
      induction t with
      | nil => rfl
      | node a l r ihl ihr => simp only [Trees.fold_node, ihl, ihr]

/-- The same fold has exactly the already verified shared shape summary. -/
theorem summary_shape (t : BinaryTree α) : (summary t).shape = Completeness.summary t :=
  Trees.fold_fusion empty combine Completeness.empty Completeness.combine
    State.shape rfl (fun _ _ _ => rfl) t

private theorem complete_fields (t : BinaryTree α) (ht : Complete t) :
    (summary t).selected = t ∧ (summary t).selectedHeight = t.height := by
  cases t with
  | nil => exact ⟨rfl, rfl⟩
  | node a l r =>
      have hs : Completeness.combine (summary l).shape a (summary r).shape =
          Completeness.summary (.node a l r) := by
        simpa only [summary_node, combine] using summary_shape (.node a l r)
      have hf : (Completeness.combine (summary l).shape a (summary r).shape).1 = true :=
        (congrArg Prod.fst hs).trans ((Completeness.summary_complete _).mpr ht)
      have hh : (Completeness.combine (summary l).shape a (summary r).shape).2 =
          (BinaryTree.node a l r).height :=
        (congrArg Prod.snd hs).trans (Completeness.summary_height _)
      constructor
      · simp only [summary_node, combine, ite_eq_left hf, summary_original]
      · simpa only [summary_node, combine, ite_eq_left hf] using hh

/-- The selected-result invariant holds for reachable fold states. The maximum
ranges over all complete structural descendants, including nil and the input. -/
theorem summary_correct (t : BinaryTree α) :
    Subtree (summary t).selected t ∧
      Complete (summary t).selected ∧
      (summary t).selectedHeight = (summary t).selected.height ∧
      ∀ s, Subtree s t → Complete s → s.height ≤ (summary t).selectedHeight := by
  induction t with
  | nil =>
      refine ⟨Subtree.refl _, complete_nil, rfl, ?_⟩
      intro s hs _
      rw [(subtree_nil_iff s).mp hs]
      exact Nat.le_refl 0
  | node a l r ihl ihr =>
      by_cases ht : Complete (.node a l r)
      · obtain ⟨hselected, hheight⟩ := complete_fields (.node a l r) ht
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hselected]
          exact Subtree.refl _
        · rw [hselected]
          exact ht
        · rw [hheight, hselected]
        · intro s hs _
          rw [hheight]
          exact hs.height_le
      · have hs : Completeness.combine (summary l).shape a (summary r).shape =
            Completeness.summary (.node a l r) := by
          simpa only [summary_node, combine] using summary_shape (.node a l r)
        have hf : (Completeness.combine (summary l).shape a (summary r).shape).1 ≠ true := by
          intro h
          exact ht ((Completeness.summary_complete _).mp ((congrArg Prod.fst hs).symm.trans h))
        have hmax : ∀ s, Subtree s (.node a l r) → Complete s →
            s.height ≤ max (summary l).selectedHeight (summary r).selectedHeight := by
          intro s hsub hc
          rcases (subtree_node_iff s a l r).mp hsub with hself | hleft | hright
          · subst s
            exact False.elim (ht hc)
          · exact (ihl.2.2.2 s hleft hc).trans (le_max_left _ _)
          · exact (ihr.2.2.2 s hright hc).trans (le_max_right _ _)
        by_cases hle : (summary r).selectedHeight ≤ (summary l).selectedHeight
        · have hselected : (summary (.node a l r)).selected = (summary l).selected := by
            simp only [summary_node, combine, ite_eq_right hf, ite_eq_left hle]
          have hheight : (summary (.node a l r)).selectedHeight = (summary l).selectedHeight := by
            simp only [summary_node, combine, ite_eq_right hf, ite_eq_left hle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hselected]
            exact Subtree.left a ihl.1
          · rw [hselected]
            exact ihl.2.1
          · rw [hheight, hselected]
            exact ihl.2.2.1
          · intro s hsub hc
            rw [hheight]
            simpa only [max_eq_left hle] using hmax s hsub hc
        · have hselected : (summary (.node a l r)).selected = (summary r).selected := by
            simp only [summary_node, combine, ite_eq_right hf, ite_eq_right hle]
          have hheight : (summary (.node a l r)).selectedHeight = (summary r).selectedHeight := by
            simp only [summary_node, combine, ite_eq_right hf, ite_eq_right hle]
          have hlr : (summary l).selectedHeight ≤ (summary r).selectedHeight := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hselected]
            exact Subtree.right a ihr.1
          · rw [hselected]
            exact ihr.2.1
          · rw [hheight, hselected]
            exact ihr.2.2.1
          · intro s hsub hc
            rw [hheight]
            simpa only [max_eq_right hlr] using hmax s hsub hc

theorem selected_height (t : BinaryTree α) :
    (summary t).selectedHeight = (select t).height := (summary_correct t).2.2.1

/-- The public result is a complete structural descendant of greatest height. -/
theorem correct (t : BinaryTree α) :
    Subtree (select t) t ∧ Complete (select t) ∧
      ∀ s, Subtree s t → Complete s → s.height ≤ (select t).height := by
  obtain ⟨hs, hc, hh, hm⟩ := summary_correct t
  refine ⟨hs, hc, ?_⟩
  intro s hsub hcomplete
  rw [← selected_height t]
  exact hm s hsub hcomplete

theorem selected_subtree (t : BinaryTree α) : Subtree (select t) t := (correct t).1

theorem selected_complete (t : BinaryTree α) : Complete (select t) := (correct t).2.1

theorem maximal {s t : BinaryTree α} (hs : Subtree s t) (hc : Complete s) :
    s.height ≤ (select t).height := (correct t).2.2 s hs hc

theorem select_of_complete (t : BinaryTree α) (ht : Complete t) : select t = t :=
  (complete_fields t ht).1

@[simp] theorem select_nil : select (.nil : BinaryTree α) = .nil := rfl

/-- An incomplete node chooses by selected heights, with equality going left. -/
theorem select_node_of_not_complete (a : α) (l r : BinaryTree α)
    (ht : ¬ Complete (.node a l r)) :
    select (.node a l r) =
      if (select r).height ≤ (select l).height then select l else select r := by
  have hs : Completeness.combine (summary l).shape a (summary r).shape =
      Completeness.summary (.node a l r) := by
    simpa only [summary_node, combine] using summary_shape (.node a l r)
  have hf : (Completeness.combine (summary l).shape a (summary r).shape).1 ≠ true := by
    intro h
    exact ht ((Completeness.summary_complete _).mp ((congrArg Prod.fst hs).symm.trans h))
  change (summary (.node a l r)).selected =
    if (summary r).selected.height ≤ (summary l).selected.height then
      (summary l).selected else (summary r).selected
  simp only [summary_node, combine, ite_eq_right hf,
    (summary_correct l).2.2.1, (summary_correct r).2.2.1]
  split <;> simp_all

end Trees.MaximalCompleteSubtree
