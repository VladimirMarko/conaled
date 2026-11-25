import Applications.Graphs.Coloring.Correctness

/-!
# Exact support of the source coloring

Successful lookup supplies the value on a finite supported subtype. The colors
of bound neighbors form its image, so they cannot outnumber those neighbors.
The actual selection's later-neighbor bound therefore prevents failure at every
right-fold step, even on raw directed, self-loop or dangling-neighbor inputs.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Graphs.Coloring

open Search.PositiveTrie

/-- A value is available only with evidence of a successful optional binding. -/
def valueAt (f : Assignment) (node : {n // n ∈ SparseMap.keys f}) : Node :=
  (SparseMap.find node.val f).get ((SparseMap.keys_isSome node.val f).mpr node.property)

theorem find_valueAt (f : Assignment) (node : {n // n ∈ SparseMap.keys f}) :
    SparseMap.find node.val f = some (valueAt f node) := (Option.some_get _).symm

theorem valueAt_eq {f : Assignment} {node : {n // n ∈ SparseMap.keys f}} {color : Node}
    (found : SparseMap.find node.val f = some color) : valueAt f node = color :=
  Option.get_of_eq_some _ found

theorem observe_colorsOf_image (f : Assignment) (vertices : NodeSet) :
    KeySet.observe (colorsOf f vertices) =
      (KeySet.observe vertices ∩ SparseMap.keys f).attach.image
        (fun node => valueAt f ⟨node.val, (Finset.mem_inter.mp node.property).2⟩) := by
  ext color
  rw [KeySet.mem_observe, mem_colorsOf, Finset.mem_image]
  constructor
  · rintro ⟨node, member, found⟩
    have present : node ∈ SparseMap.keys f := (SparseMap.mem_keys node f).mpr ⟨color, found⟩
    let boundNode : {n // n ∈ KeySet.observe vertices ∩ SparseMap.keys f} :=
      ⟨node, Finset.mem_inter.mpr ⟨(KeySet.mem_observe node vertices).mpr member, present⟩⟩
    refine ⟨boundNode, Finset.mem_attach _ _, ?_⟩
    exact valueAt_eq found
  · rintro ⟨node, _, same⟩
    refine ⟨node.val, (KeySet.mem_observe _ _).mp (Finset.mem_inter.mp node.property).1, ?_⟩
    exact (find_valueAt f ⟨node.val, (Finset.mem_inter.mp node.property).2⟩).trans
      (congrArg some same)

theorem colorsOf_card_le (f : Assignment) (vertices : NodeSet) :
    KeySet.cardinal (colorsOf f vertices) ≤ (KeySet.observe vertices ∩ SparseMap.keys f).card := by
  rw [← KeySet.observe_card, observe_colorsOf_image]
  exact Finset.card_image_le.trans_eq Finset.card_attach

theorem exists_available_color {palette : NodeSet} {g : Graph} {node : Node} {f : Assignment}
    (few : KeySet.cardinal (colorsOf f (adj g node)) < KeySet.cardinal palette) :
    ∃ color, KeySet.choose (availableColors palette g node f) = some color := by
  cases chosen : KeySet.choose (availableColors palette g node f) with
  | some color => exact ⟨color, rfl⟩
  | none =>
      have empty := (KeySet.choose_none_iff_observe_empty _).mp chosen
      rw [availableColors, KeySet.observe_diff, Finset.sdiff_eq_empty_iff_subset] at empty
      have bound := Finset.card_le_card empty
      rw [KeySet.observe_card, KeySet.observe_card] at bound
      exact (Nat.not_lt_of_ge bound few).elim

theorem keys_colorList_subset (palette : NodeSet) (g : Graph) (vertices : List Node) :
    SparseMap.keys (colorList palette g vertices) ⊆ vertices.toFinset := by
  induction vertices with
  | nil =>
      intro node member
      obtain ⟨value, found⟩ := (SparseMap.mem_keys node _).mp member
      change SparseMap.find node (.nil : Assignment) = some value at found
      rw [SparseMap.find_nil] at found
      cases found
  | cons node vertices ih =>
      intro query member
      have included := keys_color1_subset palette g node (colorList palette g vertices) member
      rcases Finset.mem_insert.mp included with same | prior
      · subst query
        exact List.mem_toFinset.mpr List.mem_cons_self
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem node (List.mem_toFinset.mp (ih prior)))

theorem keys_color_subset_select (palette : NodeSet) (g : Graph) :
    SparseMap.keys (color palette g) ⊆ (select (KeySet.cardinal palette) g).toFinset :=
  keys_colorList_subset palette g _

theorem keys_color_subset_nodes (palette : NodeSet) (g : Graph) :
    SparseMap.keys (color palette g) ⊆ SparseMap.keys g := by
  intro node member
  exact mem_select (KeySet.cardinal palette) g
    (List.mem_toFinset.mp (keys_color_subset_select palette g member))

theorem colorsOf_suffix_card_lt (palette : NodeSet) (g : Graph)
    (before after : List Node) (node : Node)
    (selected : select (KeySet.cardinal palette) g = before ++ node :: after) :
    KeySet.cardinal (colorsOf (colorList palette g after) (adj g node)) < KeySet.cardinal palette := by
  calc
    _ ≤ (neighbors g node ∩ SparseMap.keys (colorList palette g after)).card :=
      colorsOf_card_le _ _
    _ ≤ (neighbors g node ∩ after.toFinset).card := by
      apply Finset.card_le_card
      intro query member
      obtain ⟨edge, bound⟩ := Finset.mem_inter.mp member
      exact Finset.mem_inter.mpr ⟨edge, keys_colorList_subset palette g after bound⟩
    _ < KeySet.cardinal palette :=
      later_neighbors_card_lt (KeySet.cardinal palette) g before after node selected

/-- An actual coloring step in the reverse selection execution cannot fail. -/
theorem exists_color_after_suffix (palette : NodeSet) (g : Graph)
    (before after : List Node) (node : Node)
    (selected : select (KeySet.cardinal palette) g = before ++ node :: after) :
    ∃ value, KeySet.choose (availableColors palette g node (colorList palette g after)) = some value :=
  exists_available_color (colorsOf_suffix_card_lt palette g before after node selected)

/-- The condition is on original neighbors in each remaining suffix. -/
theorem keys_colorList_eq_of_later_degree (palette : NodeSet) (g : Graph) (vertices : List Node)
    (later : ∀ before after node, vertices = before ++ node :: after →
      (neighbors g node ∩ after.toFinset).card < KeySet.cardinal palette) :
    SparseMap.keys (colorList palette g vertices) = vertices.toFinset := by
  induction vertices with
  | nil =>
      ext node
      simp [SparseMap.mem_keys]
  | cons node vertices ih =>
      have tailDegree : ∀ before after current, vertices = before ++ current :: after →
          (neighbors g current ∩ after.toFinset).card < KeySet.cardinal palette := by
        intro before after current split
        exact later (node :: before) after current (congrArg (List.cons node) split)
      have tailKeys := ih tailDegree
      have few : KeySet.cardinal (colorsOf (colorList palette g vertices) (adj g node)) <
          KeySet.cardinal palette := by
        have bound := colorsOf_card_le (colorList palette g vertices) (adj g node)
        rw [tailKeys] at bound
        exact lt_of_le_of_lt bound (later [] vertices node rfl)
      obtain ⟨color, chosen⟩ := exists_available_color few
      rw [colorList_cons, keys_color1_of_some chosen, tailKeys, List.toFinset_cons]

/-- Every selected vertex receives a color; no graph-validity hypotheses occur. -/
theorem keys_color (palette : NodeSet) (g : Graph) :
    SparseMap.keys (color palette g) = (select (KeySet.cardinal palette) g).toFinset := by
  apply keys_colorList_eq_of_later_degree
  intro before after node selected
  exact later_neighbors_card_lt (KeySet.cardinal palette) g before after node selected

theorem exists_color_iff_selected (palette : NodeSet) (g : Graph) (node : Node) :
    (∃ value, SparseMap.find node (color palette g) = some value) ↔
      node ∈ select (KeySet.cardinal palette) g := by
  rw [← SparseMap.mem_keys, keys_color, List.mem_toFinset]

theorem keys_color_of_progress (palette : NodeSet) (property : Graph → Prop)
    (closed : ∀ g node, property g → node ∈ SparseMap.keys g → property (removeNode node g))
    (progress : ∀ g, property g → (SparseMap.keys g).Nonempty →
      ∃ node, KeySet.mem node (eligible (KeySet.cardinal palette) g) = true)
    (g : Graph) (valid : property g) : SparseMap.keys (color palette g) = SparseMap.keys g := by
  rw [keys_color, select_covers_of_progress (KeySet.cardinal palette) property closed progress g valid]

theorem total_coloring_of_progress (palette : NodeSet) (property : Graph → Prop)
    (closed : ∀ g node, property g → node ∈ SparseMap.keys g → property (removeNode node g))
    (progress : ∀ g, property g → (SparseMap.keys g).Nonempty →
      ∃ node, KeySet.mem node (eligible (KeySet.cardinal palette) g) = true)
    (g : Graph) (valid : property g) (symmetric : Undirected g) (loopless : NoSelfLoop g) :
    EdgeColoringCompatible palette g (color palette g) ∧ PaletteValued palette (color palette g) ∧
      SparseMap.keys (color palette g) = SparseMap.keys g :=
  ⟨color_correct palette loopless symmetric, paletteValued_color palette g,
    keys_color_of_progress palette property closed progress g valid⟩

end Graphs.Coloring
