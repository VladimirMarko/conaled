import Applications.Graphs.Coloring.Coloring

/-!
# Source compatibility and palette membership

The source predicate is guarded by an edge in both clauses. Its proof permits
arbitrary input colorings and repeated vertices. Palette membership for every
produced binding is a separate, stronger invariant without graph hypotheses.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Graphs.Coloring

open Search.PositiveTrie

def EdgeColoringCompatible (palette : NodeSet) (g : Graph) (f : Assignment) : Prop :=
  ∀ left right, Adjacent g left right →
    (∀ color, SparseMap.find left f = some color → KeySet.mem color palette = true) ∧
    (∀ first second, SparseMap.find left f = some first →
      SparseMap.find right f = some second → first ≠ second)

def PaletteValued (palette : NodeSet) (f : Assignment) : Prop :=
  ∀ node color, SparseMap.find node f = some color → KeySet.mem color palette = true

theorem edgeColoringCompatible_nil (palette : NodeSet) (g : Graph) : EdgeColoringCompatible palette g .nil := by
  intro left _ _
  constructor
  · intro _ found
    simp only [SparseMap.find_nil] at found
    cases found
  · intro _ _ found
    simp only [SparseMap.find_nil] at found
    cases found

theorem paletteValued_nil (palette : NodeSet) : PaletteValued palette .nil := by
  intro _ _ found
  simp only [SparseMap.find_nil] at found
  cases found

theorem paletteValued_color1 {palette : NodeSet} {g : Graph} {node : Node} {f : Assignment}
    (previous : PaletteValued palette f) : PaletteValued palette (color1 palette g node f) := by
  cases chosen : KeySet.choose (availableColors palette g node f) with
  | none => rwa [color1_of_none chosen]
  | some color =>
      rw [color1_of_some chosen]
      intro query value found
      by_cases same : query = node
      · subst query
        rw [SparseMap.find_add_same] at found
        cases found
        exact (chosen_color_facts chosen).1
      · rw [SparseMap.find_add_other node query color f same] at found
        exact previous query value found

theorem edgeColoringCompatible_color1 {palette : NodeSet} {g : Graph} {node : Node} {f : Assignment}
    (symmetric : Undirected g) (loopless : NoSelfLoop g) (previous : EdgeColoringCompatible palette g f) :
    EdgeColoringCompatible palette g (color1 palette g node f) := by
  cases chosen : KeySet.choose (availableColors palette g node f) with
  | none => rwa [color1_of_none chosen]
  | some color =>
      rw [color1_of_some chosen]
      intro left right edge
      constructor
      · intro value found
        by_cases same : left = node
        · subst left
          rw [SparseMap.find_add_same] at found
          cases found
          exact (chosen_color_facts chosen).1
        · rw [SparseMap.find_add_other node left color f same] at found
          exact (previous left right edge).1 value found
      · intro first second foundLeft foundRight
        by_cases leftSame : left = node
        · subst left
          by_cases rightSame : right = node
          · subst right
            exact (loopless node edge).elim
          · rw [SparseMap.find_add_same] at foundLeft
            cases foundLeft
            rw [SparseMap.find_add_other node right color f rightSame] at foundRight
            exact chosen_color_ne chosen edge foundRight
        · rw [SparseMap.find_add_other node left color f leftSame] at foundLeft
          by_cases rightSame : right = node
          · subst right
            rw [SparseMap.find_add_same] at foundRight
            cases foundRight
            exact (chosen_color_ne chosen (symmetric left node edge) foundLeft).symm
          · rw [SparseMap.find_add_other node right color f rightSame] at foundRight
            exact (previous left right edge).2 first second foundLeft foundRight

theorem paletteValued_colorList (palette : NodeSet) (g : Graph) (vertices : List Node) :
    PaletteValued palette (colorList palette g vertices) := by
  induction vertices with
  | nil => exact paletteValued_nil palette
  | cons node vertices ih => exact paletteValued_color1 ih

theorem edgeColoringCompatible_colorList (palette : NodeSet) {g : Graph}
    (symmetric : Undirected g) (loopless : NoSelfLoop g) (vertices : List Node) :
    EdgeColoringCompatible palette g (colorList palette g vertices) := by
  induction vertices with
  | nil => exact edgeColoringCompatible_nil palette g
  | cons node vertices ih => exact edgeColoringCompatible_color1 symmetric loopless ih

theorem paletteValued_color (palette : NodeSet) (g : Graph) : PaletteValued palette (color palette g) :=
  paletteValued_colorList palette g _

/-- Source color_correct, specialized to the actual computed selection list. -/
theorem color_correct (palette : NodeSet) {g : Graph}
    (loopless : NoSelfLoop g) (symmetric : Undirected g) : EdgeColoringCompatible palette g (color palette g) :=
  edgeColoringCompatible_colorList palette symmetric loopless _

theorem edgeColoringCompatible_of_no_edges (palette : NodeSet) {g : Graph} (f : Assignment)
    (edgeless : ∀ left right, ¬ Adjacent g left right) : EdgeColoringCompatible palette g f :=
  fun left right edge => (edgeless left right edge).elim

end Graphs.Coloring
