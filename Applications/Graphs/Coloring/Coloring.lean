import Applications.Graphs.Coloring.Selection

/-!
# The source coloring program

Colors remain optional bindings. The neighbor-color fold skips absent bindings;
the update overwrites on successful choice and preserves the entire input on
failure. The right fold always reads adjacency in the original graph.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Graphs.Coloring

open Search.PositiveTrie

abbrev Assignment := NodeMap Node

def colorsOf (f : Assignment) (vertices : NodeSet) : NodeSet :=
  KeySet.fold (fun node acc =>
    match SparseMap.find node f with
    | some color => KeySet.add color acc
    | none => acc) vertices .nil

theorem mem_colorsFold (f : Assignment) (vertices : List Node) (seed : NodeSet) (color : Node) :
    KeySet.mem color (vertices.foldl (fun acc node =>
      match SparseMap.find node f with
      | some value => KeySet.add value acc
      | none => acc) seed) = true ↔
      KeySet.mem color seed = true ∨
        ∃ node ∈ vertices, SparseMap.find node f = some color := by
  induction vertices generalizing seed with
  | nil => simp
  | cons node vertices ih =>
      rw [List.foldl_cons, ih]
      cases found : SparseMap.find node f with
      | none => simp [found]
      | some value =>
          simp only [KeySet.mem_add, Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro ((same | member) | ⟨query, member, bound⟩)
            · exact Or.inr ⟨node, List.mem_cons_self, by rw [same]; exact found⟩
            · exact Or.inl member
            · exact Or.inr ⟨query, List.mem_cons_of_mem node member, bound⟩
          · rintro (member | ⟨query, member, bound⟩)
            · exact Or.inl (Or.inr member)
            · rcases List.mem_cons.mp member with same | member
              · subst query
                rw [found] at bound
                exact Or.inl (Or.inl (Option.some.inj bound).symm)
              · exact Or.inr ⟨query, member, bound⟩

theorem mem_colorsOf (f : Assignment) (vertices : NodeSet) (color : Node) :
    KeySet.mem color (colorsOf f vertices) = true ↔
      ∃ node, KeySet.mem node vertices = true ∧ SparseMap.find node f = some color := by
  rw [colorsOf, KeySet.fold_eq, mem_colorsFold]
  simp only [KeySet.mem_nil, Bool.false_eq_true, false_or, KeySet.mem_elements]

theorem in_colorsOf {f : Assignment} {vertices : NodeSet} {node color : Node}
    (member : KeySet.mem node vertices = true) (found : SparseMap.find node f = some color) :
    KeySet.mem color (colorsOf f vertices) = true :=
  (mem_colorsOf f vertices color).mpr ⟨node, member, found⟩

theorem colorsOf_observe_congr {f h : Assignment} {left right : NodeSet}
    (lookups : ∀ node, SparseMap.find node f = SparseMap.find node h)
    (sets : KeySet.observe left = KeySet.observe right) :
    KeySet.observe (colorsOf f left) = KeySet.observe (colorsOf h right) := by
  ext color
  simp only [KeySet.mem_observe, mem_colorsOf]
  have members (node : Node) : KeySet.mem node left = true ↔ KeySet.mem node right = true := by
    rw [← KeySet.mem_observe, ← KeySet.mem_observe, sets]
  simp only [members, lookups]

def availableColors (palette : NodeSet) (g : Graph) (node : Node) (f : Assignment) : NodeSet :=
  KeySet.diff palette (colorsOf f (adj g node))

theorem mem_availableColors (palette : NodeSet) (g : Graph) (node : Node) (f : Assignment)
    (color : Node) :
    KeySet.mem color (availableColors palette g node f) = true ↔
      KeySet.mem color palette = true ∧ ¬ KeySet.mem color (colorsOf f (adj g node)) = true := by
  simp [availableColors, KeySet.mem_diff]

theorem chosen_color_facts {palette : NodeSet} {g : Graph} {node color : Node} {f : Assignment}
    (chosen : KeySet.choose (availableColors palette g node f) = some color) :
    KeySet.mem color palette = true ∧ ¬ KeySet.mem color (colorsOf f (adj g node)) = true :=
  (mem_availableColors palette g node f color).mp (KeySet.choose_mem _ chosen)

theorem chosen_color_ne {palette : NodeSet} {g : Graph} {node neighbor color value : Node}
    {f : Assignment} (chosen : KeySet.choose (availableColors palette g node f) = some color)
    (edge : Adjacent g node neighbor) (found : SparseMap.find neighbor f = some value) :
    color ≠ value := by
  intro same
  subst value
  exact (chosen_color_facts chosen).2 (in_colorsOf edge found)

def color1 (palette : NodeSet) (g : Graph) (node : Node) (f : Assignment) : Assignment :=
  match KeySet.choose (availableColors palette g node f) with
  | some color => SparseMap.add node color f
  | none => f

theorem color1_of_some {palette : NodeSet} {g : Graph} {node color : Node} {f : Assignment}
    (chosen : KeySet.choose (availableColors palette g node f) = some color) :
    color1 palette g node f = SparseMap.add node color f := by rw [color1, chosen]

theorem color1_of_none {palette : NodeSet} {g : Graph} {node : Node} {f : Assignment}
    (absent : KeySet.choose (availableColors palette g node f) = none) :
    color1 palette g node f = f := by rw [color1, absent]

theorem find_color1 (palette : NodeSet) (g : Graph) (node query : Node) (f : Assignment) :
    SparseMap.find query (color1 palette g node f) =
      match KeySet.choose (availableColors palette g node f) with
      | some color => if query = node then some color else SparseMap.find query f
      | none => SparseMap.find query f := by
  cases chosen : KeySet.choose (availableColors palette g node f) <;>
    simp only [color1, chosen, SparseMap.find_add]

theorem find_color1_other (palette : NodeSet) (g : Graph) (node query : Node) (f : Assignment)
    (different : query ≠ node) :
    SparseMap.find query (color1 palette g node f) = SparseMap.find query f := by
  rw [find_color1]
  cases KeySet.choose (availableColors palette g node f) <;> simp [different]

theorem keys_color1_of_some {palette : NodeSet} {g : Graph} {node color : Node} {f : Assignment}
    (chosen : KeySet.choose (availableColors palette g node f) = some color) :
    SparseMap.keys (color1 palette g node f) = Insert.insert node (SparseMap.keys f) := by
  rw [color1_of_some chosen, SparseMap.keys_add]

theorem keys_color1_subset (palette : NodeSet) (g : Graph) (node : Node) (f : Assignment) :
    SparseMap.keys (color1 palette g node f) ⊆ Insert.insert node (SparseMap.keys f) := by
  cases chosen : KeySet.choose (availableColors palette g node f) with
  | none => rw [color1_of_none chosen]; exact Finset.subset_insert _ _
  | some color => rw [keys_color1_of_some chosen]

def colorList (palette : NodeSet) (g : Graph) (vertices : List Node) : Assignment :=
  vertices.foldr (color1 palette g) .nil

@[simp] theorem colorList_nil (palette : NodeSet) (g : Graph) : colorList palette g [] = .nil := rfl

@[simp] theorem colorList_cons (palette : NodeSet) (g : Graph) (node : Node)
    (vertices : List Node) :
    colorList palette g (node :: vertices) = color1 palette g node (colorList palette g vertices) :=
  rfl

theorem colorList_eq_reverse_foldl (palette : NodeSet) (g : Graph) (vertices : List Node) :
    colorList palette g vertices =
      vertices.reverse.foldl (fun f node => color1 palette g node f) .nil :=
  List.foldr_eq_foldl_reverse

def color (palette : NodeSet) (g : Graph) : Assignment :=
  colorList palette g (select (KeySet.cardinal palette) g)

theorem color_empty_palette (g : Graph) : color .nil g = .nil := by
  rw [color, show KeySet.cardinal .nil = 0 from rfl, select_zero, colorList_nil]

theorem color_empty_graph (palette : NodeSet) : color palette .nil = .nil := by
  rw [color, select_of_none (KeySet.cardinal palette) .nil rfl, colorList_nil]

theorem availableColors_observe_congr {palette otherPalette : NodeSet} {g h : Graph}
    {f other : Assignment} (palettes : KeySet.observe palette = KeySet.observe otherPalette)
    (graphs : observe g = observe h) (assignments : SparseMap.observe f = SparseMap.observe other)
    (node : Node) :
    KeySet.observe (availableColors palette g node f) =
      KeySet.observe (availableColors otherPalette h node other) := by
  rw [availableColors, availableColors, KeySet.observe_diff, KeySet.observe_diff, palettes]
  congr 1
  apply colorsOf_observe_congr
  · intro query
    simpa only [SparseMap.observe_lookup] using congrArg (fun view => view.lookup query) assignments
  · exact neighbors_congr graphs node

theorem color1_observe_congr {palette otherPalette : NodeSet} {g h : Graph}
    {f other : Assignment} (palettes : KeySet.observe palette = KeySet.observe otherPalette)
    (graphs : observe g = observe h) (assignments : SparseMap.observe f = SparseMap.observe other)
    (node : Node) :
    SparseMap.observe (color1 palette g node f) =
      SparseMap.observe (color1 otherPalette h node other) := by
  have available := availableColors_observe_congr palettes graphs assignments node
  have choices : KeySet.choose (availableColors palette g node f) =
      KeySet.choose (availableColors otherPalette h node other) := by
    apply KeySet.choose_ext
    intro value
    apply Bool.eq_iff_iff.mpr
    rw [← KeySet.mem_observe, ← KeySet.mem_observe, available]
  cases chosen : KeySet.choose (availableColors palette g node f) with
  | none => rw [color1_of_none chosen, color1_of_none (choices.symm.trans chosen), assignments]
  | some value =>
      rw [color1_of_some chosen, color1_of_some (choices.symm.trans chosen),
        SparseMap.observe_add, SparseMap.observe_add, assignments]

theorem colorList_observe_congr {palette otherPalette : NodeSet} {g h : Graph}
    (palettes : KeySet.observe palette = KeySet.observe otherPalette)
    (graphs : observe g = observe h) (vertices : List Node) :
    SparseMap.observe (colorList palette g vertices) =
      SparseMap.observe (colorList otherPalette h vertices) := by
  induction vertices with
  | nil => rfl
  | cons node vertices ih => exact color1_observe_congr palettes graphs ih node

theorem color_observe_congr {palette otherPalette : NodeSet} {g h : Graph}
    (palettes : KeySet.observe palette = KeySet.observe otherPalette) (graphs : observe g = observe h) :
    SparseMap.observe (color palette g) = SparseMap.observe (color otherPalette h) := by
  have cards : KeySet.cardinal palette = KeySet.cardinal otherPalette := by
    simpa only [KeySet.observe_card] using congrArg Finset.card palettes
  rw [color, color, cards, select_observe_congr (KeySet.cardinal otherPalette) graphs]
  exact colorList_observe_congr palettes graphs _

end Graphs.Coloring
