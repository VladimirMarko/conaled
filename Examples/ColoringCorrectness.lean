import Applications.Graphs.Coloring.SimpleGraph
import Examples.ColoringSelection

/-!
# Exact coloring and semantic boundary cases

Expected results were calculated independently from the source before
implementation. Optional lookup, original adjacency, update order and the
weak edge-guarded source predicate are exercised through public interfaces.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ColoringCorrectness

open Search.PositiveTrie Graphs.Coloring ColoringSelection

def collisionNeighbors : NodeSet := ([1, 2, 4] : List Node).foldr KeySet.add .nil

def collisionColoring : Assignment := SparseMap.add 1 3 (SparseMap.add 2 3 .nil)

theorem collision_colors : KeySet.elements (colorsOf collisionColoring collisionNeighbors) = [3] := by
  decide

theorem collision_membership (value : Node) :
    KeySet.mem value (colorsOf collisionColoring collisionNeighbors) = true ↔
      ∃ node, KeySet.mem node collisionNeighbors = true ∧
        SparseMap.find node collisionColoring = some value :=
  mem_colorsOf collisionColoring collisionNeighbors value

theorem collision_introduction :
    KeySet.mem 3 (colorsOf collisionColoring collisionNeighbors) = true :=
  in_colorsOf (node := 2) rfl rfl

theorem absent_neighbor : SparseMap.find 4 collisionColoring = none := rfl

def oneColor : NodeSet := KeySet.add 1 .nil

def twoColors : NodeSet := ([1, 2] : List Node).foldr KeySet.add .nil

def blockedColoring : Assignment := SparseMap.add 1 7 (SparseMap.add 2 1 .nil)

theorem failed_step_preserves : color1 oneColor directed 1 blockedColoring = blockedColoring :=
  color1_of_none rfl

theorem failed_step_old_binding :
    SparseMap.find 1 (color1 oneColor directed 1 blockedColoring) = some 7 := by
  rw [failed_step_preserves]
  rfl

theorem successful_overwrite :
    SparseMap.find 1 (color1 oneColor directed 1 (SparseMap.add 1 7 .nil)) = some 1 := by
  rw [color1_of_some (color := 1) rfl, SparseMap.find_add_same]

theorem collision_image_bound :
    KeySet.cardinal (colorsOf collisionColoring collisionNeighbors) ≤
      (KeySet.observe collisionNeighbors ∩ SparseMap.keys collisionColoring).card :=
  colorsOf_card_le collisionColoring collisionNeighbors

theorem collision_counts :
    KeySet.cardinal (colorsOf collisionColoring collisionNeighbors) = 1 ∧
      (KeySet.observe collisionNeighbors ∩ SparseMap.keys collisionColoring).card = 2 := by
  decide

theorem source_entries :
    SparseMap.elements (color palette sourceGraph) = [(4, 1), (2, 3), (6, 2), (1, 2), (5, 1)] := by
  rw [color, palette_cardinal, sourceGraph_selection]
  decide

theorem source_compatible : EdgeColoringCompatible palette sourceGraph (color palette sourceGraph) :=
  color_correct palette sourceGraph_noSelfLoop sourceGraph_undirected

theorem source_paletteValued : PaletteValued palette (color palette sourceGraph) :=
  paletteValued_color palette sourceGraph

theorem source_keys : SparseMap.keys (color palette sourceGraph) = SparseMap.keys sourceGraph := by
  rw [keys_color, palette_cardinal, sourceGraph_selection]
  decide

theorem source_support (node : Node) :
    (∃ value, SparseMap.find node (color palette sourceGraph) = some value) ↔
      node ∈ ([4, 1, 2, 6, 5] : List Node) := by
  simpa only [palette_cardinal, sourceGraph_selection] using
    exists_color_iff_selected palette sourceGraph node

theorem source_reverse_execution :
    color palette sourceGraph =
      ([5, 6, 2, 1, 4] : List Node).foldl (fun f node => color1 palette sourceGraph node f) .nil := by
  rw [color, palette_cardinal, sourceGraph_selection, colorList_eq_reverse_foldl]
  rfl

def sourceClient := producedColoring palette sourceGraph sourceGraph_undirected sourceGraph_noSelfLoop

theorem source_client_one :
    (sourceClient ⟨1, by rw [source_keys]; decide⟩).val = 2 := by
  apply Option.some.inj
  have actual : SparseMap.find 1 (color palette sourceGraph) = some 2 := by
    rw [color, palette_cardinal, sourceGraph_selection]
    rfl
  exact (producedColoring_lookup palette sourceGraph sourceGraph_undirected
    sourceGraph_noSelfLoop ⟨1, by rw [source_keys]; decide⟩).symm.trans actual

theorem source_client_distinct (left right : {n // n ∈ SparseMap.keys (color palette sourceGraph)})
    (edge : Adjacent sourceGraph left.val right.val) : sourceClient left ≠ sourceClient right :=
  sourceClient.valid edge

theorem source_client_vertex_count :
    Fintype.card {node // node ∈ SparseMap.keys (color palette sourceGraph)} = 5 := by
  rw [Fintype.card_coe, source_keys, SparseMap.keys_card, sourceGraph_cardinal]

theorem source_client_palette_count : Fintype.card {value // value ∈ KeySet.observe palette} = 3 := by
  rw [palette_value_count, palette_cardinal]

theorem empty_graph_coloring : color palette .nil = .nil := color_empty_graph palette

theorem empty_palette_coloring : color .nil sourceGraph = .nil := color_empty_palette sourceGraph

theorem isolated_entries : SparseMap.elements (color oneColor isolated) = [(1, 1)] := by
  rw [color, show KeySet.cardinal oneColor = 1 from rfl, isolated_selection]
  decide

theorem isolated_has_no_edges (left right : Node) : ¬ Adjacent isolated left right := by
  by_cases same : left = 1 <;>
    simp [Adjacent, adj, isolated, SparseMap.find_add, same]

theorem isolated_weak_accepts : EdgeColoringCompatible .nil isolated (SparseMap.add 1 7 .nil) :=
  edgeColoringCompatible_of_no_edges .nil _ isolated_has_no_edges

theorem isolated_outside_palette : ¬ PaletteValued .nil (SparseMap.add 1 7 .nil) := by
  intro paletteOnly
  have impossible := paletteOnly 1 7 rfl
  cases impossible

theorem isolated_produced_palette : PaletteValued oneColor (color oneColor isolated) :=
  paletteValued_color oneColor isolated

theorem padded_coloring_observation :
    SparseMap.observe (color oneColor paddedIsolated) = SparseMap.observe (color oneColor isolated) :=
  color_observe_congr rfl paddedIsolated_observation

theorem padded_coloring_support :
    SparseMap.keys (color oneColor paddedIsolated) = ([1] : List Node).toFinset := by
  rw [keys_color, show KeySet.cardinal oneColor = 1 from rfl, paddedIsolated_selection]

theorem isolated_undirected : Undirected isolated :=
  fun left right edge => (isolated_has_no_edges left right edge).elim

theorem isolated_noSelfLoop : NoSelfLoop isolated := fun node => isolated_has_no_edges node node

theorem empty_undirected : Undirected (.nil : Graph) := undirected_mkGraph []

theorem empty_noSelfLoop : NoSelfLoop (.nil : Graph) := by
  intro node
  simp [Adjacent, adj]

theorem isolated_simple_observation_distinct :
    simpleObservation isolated isolated_undirected isolated_noSelfLoop ≠
      simpleObservation .nil empty_undirected empty_noSelfLoop := by
  intro same
  exact isolated_distinct_observation ((simpleObservation_eq_iff isolated .nil
    isolated_undirected isolated_noSelfLoop empty_undirected empty_noSelfLoop).mp same)

theorem source_second_step_succeeds :
    ∃ value, KeySet.choose (availableColors palette sourceGraph 1
      (colorList palette sourceGraph [2, 6, 5])) = some value := by
  apply exists_color_after_suffix palette sourceGraph [4] [2, 6, 5] 1
  rw [palette_cardinal, sourceGraph_selection]
  rfl

theorem directed_result :
    color oneColor directed = SparseMap.add 2 1 (SparseMap.add 1 1 .nil) := by
  rw [color, show KeySet.cardinal oneColor = 1 from rfl, directed_selection]
  rfl

theorem directed_entries : SparseMap.elements (color oneColor directed) = [(2, 1), (1, 1)] := by
  rw [directed_result]
  decide

theorem directed_support : SparseMap.keys (color oneColor directed) = SparseMap.keys directed := by
  rw [keys_color, show KeySet.cardinal oneColor = 1 from rfl, directed_selection]
  decide

theorem directed_palette : PaletteValued oneColor (color oneColor directed) :=
  paletteValued_color oneColor directed

theorem directed_incompatible : ¬ EdgeColoringCompatible oneColor directed (color oneColor directed) := by
  rw [directed_result]
  intro compatible
  exact (compatible 1 2 rfl).2 1 1 rfl rfl rfl

theorem selfLoop_result : color twoColors selfLoop = SparseMap.add 1 1 .nil := by
  rw [color, show KeySet.cardinal twoColors = 2 from rfl, selfLoop_selection]
  rfl

theorem selfLoop_support : SparseMap.keys (color twoColors selfLoop) = SparseMap.keys selfLoop := by
  rw [keys_color, show KeySet.cardinal twoColors = 2 from rfl, selfLoop_selection]
  decide

theorem selfLoop_palette : PaletteValued twoColors (color twoColors selfLoop) :=
  paletteValued_color twoColors selfLoop

theorem selfLoop_incompatible : ¬ EdgeColoringCompatible twoColors selfLoop (color twoColors selfLoop) := by
  rw [selfLoop_result]
  intro compatible
  exact (compatible 1 1 selfLoop_present).2 1 1 rfl rfl rfl

def pairGraph : Graph := mkGraph [(1, 2)]

theorem pairGraph_undirected : Undirected pairGraph := undirected_mkGraph _

theorem pairGraph_noSelfLoop : NoSelfLoop pairGraph := by
  apply noSelfLoop_mkGraph
  intro edge member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst edge
  decide

theorem repeated_list_entries :
    SparseMap.elements (colorList twoColors pairGraph [1, 2, 1]) = [(2, 2), (1, 1)] := by
  decide

theorem repeated_list_compatible : EdgeColoringCompatible twoColors pairGraph (colorList twoColors pairGraph [1, 2, 1]) :=
  edgeColoringCompatible_colorList twoColors pairGraph_undirected pairGraph_noSelfLoop [1, 2, 1]

theorem overwritten_vertex_present :
    SparseMap.find 1 (colorList twoColors pairGraph [2, 1]) = some 1 := rfl

theorem overwrite_preserves_compatibility :
    EdgeColoringCompatible twoColors pairGraph (color1 twoColors pairGraph 1 (colorList twoColors pairGraph [2, 1])) :=
  edgeColoringCompatible_color1 pairGraph_undirected pairGraph_noSelfLoop
    (edgeColoringCompatible_colorList twoColors pairGraph_undirected pairGraph_noSelfLoop [2, 1])

def cycleAssignment : Assignment :=
  SparseMap.add 1 1 (SparseMap.add 2 2 (SparseMap.add 3 1 (SparseMap.add 4 2 .nil)))

theorem fourCycle_produced_empty : color twoColors fourCycle = .nil := by
  rw [color, show KeySet.cardinal twoColors = 2 from rfl, fourCycle_stops, colorList_nil]

theorem cycleAssignment_entries :
    SparseMap.elements cycleAssignment = [(4, 2), (2, 2), (1, 1), (3, 1)] := by decide

theorem cycleAssignment_total : SparseMap.keys cycleAssignment = SparseMap.keys fourCycle := by decide

theorem cycleAssignment_palette : PaletteValued twoColors cycleAssignment := by
  intro node value found
  simp only [cycleAssignment, SparseMap.find_add, SparseMap.find_nil] at found
  split_ifs at found <;> cases found <;> decide

theorem cycleAssignment_compatible : EdgeColoringCompatible twoColors fourCycle cycleAssignment := by
  intro left right edge
  refine ⟨fun value found => cycleAssignment_palette left value found, ?_⟩
  intro first second foundLeft foundRight
  have edges := (adjacent_mkGraph [(1, 2), (2, 3), (3, 4), (4, 1)] left right).mp edge
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at edges
  rcases edges with forward | reverse
  · rcases forward with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases Option.some.inj foundLeft <;> cases Option.some.inj foundRight <;> decide
  · rcases reverse with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases Option.some.inj foundLeft <;> cases Option.some.inj foundRight <;> decide

theorem edgeless_total (palette : NodeSet) (positive : 0 < KeySet.cardinal palette) (g : Graph)
    (edgeless : ∀ node, neighbors g node = ∅) :
    EdgeColoringCompatible palette g (color palette g) ∧ PaletteValued palette (color palette g) ∧
      SparseMap.keys (color palette g) = SparseMap.keys g := by
  apply total_coloring_of_progress palette (fun current => ∀ node, neighbors current node = ∅)
    (g := g) (valid := edgeless)
  · intro current node empty _ query
    rw [neighbors_removeNode, empty]
    split_ifs <;> simp
  · intro current empty nonempty
    obtain ⟨node, present⟩ := nonempty
    obtain ⟨value, found⟩ := (SparseMap.mem_keys node current).mp present
    refine ⟨node, (mem_eligible (KeySet.cardinal palette) current node).mpr ⟨value, found, ?_⟩⟩
    have zero : KeySet.cardinal value = 0 := by
      have cards := congrArg Finset.card (empty node)
      simpa only [neighbors_card, adj_of_find_some found, Finset.card_empty] using cards
    rwa [zero]
  · intro left right edge
    have impossible := (mem_neighbors g left right).mpr edge
    simp [edgeless] at impossible
  · intro node edge
    have impossible := (mem_neighbors g node node).mpr edge
    simp [edgeless] at impossible

end Examples.ColoringCorrectness
