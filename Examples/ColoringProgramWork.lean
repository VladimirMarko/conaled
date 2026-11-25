import Applications.Resources.Coloring.Construction
import Applications.Resources.Coloring.Bounds
import Applications.Resources.Coloring.Export
import Applications.Resources.Growth
import Examples.ColoringResourceHelpers
import Examples.PositiveFiniteTraversalWork

/-!
# Complete-program resource clients for Color

The expected work and event coordinates were derived before these clients were
executed. Exact reductions are paired with the generic erasure, invariant and
resource laws they exercise. Construction remains separate from supplied-input
coloring and from exports.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ColoringProgramWork

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring Resources Resources.Coloring
open Examples.ColoringSelection
open Examples.ColoringCorrectness
open Numerals.PositiveKeys Resources.PositiveTrie

theorem source_construction_value : (mkGraphRun sourceEdges).1 = sourceGraph :=
  mkGraphRun_value sourceEdges

theorem source_construction_valid : GraphValid 3 (mkGraphRun sourceEdges).1 := by
  rw [source_construction_value]
  exact ColoringResourceHelpers.source_valid

theorem source_construction_work : work (mkGraphRun sourceEdges).2 = 194 := rfl

theorem source_construction_bound : work (mkGraphRun sourceEdges).2 ≤ 317 := by
  apply mkGraphRun_work_le 3 (by decide) sourceEdges
  intro edge member
  simp only [sourceEdges, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem source_construction_operations :
    count .addEdge (mkGraphRun sourceEdges).2 = 7 ∧
    count .edgeRead (mkGraphRun sourceEdges).2 = 14 ∧
    count .edgeSetInsert (mkGraphRun sourceEdges).2 = 14 ∧
    count .edgeMapWrite (mkGraphRun sourceEdges).2 = 14 ∧
    count .listEntry (mkGraphRun sourceEdges).2 = 8 ∧
    count .listCallback (mkGraphRun sourceEdges).2 = 7 := by
  simp [mkGraphRun_count, edgeCount, sourceEdges]

theorem source_old_reads_found : count .adjFound (mkGraphRun sourceEdges).2 = 9 := rfl

theorem old_read_contract (edge : Node × Node) (g : Graph) :
    count .adjFound (addEdgeRun edge g).2 =
      (if (SparseMap.find edge.1 g).isSome then 1 else 0) +
      (if (SparseMap.find edge.2 g).isSome then 1 else 0) := by
  simpa only [edgeCount, ite_true, Nat.zero_add] using addEdgeRun_count .adjFound edge g

/-- These are observations of each actual right-fold tail, not a new executor. -/
theorem source_old_read_entries :
    sourceEdges.reverse.mapIdx (fun index edge =>
      let g := (mkGraphRun (sourceEdges.drop (sourceEdges.length - index))).1
      (work (lookup edge.1 g).2, work (lookup edge.2 g).2)) =
      [(1, 1), (2, 3), (1, 2), (1, 2), (3, 2), (3, 2), (3, 3)] := by
  decide

theorem source_left_read_entries :
    (sourceEdges.mapIdx (fun index edge =>
      let g := (Resources.run addEdgeRun (sourceEdges.take index) .nil).1
      work (lookup edge.1 g).2 + work (lookup edge.2 g).2)).sum = 28 := by
  decide

theorem source_left_value : (Resources.run addEdgeRun sourceEdges .nil).1 = sourceGraph := by
  decide

theorem self_edge_empty_work : work (mkGraphRun []).2 = 2 := mkGraphRun_work_nil
theorem self_edge_one_work : work (mkGraphRun [(8, 8)]).2 = 41 := rfl
theorem self_edge_two_work : work (mkGraphRun [(8, 8), (8, 8)]).2 = 86 := rfl

def selfEdgeGraph : Graph := mkGraph [(8, 8)]

theorem self_edge_repeat_value (extra : Nat) :
    mkGraph (List.replicate (extra + 1) (8, 8)) = selfEdgeGraph := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [List.replicate_succ, mkGraph_cons, ih]
      rfl

theorem self_edge_repeat_work (extra : Nat) :
    work (mkGraphRun (List.replicate (extra + 1) (8, 8))).2 = 45 * extra + 41 := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [List.replicate_succ, mkGraphRun_work_cons, ih, self_edge_repeat_value]
      change 2 + (45 * extra + 41) + 43 = _
      omega

theorem self_edge_occurrence_work (occurrences : Nat) (positive : 1 ≤ occurrences) :
    work (mkGraphRun (List.replicate occurrences (8, 8))).2 + 4 = 45 * occurrences := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : occurrences ≠ 0)
  rw [self_edge_repeat_work]
  omega

theorem source_palette_value : (paletteRun [1, 2, 3]).1 = palette := paletteRun_value _
theorem source_palette_work : work (paletteRun [1, 2, 3]).2 = 18 := by
  rw [paletteRun_work]
  rfl
theorem empty_palette_setup : work (paletteRun []).2 = 2 := rfl
theorem duplicate_palette_setup : work (paletteRun [1, 1]).2 = 10 := by
  rw [paletteRun_work]
  rfl

theorem source_selection_value : (selectRun unitPrices 3 sourceGraph).1 = [4, 1, 2, 6, 5] := by
  rw [selectRun_value, sourceGraph_selection]

theorem source_stage_work :
    (residuals (select 3 sourceGraph) sourceGraph).map
      (fun current => work (selectionStageCost unitPrices 3 current)) = [231, 164, 158, 120, 53, 5] := by
  rw [sourceGraph_selection]
  decide

theorem source_selection_work : work (selectRun unitPrices 3 sourceGraph).2 = 731 := by
  change workHom (selectRun unitPrices 3 sourceGraph).2 = 731
  rw [selectRun_projection_trajectory, sourceGraph_selection]
  decide

theorem source_selection_arithmetic : (selectRun unitPrices 3 sourceGraph).2.1.2 = 101 := by
  change arithmeticHom (selectRun unitPrices 3 sourceGraph).2 = 101
  rw [selectRun_projection_trajectory, sourceGraph_selection]
  decide

theorem source_selection_count (event : Event) :
    count event (selectRun unitPrices 3 sourceGraph).2 = selectionCount event 5 5 10 := by
  have inserted : candidateVisits 3 sourceGraph = 10 := by
    rw [candidateVisits, sourceGraph_selection]
    decide
  rw [selectRun_count, sourceGraph_cardinal, sourceGraph_selection, inserted]
  rfl

theorem source_selection_counts :
    ([.select, .eligible, .subset, .candidateChoice, .predicate, .degreeCardinality, .comparison,
      .candidateInsert, .mapErase, .valueMap, .adjErase] : List Event).map
      (fun event => count event (selectRun unitPrices 3 sourceGraph).2) =
      [6, 6, 6, 6, 15, 15, 15, 10, 5, 5, 10] := by
  simp only [List.map_cons, List.map_nil, source_selection_count]
  decide

theorem source_scan_balance : scanVisits 5 5 + triangle 5 = 30 ∧
    eraseVisits 5 5 + triangle 5 = 25 ∧ scanVisits 5 5 = 5 + eraseVisits 5 5 ∧ 2 * triangle 5 = 30 :=
  ⟨scanVisits_add_triangle 5 5 (by decide), eraseVisits_add_triangle 5 5 (by decide),
    scanVisits_eq_add_eraseVisits 5 5 (by decide), twice_triangle 5⟩

theorem source_colorList_work : work (colorListRun palette sourceGraph [4, 1, 2, 6, 5]).2 = 313 := by
  decide

theorem source_paint_callbacks :
    ([4, 1, 2, 6, 5] : List Node).mapIdx (fun index key =>
      work (color1Run palette sourceGraph key
        (colorList palette sourceGraph ([4, 1, 2, 6, 5].drop (index + 1)))).2) =
      [51, 69, 83, 55, 43] := by
  decide

theorem source_color_counts :
    ([.colorStep, .colorsOf, .difference, .colorChoice, .listEntry, .listCallback,
      .neighborLookup, .neighborSuccess, .neighborInsert, .assignmentWrite] : List Event).map
      (fun event => count event (colorListRun palette sourceGraph [4, 1, 2, 6, 5]).2) =
      [5, 5, 5, 5, 6, 5, 14, 7, 7, 5] := by
  simp only [List.map_cons, List.map_nil, colorListRun_count]
  decide

theorem source_selected_writes : count .assignmentWrite (colorRun unitPrices palette sourceGraph).2 = 5 := by
  rw [colorRun_writes, palette_cardinal, sourceGraph_selection]
  rfl

theorem source_program_work : work (colorRun unitPrices palette sourceGraph).2 = 1058 := by
  rw [colorRun_work, palette_cardinal, source_selection_work, sourceGraph_selection, source_colorList_work]
  rfl

theorem source_program_arithmetic : (colorRun unitPrices palette sourceGraph).2.1.2 = 107 := by
  simp only [colorRun, enter, Resources.bind, Resources.Coloring.observe, cardinality_value, selectRun_value,
    palette_cardinal, sourceGraph_selection, Prod.fst_add, Prod.snd_add]
  rw [source_selection_arithmetic]
  rfl

theorem source_program_structural : (colorRun unitPrices palette sourceGraph).2.1.1 = 951 := by
  have total := source_program_work
  have arithmeticWork := source_program_arithmetic
  unfold work at total
  omega

theorem source_program_entries : SparseMap.elements (colorRun unitPrices palette sourceGraph).1 =
    [(4, 1), (2, 3), (6, 2), (1, 2), (5, 1)] := by
  rw [colorRun_value]
  exact ColoringCorrectness.source_entries

theorem source_program_semantics :
    EdgeColoringCompatible palette sourceGraph (colorRun unitPrices palette sourceGraph).1 ∧
      PaletteValued palette (colorRun unitPrices palette sourceGraph).1 ∧
      SparseMap.keys (colorRun unitPrices palette sourceGraph).1 = SparseMap.keys sourceGraph := by
  rw [colorRun_value]
  exact ⟨ColoringCorrectness.source_compatible, ColoringCorrectness.source_paletteValued,
    ColoringCorrectness.source_keys⟩

theorem source_program_client_lookup (node : {key // key ∈ SparseMap.keys (color palette sourceGraph)}) :
    SparseMap.find node.val (colorRun unitPrices palette sourceGraph).1 = some (sourceClient node).val := by
  rw [colorRun_value]
  exact producedColoring_lookup palette sourceGraph sourceGraph_undirected sourceGraph_noSelfLoop node

theorem source_polynomial : colorPolynomial 5 14 3 2 3 = 547 := rfl

theorem source_program_bound : work (colorRun unitPrices palette sourceGraph).2 ≤ 35008 := by
  have h := colorRun_work_le ColoringResourceHelpers.source_valid ColoringResourceHelpers.palette_valid
    (by decide) (by decide)
  norm_num only [sourceGraph_cardinal, ColoringResourceHelpers.source_mass, palette_cardinal,
    source_polynomial] at h
  exact h

theorem source_residual_degree_mass :
    (residuals (select 3 sourceGraph) sourceGraph).map degreeMass = [14, 10, 6, 2, 0, 0] := by
  rw [sourceGraph_selection]
  simp only [residuals, List.map_cons, List.map_nil, degreeMass_entries]
  decide

theorem source_paint_order : (select 3 sourceGraph).reverse = [5, 6, 2, 1, 4] := by
  rw [sourceGraph_selection]
  rfl

def sourceFrames : List (Node × Assignment) :=
  (([4, 1, 2, 6, 5] : List Node).mapIdx (fun index key =>
    (key, (colorListRun palette sourceGraph ([4, 1, 2, 6, 5].drop (index + 1))).1))).reverse

theorem source_neighbor_ledger :
    sourceFrames.map (fun frame =>
      let neighbors := KeySet.elements (adj sourceGraph frame.1)
      (frame.1, neighbors, neighbors.filterMap (fun key => SparseMap.find key frame.2),
        KeySet.choose (availableColors palette sourceGraph frame.1 frame.2),
        (neighbors.map (fun key => work (lookup key frame.2).2)).sum,
        work (color1Run palette sourceGraph frame.1 frame.2).2)) =
      [(5, [2, 6, 1], [], some 1, 3, 43), (6, [2, 5], [1], some 2, 5, 55),
       (2, [4, 6, 1, 5], [2, 1], some 3, 10, 83), (1, [4, 2, 5], [3, 1], some 2, 8, 69),
       (4, [2, 1], [3, 2], some 1, 3, 51)] := by
  rfl

theorem source_paint_runner : work (colorListRun palette sourceGraph [4, 1, 2, 6, 5]).2 =
    12 + work (Resources.run (color1Run palette sourceGraph) [5, 6, 2, 1, 4] .nil).2 := by
  rw [colorListRun, enter_work, listFold_cost]
  simp only [work_add, work_structural, work_mark, Nat.add_zero]
  rfl

theorem nil_programs : (colorRun unitPrices .nil .nil).1 = .nil ∧
    work (colorRun unitPrices .nil .nil).2 = 9 ∧ work (colorRun unitPrices palette .nil).2 = 21 := by
  refine ⟨by rw [colorRun_value, color_empty_graph], ?_, ?_⟩ <;> rw [colorRun_nil_work] <;> rfl

theorem isolated_selection_work : work (selectRun unitPrices 1 isolated).2 = 25 := by
  rw [selectRun_work_some unitPrices 1 isolated 1 rfl,
    show removeNode 1 isolated = .nil from rfl, selectRun_nil_work]
  rfl

theorem isolated_program_work : work (colorRun unitPrices oneColor isolated).2 = 45 := by
  rw [colorRun_work, show KeySet.cardinal oneColor = 1 from rfl,
    isolated_selection_work, isolated_selection]
  rfl

theorem isolated_program_binding : SparseMap.elements (colorRun unitPrices oneColor isolated).1 = [(1, 1)] := by
  rw [colorRun_value]
  exact isolated_entries

theorem zero_threshold_count (event : Event) (prices : Prices) (g : Graph) :
    count event (selectRun prices 0 g).2 = selectionCount event (SparseMap.cardinal g) 0 0 := by
  have chosen := (select_nil_iff 0 g).mp (select_zero g)
  rw [selectRun_count, select_zero, candidateVisits_none 0 g chosen]
  rfl

theorem empty_palette_program_work : work (colorRun unitPrices .nil sourceGraph).2 = 159 := by
  rw [colorRun_work, show KeySet.cardinal (.nil : NodeSet) = 0 from rfl,
    selectRun_work_none unitPrices 0 sourceGraph rfl, select_zero, colorListRun_work_nil]
  rfl

theorem stalled_program_work : work (colorRun unitPrices twoColors fourCycle).2 = 103 := by
  rw [colorRun_work, show KeySet.cardinal twoColors = 2 from rfl,
    selectRun_work_none unitPrices 2 fourCycle rfl, fourCycle_stops, colorListRun_work_nil]
  rfl

theorem stalled_counts : count .predicate (selectRun unitPrices 2 fourCycle).2 = 4 ∧
    count .candidateChoice (selectRun unitPrices 2 fourCycle).2 = 1 ∧
    count .mapErase (selectRun unitPrices 2 fourCycle).2 = 0 ∧ SparseMap.cardinal fourCycle = 4 := by
  simp only [selectRun_count, fourCycle_stops, selectionCount, List.length_nil, scanVisits_zero]
  decide

def danglingEight : Graph := SparseMap.add 1 (KeySet.add 8 .nil) .nil

theorem dangling_eight_valid : GraphValid 4 danglingEight :=
  (GraphValid.nil 4).add 1 _ (by decide) ((SetValid.nil 4).add 8 (by decide))

theorem dangling_eight_not_small : ¬ GraphValid 1 danglingEight := by
  intro valid
  have bound := (valid.payload 1 (KeySet.add 8 .nil) rfl).bounded 8 rfl
  change 4 ≤ 1 at bound
  omega

theorem dangling_eight_selection : select 2 danglingEight = [1] := by
  rw [select_of_some 2 danglingEight (node := 1) rfl, select_of_none 2 (removeNode 1 danglingEight) rfl]

theorem dangling_eight_program_work : work (colorRun unitPrices twoColors danglingEight).2 = 87 := by
  rw [colorRun_work, show KeySet.cardinal twoColors = 2 from rfl,
    selectRun_work_some unitPrices 2 danglingEight 1 rfl,
    show removeNode 1 danglingEight = .nil from rfl, selectRun_nil_work, dangling_eight_selection]
  rfl

theorem dangling_eight_lookup : KeySet.elements (adj danglingEight 1) = [8] ∧
    count .neighborLookup (color1Run twoColors danglingEight 1 .nil).2 = 1 ∧
    count .neighborSuccess (color1Run twoColors danglingEight 1 .nil).2 = 0 := by
  refine ⟨by decide, ?_, ?_⟩ <;>
    simp only [color1Run_count, availableColorsRun_count, adjRun_count, colorsOfRun_count] <;> decide

theorem absent_removal_changes_degree : degreeMass dangling = 1 ∧
    degreeMass (removeNodeRun 2 dangling).1 = 0 ∧
    SparseMap.cardinal (removeNodeRun 2 dangling).1 = SparseMap.cardinal dangling := by
  simp only [removeNodeRun_value, degreeMass_entries]
  decide

theorem repeated_absent_removal_attempts :
    count .adjErase (removeNodeRun 2 dangling).2 = 1 ∧
    count .adjErase (removeNodeRun 2 (removeNodeRun 2 dangling).1).2 = 1 := by
  simp only [removeNodeRun_count, removeNodeRun_value]
  decide

theorem failed_measured_step : (color1Run oneColor directed 1 blockedColoring).1 = blockedColoring ∧
    count .assignmentWrite (color1Run oneColor directed 1 blockedColoring).2 = 0 ∧
    work (color1Run oneColor directed 1 blockedColoring).2 = 27 := by
  refine ⟨by rw [color1Run_value]; exact failed_step_preserves, ?_, ?_⟩
  · rw [color1Run_writes]; rfl
  · rw [color1Run_work]; rfl

theorem generic_write_bound_strict : count .assignmentWrite (colorListRun .nil isolated [1]).2 ≤ 1 ∧
    count .assignmentWrite (colorListRun .nil isolated [1]).2 < 1 := by
  refine ⟨colorListRun_writes_le .nil isolated [1], ?_⟩
  rw [colorListRun_count]
  decide

theorem repeated_color_attempts :
    count .neighborLookup (colorsOfRun collisionColoring collisionNeighbors).2 = 3 ∧
    count .neighborSuccess (colorsOfRun collisionColoring collisionNeighbors).2 = 2 ∧
    count .neighborInsert (colorsOfRun collisionColoring collisionNeighbors).2 = 2 ∧
    KeySet.cardinal (colorsOfRun collisionColoring collisionNeighbors).1 = 1 ∧
    work (colorsOfRun collisionColoring collisionNeighbors).2 = 40 := by
  simp only [colorsOfRun_count, colorsOfRun_value, colorsOfRun_work]
  decide

theorem directed_semantic_boundary : ¬ EdgeColoringCompatible oneColor directed (colorRun unitPrices oneColor directed).1 := by
  rw [colorRun_value]
  exact directed_incompatible

theorem self_loop_semantic_boundary : ¬ EdgeColoringCompatible twoColors selfLoop (colorRun unitPrices twoColors selfLoop).1 := by
  rw [colorRun_value]
  exact selfLoop_incompatible

theorem operand_cross_addition :
    work (lowDegreeRun ColoringResourceHelpers.operandPrices 3 1 (KeySet.add 1 (KeySet.add 2 .nil))).2 + 5 =
      work (lowDegreeRun unitPrices 3 1 (KeySet.add 1 (KeySet.add 2 .nil))).2 + 14 := by
  rw [ColoringResourceHelpers.operand_sensitive.2.1, ColoringResourceHelpers.operand_sensitive.2.2]

theorem source_repriced_work :
    work (colorRun ColoringResourceHelpers.operandPrices palette sourceGraph).2 + 107 =
      1058 + arithmeticTariff ColoringResourceHelpers.operandPrices palette sourceGraph := by
  have h := colorRun_reprice ColoringResourceHelpers.operandPrices unitPrices palette sourceGraph
  rw [← colorRun_arithmetic unitPrices palette sourceGraph, source_program_work] at h
  rw [show arithmeticHom (colorRun unitPrices palette sourceGraph).2 = 107
    from source_program_arithmetic] at h
  exact h

theorem source_repriced_bound :
    work (colorRun ColoringResourceHelpers.operandPrices palette sourceGraph).2 ≤
      35008 + arithmeticTariff ColoringResourceHelpers.operandPrices palette sourceGraph := by
  have h := colorRun_repriced_work_le ColoringResourceHelpers.source_valid
    ColoringResourceHelpers.palette_valid (by decide) (by decide) ColoringResourceHelpers.operandPrices
  norm_num only [sourceGraph_cardinal, ColoringResourceHelpers.source_mass, palette_cardinal,
    source_polynomial] at h
  exact h

/-- Change only the absent payload type of the accepted raw padding family. -/
def paddedGraph (height : Nat) : Graph :=
  SparseMap.map (fun _ : Nat => (.nil : NodeSet)) (PositiveFiniteTraversalWork.mapPadding height)

theorem paddedGraph_cardinal (height : Nat) : SparseMap.cardinal (paddedGraph height) = 0 := by
  rw [paddedGraph, SparseMap.cardinal_map, PositiveFiniteTraversalWork.mapPadding_cardinal]

theorem paddedGraph_nodes (height : Nat) : (paddedGraph height).numNodes = height := by
  rw [paddedGraph, SparseMap.map, Trees.numNodes_map, PositiveFiniteTraversalWork.mapPadding_nodes]

theorem paddedGraph_normalized_iff (height : Nat) :
    SparseMap.Normalized (paddedGraph height) ↔ height = 0 :=
  (Search.PositiveTrie.normalized_map_iff Option.isSome Option.isSome
    (Option.map (fun _ : Nat => (.nil : NodeSet))) (fun value => by cases value <;> rfl)
    (PositiveFiniteTraversalWork.mapPadding height)).trans
      (PositiveFiniteTraversalWork.mapPadding_normalized_iff height)

theorem paddedGraph_prefixMass (height : Nat) :
    2 * Traversal.prefixMass (paddedGraph height) .one = height * (height + 1) := by
  rw [paddedGraph, SparseMap.map, Traversal.prefixMass_map]
  exact PositiveFiniteTraversalWork.mapPadding_prefixMass height

theorem paddedGraph_elements (height : Nat) : SparseMap.elements (paddedGraph height) = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [SparseMap.elements_length, paddedGraph_cardinal]

theorem paddedGraph_degreeMass (height : Nat) : degreeMass (paddedGraph height) = 0 := by
  rw [degreeMass_entries, paddedGraph_elements]
  rfl

theorem paddedGraph_eligible (height bound : Nat) : eligible bound (paddedGraph height) = .nil := by
  rw [eligible, subsetNodes, SparseMap.fold_eq, paddedGraph_elements]
  rfl

theorem paddedGraph_selection (height bound : Nat) : select bound (paddedGraph height) = [] :=
  select_of_none bound (paddedGraph height) (by rw [paddedGraph_eligible]; rfl)

theorem paddedGraph_scan_work (prices : Prices) (height bound : Nat) :
    work (eligibleRun prices bound (paddedGraph height)).2 =
      4 * Traversal.prefixMass (paddedGraph height) .one + 3 := by
  change structuralHom (eligibleRun prices bound (paddedGraph height)).2 +
    arithmeticHom (eligibleRun prices bound (paddedGraph height)).2 = _
  rw [eligibleRun_structural, eligibleRun_arithmetic, scanTariff,
    paddedGraph_cardinal, paddedGraph_elements]
  simp only [List.map_nil, List.sum_nil, Nat.add_zero]

theorem paddedGraph_select_work (prices : Prices) (height bound : Nat) :
    work (selectRun prices bound (paddedGraph height)).2 =
      4 * Traversal.prefixMass (paddedGraph height) .one + 5 := by
  rw [selectRun_work_none prices bound (paddedGraph height)
    (by rw [paddedGraph_eligible]; rfl), paddedGraph_scan_work, paddedGraph_eligible]
  change 1 + (4 * Traversal.prefixMass (paddedGraph height) .one + 3) + 1 = _
  omega

theorem paddedGraph_no_callbacks (prices : Prices) (height bound : Nat) :
    count .predicate (eligibleRun prices bound (paddedGraph height)).2 = 0 ∧
      count .candidateInsert (eligibleRun prices bound (paddedGraph height)).2 = 0 := by
  simp only [eligibleRun_count, scanCount, paddedGraph_cardinal, paddedGraph_eligible]
  decide

theorem paddedGraph_color_value (prices : Prices) (palette : NodeSet) (height : Nat) :
    (colorRun prices palette (paddedGraph height)).1 = .nil := by
  rw [colorRun_value, color, paddedGraph_selection]
  rfl

theorem paddedGraph_color_work (height : Nat) :
    work (colorRun unitPrices .nil (paddedGraph height)).2 = 2 * height * (height + 1) + 9 := by
  rw [colorRun_work, paddedGraph_select_work, paddedGraph_selection, colorListRun_work_nil]
  change 1 + 1 + (4 * Traversal.prefixMass (paddedGraph height) .one + 5) + 2 = _
  have mass := paddedGraph_prefixMass height
  nlinarith

theorem paddedGraph_size_bound_fails :
    work (colorRun unitPrices .nil (paddedGraph 5)).2 = 69 ∧
      64 * colorPolynomial (SparseMap.cardinal (paddedGraph 5)) (degreeMass (paddedGraph 5)) 1 1 0 <
        work (colorRun unitPrices .nil (paddedGraph 5)).2 ∧ ¬ GraphValid 1 (paddedGraph 5) := by
  rw [paddedGraph_color_work, paddedGraph_cardinal, paddedGraph_degreeMass]
  refine ⟨rfl, by decide, ?_⟩
  intro valid
  have impossible := (paddedGraph_normalized_iff 5).mp valid.normal
  omega

/-- The varying parameter is positive-key height; graph and palette cardinalities stay one. -/
def isolatedLong (height : Nat) : Graph := SparseMap.add (longKey height) (.nil : NodeSet) .nil

theorem isolatedLong_valid (height : Nat) : GraphValid (height + 1) (isolatedLong height) :=
  (GraphValid.nil (height + 1)).add (longKey height) .nil
    (longKey_bitLength height).le (SetValid.nil (height + 1))

theorem isolatedLong_cardinal (height : Nat) : SparseMap.cardinal (isolatedLong height) = 1 := by
  rw [← SparseMap.keys_card, isolatedLong, SparseMap.keys_add]
  change (Insert.insert (longKey height) (∅ : Finset Node)).card = 1
  simp

theorem isolatedLong_adj (height : Nat) (key : Node) : adj (isolatedLong height) key = .nil := by
  by_cases same : key = longKey height <;>
    simp [adj, isolatedLong, SparseMap.find_add, same]

theorem isolatedLong_degreeMass (height : Nat) : degreeMass (isolatedLong height) = 0 := by
  simp [degreeMass, degree, isolatedLong_adj, KeySet.cardinal]

theorem isolatedLong_palette_valid : SetValid 1 oneColor := (SetValid.nil 1).add 1 (by decide)

theorem isolatedLong_polynomial (height : Nat) :
    colorPolynomial 1 0 (height + 1) 1 1 = (height + 1) ^ 2 + 4 := by
  unfold colorPolynomial
  ring

theorem isolatedLong_polynomial_le (height : Nat) :
    colorPolynomial 1 0 (height + 1) 1 1 ≤ 5 * (height + 1) ^ 2 := by
  rw [isolatedLong_polynomial]
  have positive : 1 ≤ height + 1 := by omega
  have square : 1 ≤ (height + 1) ^ 2 := by
    simpa only [pow_two, Nat.one_mul] using Nat.mul_le_mul positive positive
  omega

def isolatedLongWork (height : Nat) : Nat := work (colorRun unitPrices oneColor (isolatedLong height)).2

theorem isolatedLong_work_le (height : Nat) : isolatedLongWork height ≤ 320 * (height + 1) ^ 2 := by
  have bill := colorRun_work_le (isolatedLong_valid height) isolatedLong_palette_valid (by omega) (by decide)
  rw [isolatedLong_cardinal, isolatedLong_degreeMass, show KeySet.cardinal oneColor = 1 from rfl] at bill
  calc
    isolatedLongWork height ≤ 64 * colorPolynomial 1 0 (height + 1) 1 1 := bill
    _ ≤ 64 * (5 * (height + 1) ^ 2) := Nat.mul_le_mul_left 64 (isolatedLong_polynomial_le height)
    _ = 320 * (height + 1) ^ 2 := by ring

theorem isolatedLong_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun height => (isolatedLongWork height : ℝ))
      (fun height => (((height + 1) ^ 2 : Nat) : ℝ)) :=
  Resources.isBigO_of_nat_bound isolatedLongWork (fun height => (height + 1) ^ 2) 320 0
    (fun height _ => isolatedLong_work_le height)

def decodedPrice (_key : Node) (value : Nat) : Nat := value + 1

theorem source_domain_export_work : work (domainExportRun decodedPrice sourceGraph).2 = 176 := by
  rw [domainExportRun_work, ColoringResourceHelpers.nodes_work, enumerateSet_work, decodeKeysRun_work]
  rfl

theorem source_assignment_export_work :
    work (assignmentExportRun decodedPrice (color palette sourceGraph)).2 = 137 := by
  rw [assignmentExportRun_work, enumerateMap_work, decodePairsRun_work, color, palette_cardinal, sourceGraph_selection]
  rfl

theorem source_export_components :
    work (enumerateSet (nodes sourceGraph)).2 = 49 ∧
    work (decodeKeysRun decodedPrice (KeySet.elements (nodes sourceGraph))).2 = 39 ∧
    work (enumerateMap (color palette sourceGraph)).2 = 78 ∧
    work (decodePairsRun decodedPrice (SparseMap.elements (color palette sourceGraph))).2 = 58 := by
  rw [color, palette_cardinal, sourceGraph_selection]
  decide

theorem source_pipeline_work : work (pipelineRun unitPrices decodedPrice sourceEdges [1, 2, 3]).2 = 1584 := by
  rw [pipelineRun_work]
  change 1 + work (mkGraphRun sourceEdges).2 + work (paletteRun [1, 2, 3]).2 +
    work (colorRun unitPrices palette sourceGraph).2 + work (domainExportRun decodedPrice sourceGraph).2 +
    work (assignmentExportRun decodedPrice (color palette sourceGraph)).2 = _
  rw [source_construction_work, source_palette_work, source_program_work,
    source_domain_export_work, source_assignment_export_work]

theorem source_pipeline_value : (pipelineRun unitPrices decodedPrice sourceEdges [1, 2, 3]).1 =
    ([4, 2, 6, 1, 5], [(4, 1), (2, 3), (6, 2), (1, 2), (5, 1)]) := by
  rw [pipelineRun_value]
  change ((KeySet.elements (nodes sourceGraph)).map numeric,
    (SparseMap.elements (color palette sourceGraph)).map (fun entry => (numeric entry.1, numeric entry.2))) = _
  rw [sourceGraph_domain, ColoringCorrectness.source_entries]
  rfl

theorem source_pipeline_once : count .mkGraph (pipelineRun unitPrices decodedPrice sourceEdges [1, 2, 3]).2 = 1 ∧
    count .paletteSetup (pipelineRun unitPrices decodedPrice sourceEdges [1, 2, 3]).2 = 1 :=
  pipelineRun_builds_once unitPrices decodedPrice sourceEdges [1, 2, 3]

end Examples.ColoringProgramWork
