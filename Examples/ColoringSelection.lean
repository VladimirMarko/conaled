import Applications.Graphs.Coloring.Selection
import Applications.Graphs.Coloring.Construction
import Examples.PositiveFiniteTries

/-!
# Graph construction and selection cases

The source palette and graph are literal source inputs. Expected domain,
selection, residual cardinalities and candidate lists were derived before
implementation. Boundary cases retain raw padding and stored empty vertices.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ColoringSelection

open Search.PositiveTrie Graphs.Coloring

def palette : NodeSet := ([1, 2, 3] : List Node).foldr KeySet.add .nil

def sourceEdges : List (Node × Node) :=
  [(5, 6), (6, 2), (5, 2), (1, 5), (1, 2), (2, 4), (1, 4)]

def sourceGraph : Graph := mkGraph sourceEdges

theorem palette_cardinal : KeySet.cardinal palette = 3 := rfl

theorem sourceGraph_undirected : Undirected sourceGraph := undirected_mkGraph sourceEdges

theorem sourceGraph_noSelfLoop : NoSelfLoop sourceGraph := by
  apply noSelfLoop_mkGraph sourceEdges
  intro edge member
  simp only [sourceEdges, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sourceGraph_domain : KeySet.elements (nodes sourceGraph) = [4, 2, 6, 1, 5] := by
  decide

theorem sourceGraph_cardinal : SparseMap.cardinal sourceGraph = 5 := rfl

theorem sourceGraph_adjacencies :
    ([1, 2, 4, 5, 6] : List Node).map (fun node => (node, KeySet.elements (adj sourceGraph node))) =
      [(1, [4, 2, 5]), (2, [4, 6, 1, 5]), (4, [2, 1]), (5, [2, 6, 1]), (6, [2, 5])] := by
  decide

theorem sourceGraph_degrees :
    ([1, 2, 4, 5, 6] : List Node).map (fun node => KeySet.cardinal (adj sourceGraph node)) =
      [3, 4, 2, 3, 2] := rfl

theorem sourceGraph_selection : select 3 sourceGraph = [4, 1, 2, 6, 5] := by
  refine (select_cons_iff 3 _ 4 _).mpr ⟨by rfl, ?_⟩
  refine (select_cons_iff 3 _ 1 _).mpr ⟨by rfl, ?_⟩
  refine (select_cons_iff 3 _ 2 _).mpr ⟨by rfl, ?_⟩
  refine (select_cons_iff 3 _ 6 _).mpr ⟨by rfl, ?_⟩
  refine (select_cons_iff 3 _ 5 _).mpr ⟨by rfl, ?_⟩
  exact select_of_none 3 _ (by rfl)

def sourceResidual (count : Nat) : Graph :=
  removeNodes ((select 3 sourceGraph).take count) sourceGraph

theorem sourceResidual_cards :
    (List.range 6).map (fun count => SparseMap.cardinal (sourceResidual count)) =
      [5, 4, 3, 2, 1, 0] := by
  simp only [sourceResidual, sourceGraph_selection]
  decide

theorem sourceResidual_candidates :
    (List.range 6).map (fun count => KeySet.elements (eligible 3 (sourceResidual count))) =
      [[4, 6], [6, 1], [2, 6, 5], [6, 5], [5], []] := by
  simp only [sourceResidual, sourceGraph_selection]
  decide

theorem sourceResidual_choices :
    (List.range 6).map (fun count => KeySet.choose (eligible 3 (sourceResidual count))) =
      [some 4, some 1, some 2, some 6, some 5, none] := by
  simp only [sourceResidual, sourceGraph_selection]
  decide

theorem sourceResidual_card (count : Nat) (within : count ≤ 5) :
    SparseMap.cardinal (sourceResidual count) = 5 - count := by
  have lengthBound : count ≤ (select 3 sourceGraph).length := by
    simpa only [sourceGraph_selection, List.length_cons, List.length_nil] using within
  simpa only [sourceResidual, sourceGraph_cardinal] using
    cardinal_removeNodes_take 3 sourceGraph count lengthBound

theorem sourceResidual_suffix (count : Nat) :
    select 3 (sourceResidual count) = [4, 1, 2, 6, 5].drop count := by
  simpa only [sourceResidual, sourceGraph_selection] using
    select_removeNodes_take 3 sourceGraph count

theorem sourceResidual_undirected (count : Nat) : Undirected (sourceResidual count) :=
  undirected_removeNodes sourceGraph_undirected _

theorem sourceResidual_noSelfLoop (count : Nat) : NoSelfLoop (sourceResidual count) :=
  noSelfLoop_removeNodes sourceGraph_noSelfLoop _

theorem source_second_current :
    (1 : Node) ∈ SparseMap.keys (sourceResidual 1) ∧
      KeySet.cardinal (adj (sourceResidual 1) 1) < 3 := by
  have selected : select 3 sourceGraph = [4] ++ 1 :: [2, 6, 5] := sourceGraph_selection
  simpa only [sourceResidual, sourceGraph_selection, List.take] using
    current_vertex 3 sourceGraph [4] [2, 6, 5] 1 selected

theorem source_second_later_neighbors :
    (neighbors sourceGraph 1 ∩ ([2, 6, 5] : List Node).toFinset).card < 3 :=
  later_neighbors_card_lt 3 sourceGraph [4] [2, 6, 5] 1 sourceGraph_selection

/-- A later choice need not have low degree in the original graph. -/
theorem source_second_original_degree : KeySet.cardinal (adj sourceGraph 1) = 3 := rfl

theorem source_second_choice_not_minimum :
    KeySet.choose (eligible 3 (sourceResidual 1)) ≠
      (KeySet.elements (eligible 3 (sourceResidual 1))).head? := by
  simp only [sourceResidual, sourceGraph_selection]
  decide

theorem empty_selection (bound : Nat) : select bound .nil = [] :=
  select_of_none bound .nil rfl

def isolated : Graph := SparseMap.add 1 .nil .nil

theorem isolated_stored : SparseMap.find 1 isolated = some .nil ∧
    KeySet.mem 1 (nodes isolated) = true ∧ SparseMap.cardinal isolated = 1 := by
  exact ⟨rfl, (mem_nodes isolated 1).mpr ⟨.nil, rfl⟩, rfl⟩

theorem isolated_same_default : adj isolated 1 = adj (.nil : Graph) 1 := rfl

theorem isolated_distinct_observation : observe isolated ≠ observe (.nil : Graph) := by
  intro same
  have keys := congrArg (fun view => view.lookup 1) same
  simp [observe_lookup, isolated] at keys

theorem isolated_selection : select 1 isolated = [1] := by
  refine (select_cons_iff 1 isolated 1 []).mpr ⟨rfl, ?_⟩
  exact select_of_none 1 _ rfl

theorem zero_bound_source : select 0 sourceGraph = [] := select_zero sourceGraph

theorem threshold_not_eligible : lowDegree 3 1 (adj sourceGraph 1) = false := rfl

def paddedIsolated : Graph := SparseMap.add 1 PositiveFiniteTries.paddedEmpty .nil

theorem paddedIsolated_observation : observe paddedIsolated = observe isolated := by
  apply Finmap.ext_lookup
  intro node
  by_cases same : node = 1 <;>
    simp [observe_lookup, paddedIsolated, isolated, SparseMap.find_add, same,
      PositiveFiniteTries.paddedEmpty_same_observation]

def rawShapePredicate (_node : Node) (value : NodeSet) : Bool := decide (0 < value.numNodes)

theorem rawShape_distinguishes :
    KeySet.mem 1 (subsetNodes rawShapePredicate paddedIsolated) = true ∧
      KeySet.mem 1 (subsetNodes rawShapePredicate isolated) = false := by
  exact ⟨rfl, rfl⟩

theorem lowDegree_ignores_padding :
    KeySet.observe (eligible 1 paddedIsolated) = KeySet.observe (eligible 1 isolated) :=
  eligible_observe_congr 1 paddedIsolated_observation

theorem paddedIsolated_selection : select 1 paddedIsolated = [1] := by
  rw [select_observe_congr 1 paddedIsolated_observation, isolated_selection]

def paddedEmptyGraph : Graph := .node none (.node none .nil .nil) .nil

theorem paddedEmptyGraph_counts :
    paddedEmptyGraph.numNodes = 2 ∧ SparseMap.cardinal paddedEmptyGraph = 0 ∧
      KeySet.elements (nodes paddedEmptyGraph) = [] := by
  exact ⟨rfl, rfl, rfl⟩

def dangling : Graph := SparseMap.add 1 (KeySet.add 2 .nil) .nil

theorem dangling_absent_removal :
    SparseMap.find 2 dangling = none ∧ SparseMap.cardinal (removeNode 2 dangling) = 1 ∧
      KeySet.elements (adj dangling 1) = [2] ∧
      KeySet.elements (adj (removeNode 2 dangling) 1) = [] := by
  refine ⟨rfl, ?_, by decide, by decide⟩
  rw [cardinal_removeNode_of_none 2 dangling rfl]
  rfl

theorem dangling_changed_by_absent_removal :
    observe (removeNode 2 dangling) ≠ observe dangling := by
  intro same
  have sameNeighbors := neighbors_congr same 1
  have member : (2 : Node) ∈ neighbors dangling 1 := (mem_neighbors dangling 1 2).mpr rfl
  rw [← sameNeighbors, mem_neighbors, adjacent_removeNode] at member
  exact member.2.1 rfl

def directed : Graph := SparseMap.add 2 .nil dangling

theorem directed_selection : select 1 directed = [2, 1] := by
  refine (select_cons_iff 1 directed 2 [1]).mpr ⟨rfl, ?_⟩
  refine (select_cons_iff 1 _ 1 []).mpr ⟨rfl, ?_⟩
  exact select_of_none 1 _ rfl

theorem directed_not_undirected : ¬ Undirected directed := by
  intro symmetric
  have impossible := symmetric 1 2 rfl
  cases impossible

def selfLoop : Graph := mkGraph [(1, 1)]

theorem selfLoop_present : Adjacent selfLoop 1 1 := adjacent_addEdge_self .nil 1

theorem selfLoop_not_loopless : ¬ NoSelfLoop selfLoop := fun loopless => loopless 1 selfLoop_present

theorem selfLoop_selection : select 2 selfLoop = [1] := by
  refine (select_cons_iff 2 selfLoop 1 []).mpr ⟨rfl, ?_⟩
  exact select_of_none 2 _ rfl

def fourCycle : Graph := mkGraph [(1, 2), (2, 3), (3, 4), (4, 1)]

theorem fourCycle_nonempty : KeySet.elements (nodes fourCycle) = [4, 2, 1, 3] := by decide

theorem fourCycle_degrees :
    ([1, 2, 3, 4] : List Node).map (fun node => KeySet.cardinal (adj fourCycle node)) =
      [2, 2, 2, 2] := rfl

theorem fourCycle_stops : select 2 fourCycle = [] := select_of_none 2 fourCycle rfl

theorem fourCycle_terminal : removeNodes (select 2 fourCycle) fourCycle = fourCycle := by
  rw [fourCycle_stops, removeNodes_nil]

theorem repeated_edge_observation :
    observe (mkGraph [(1, 2), (1, 2)]) = observe (mkGraph [(1, 2)]) :=
  observe_addEdge_duplicate (1, 2) .nil

theorem reversed_edge_observation :
    observe (mkGraph [(1, 2)]) = observe (mkGraph [(2, 1)]) :=
  observe_addEdge_reverse 1 2 .nil

theorem repeated_absent_removal_domain :
    SparseMap.keys (removeNodes [4, 4, 7] sourceGraph) =
      SparseMap.keys sourceGraph \ ([4, 4, 7] : List Node).toFinset :=
  keys_removeNodes [4, 4, 7] sourceGraph

theorem repeated_absent_removal_adjacency (left right : Node) :
    Adjacent (removeNodes [4, 4, 7] sourceGraph) left right ↔
      left ∉ ([4, 4, 7] : List Node) ∧ right ∉ ([4, 4, 7] : List Node) ∧
        Adjacent sourceGraph left right :=
  adjacent_removeNodes [4, 4, 7] sourceGraph left right

/-- A concrete removal-closed class instantiates the conditional coverage theorem. -/
theorem edgeless_selection_covers (bound : Nat) (positive : 0 < bound) (g : Graph)
    (edgeless : ∀ node, neighbors g node = ∅) :
    (select bound g).toFinset = SparseMap.keys g := by
  apply select_covers_of_progress bound (fun current => ∀ node, neighbors current node = ∅)
    (g := g) (valid := edgeless)
  · intro current node empty _ query
    rw [neighbors_removeNode, empty]
    split_ifs <;> simp
  · intro current empty nonempty
    obtain ⟨node, present⟩ := nonempty
    obtain ⟨value, found⟩ := (SparseMap.mem_keys node current).mp present
    refine ⟨node, (mem_eligible bound current node).mpr ⟨value, found, ?_⟩⟩
    have zero : KeySet.cardinal value = 0 := by
      have cards := congrArg Finset.card (empty node)
      simpa only [neighbors_card, adj_of_find_some found, Finset.card_empty] using cards
    rwa [zero]

end Examples.ColoringSelection
