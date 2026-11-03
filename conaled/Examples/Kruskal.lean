import Applications.Kruskal.Observation
set_option autoImplicit false
set_option warningAsError true
namespace Examples.KruskalCases
open Kruskal
open Connectivity.ListPartition (findDS lookupDS unionDS startDS Connected)
private theorem pair_connected (a b w : Int) : ConnectedGraph ([a, b], [(a, b, w)]) := by
  have he : Reach [a,b] [(a,b,w)] a b :=
    reach_edge (e := (a,b,w)) (by simp) (by simp [source]) (by simp [target])
  have ha : Reach [a,b] [(a,b,w)] a a := reach_refl (by simp)
  have hb : Reach [a,b] [(a,b,w)] b b := reach_refl (by simp)
  intro u hu v hv
  change Reach [a,b] [(a,b,w)] u v
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ha
  · exact he
  · exact reach_symm he
  · exact hb

/-- Diagnostic D01: empty wrapper and independent nonempty-tree convention. -/
theorem diagnostic01 : kruskal ([], []) = none ∧ ¬ ∃ t, SpanningTree ([], []) t := by
  refine ⟨by decide, ?_⟩
  rintro ⟨t, ht⟩
  exact ht.2.2.1 rfl

/-- Diagnostic D02: the zero-step singleton wrapper does not validate unused edges. -/
theorem diagnostic02 : kruskal ([1], [(99,99,-10)]) = some ([1], []) ∧
    ¬ NumberedGraph ([1], [(99,99,-10)]) := by
  refine ⟨by decide, ?_⟩
  intro h
  have hh := (h.2.2 (99,99,-10) (by decide)).1
  simp [source, nodes] at hh

/-- Diagnostic D03: a supported disconnected graph has no completed run. -/
theorem diagnostic03 : NumberedGraph ([1,2], []) ∧ ¬ ConnectedGraph ([1,2], []) ∧
    kruskal ([1,2], []) = none := by
  refine ⟨⟨by decide, by decide, by simp [EndpointsIn, edges]⟩, ?_, by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, selected, weight]⟩
  intro hc
  have hh := (reach_empty_iff [1,2] 1 2).mp (hc 1 (by decide) 2 (by decide))
  exact (by decide : (1 : Int) ≠ 2) hh.1

/-- Diagnostic D04: exact reversed acceptance order and an independent global minimum. -/
theorem diagnostic04 : kruskal ([1,2,3], [(1,2,3),(2,3,1),(1,3,2)]) =
      some ([1,2,3], [(1,3,2),(2,3,1)]) ∧
    MinimumSpanningTree ([1,2,3], [(1,2,3),(2,3,1),(1,3,2)])
      ([1,2,3], [(1,3,2),(2,3,1)]) ∧
    costMCST ([1,2,3], [(1,3,2),(2,3,1)]) = 3 := by
  have hg : NumberedGraph ([1,2,3], [(1,2,3),(2,3,1),(1,3,2)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have he : kruskal ([1,2,3], [(1,2,3),(2,3,1),(1,3,2)]) =
      some ([1,2,3], [(1,3,2),(2,3,1)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort]
  exact ⟨he, kruskal_minimum hg he, by decide⟩

/-- Diagnostic D05: stable equal-weight input order can change the optimal edge set. -/
theorem diagnostic05 : let g1 : Graph := ([1,2,3], [(1,2,1),(2,3,1),(1,3,1)])
    let g2 : Graph := ([1,2,3], [(1,3,1),(2,3,1),(1,2,1)])
    kruskal g1 = some ([1,2,3], [(2,3,1),(1,2,1)]) ∧
    kruskal g2 = some ([1,2,3], [(2,3,1),(1,3,1)]) ∧
    MinimumSpanningTree g1 ([1,2,3], [(2,3,1),(1,2,1)]) ∧
    MinimumSpanningTree g2 ([1,2,3], [(2,3,1),(1,3,1)]) ∧
    ¬ ([(2,3,1),(1,2,1)] : List Edge).Perm [(2,3,1),(1,3,1)] := by
  dsimp only
  have hg1 : NumberedGraph ([1,2,3], [(1,2,1),(2,3,1),(1,3,1)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have hg2 : NumberedGraph ([1,2,3], [(1,3,1),(2,3,1),(1,2,1)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have h1 : kruskal ([1,2,3], [(1,2,1),(2,3,1),(1,3,1)]) =
      some ([1,2,3], [(2,3,1),(1,2,1)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort]
  have h2 : kruskal ([1,2,3], [(1,3,1),(2,3,1),(1,2,1)]) =
      some ([1,2,3], [(2,3,1),(1,3,1)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort]
  exact ⟨h1, h2, kruskal_minimum hg1 h1, kruskal_minimum hg2 h2, by decide⟩

/-- Diagnostic D06: duplicate and reversed parallel occurrences remain in the exact suffix. -/
theorem diagnostic06 : kruskalState ([1,2], [(1,2,5),(1,2,1),(2,1,1),(1,2,1)]) =
      some ([(1,[1,2])], [(1,2,1)], [(2,1,1),(1,2,1),(1,2,5)]) ∧
    MinimumSpanningTree ([1,2], [(1,2,5),(1,2,1),(2,1,1),(1,2,1)])
      ([1,2], [(1,2,1)]) := by
  have hg : NumberedGraph ([1,2], [(1,2,5),(1,2,1),(2,1,1),(1,2,1)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  exact ⟨by simp +decide [kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, weight, List.mergeSort], kruskal_minimum hg (by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort])⟩

/-- Diagnostic D07: negative loops are skipped; signed global weights are unrestricted. -/
theorem diagnostic07 : kruskal ([1,2,3], [(1,1,-100),(1,2,-5),(2,3,-2),(1,3,0),(2,2,-99)]) =
      some ([1,2,3], [(2,3,-2),(1,2,-5)]) ∧
    MinimumSpanningTree ([1,2,3], [(1,1,-100),(1,2,-5),(2,3,-2),(1,3,0),(2,2,-99)])
      ([1,2,3], [(2,3,-2),(1,2,-5)]) ∧
    costMCST ([1,2,3], [(2,3,-2),(1,2,-5)]) = -7 := by
  have hg : NumberedGraph ([1,2,3], [(1,1,-100),(1,2,-5),(2,3,-2),(1,3,0),(2,2,-99)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have he : kruskal ([1,2,3], [(1,1,-100),(1,2,-5),(2,3,-2),(1,3,0),(2,2,-99)]) =
      some ([1,2,3], [(2,3,-2),(1,2,-5)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort]
  exact ⟨he, kruskal_minimum hg he, by decide⟩

/-- Diagnostic D08: original vertex order survives the numbered-universe adapter. -/
theorem diagnostic08 : NumberedGraph ([3,1,2], [(3,2,2),(2,1,1)]) ∧
    kruskal ([3,1,2], [(3,2,2),(2,1,1)]) = some ([3,1,2], [(3,2,2),(2,1,1)]) ∧
    MinimumSpanningTree ([3,1,2], [(3,2,2),(2,1,1)])
      ([3,1,2], [(3,2,2),(2,1,1)]) := by
  have hg : NumberedGraph ([3,1,2], [(3,2,2),(2,1,1)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have he : kruskal ([3,1,2], [(3,2,2),(2,1,1)]) =
      some ([3,1,2], [(3,2,2),(2,1,1)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight]
  exact ⟨hg, he, kruskal_minimum hg he⟩

/-- Diagnostic D09: abstract connectivity does not repair unsupported source labels. -/
theorem diagnostic09 : ConnectedGraph ([10,20], [(10,20,7)]) ∧
    ¬ NumberedGraph ([10,20], [(10,20,7)]) ∧
    kruskal ([10,20], [(10,20,7)]) = none := by
  refine ⟨pair_connected 10 20 7, ?_, by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, source, target, selected, weight]⟩
  intro hg
  have hm := hg.2.1.mem_iff.mp (by decide : (10 : Int) ∈ nodes ([10,20], [(10,20,7)]))
  have hn : (10 : Int) ∉ Connectivity.ListPartition.vertices (Int.ofNat (nodes ([10,20], [(10,20,7)])).length) := by decide
  exact hn hm

/-- Diagnostic D10: malformed overlapping blocks retain first-match append duplication. -/
theorem diagnostic10 : gstepK2 ([(1,[1,2]),(2,[2,3])], [], [(2,3,7)]) =
    some ([(1,[1,2,2,3])], [(2,3,7)], []) := by
  exact gstepK2_take (a := 1) (b := 2) (by decide) (by decide) (by decide) (by decide)

/-- Diagnostic D11: the client guard avoids the raw same-name union duplication. -/
theorem diagnostic11 : gstepK2 (Connectivity.ListPartition.startDS 1, [], [(1,1,-5)]) = none := by simp +decide [gstepK2]

/-- Diagnostic D12: an extra step can fail with a nonempty all-internal suffix. -/
theorem diagnostic12 : let s : StateDS := ([(1,[1,2])], [(1,2,1)], [(2,1,2),(1,1,0)])
    gstepK2 s = none ∧
    kruskal ([1,2], [(1,2,1),(2,1,2),(1,1,0)]) = some ([1,2], [(1,2,1)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort]

/-- Diagnostic D13: the actual extraction's g4 input; no invented printed-example mapping. -/
theorem diagnostic13 : let g4 : Graph := ([1,2,3,4], [(1,2,5),(1,3,6),(1,4,7),(2,4,8),(3,2,9),(3,4,10)])
    kruskal g4 = some ([1,2,3,4], [(1,4,7),(1,3,6),(1,2,5)]) ∧
    MinimumSpanningTree g4 ([1,2,3,4], [(1,4,7),(1,3,6),(1,2,5)]) ∧
    costMCST ([1,2,3,4], [(1,4,7),(1,3,6),(1,2,5)]) = 18 := by
  dsimp only
  have hg : NumberedGraph ([1,2,3,4], [(1,2,5),(1,3,6),(1,4,7),(2,4,8),(3,2,9),(3,4,10)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have he : kruskal ([1,2,3,4], [(1,2,5),(1,3,6),(1,4,7),(2,4,8),(3,2,9),(3,4,10)]) =
      some ([1,2,3,4], [(1,4,7),(1,3,6),(1,2,5)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort]
  exact ⟨he, kruskal_minimum hg he, by decide⟩

/-- Diagnostic D14: deleting an arbitrary cycle edge can lose the chosen forest and optimality. -/
theorem diagnostic14 : let g : Graph := ([1,2,3], [(1,2,1),(1,3,2),(2,3,2)])
    let good : Graph := ([1,2,3], [(1,2,1),(2,3,2)])
    let bad : Graph := ([1,2,3], [(1,3,2),(2,3,2)])
    MinimumSpanningTree g good ∧ SpanningTree g bad ∧
    costMCST good = 3 ∧ costMCST bad = 4 ∧
    ¬ MinimumSpanningTree g bad ∧ ¬ ([(1,2,1)] : List Edge) ⊆ edges bad := by
  dsimp only
  have hg : NumberedGraph ([1,2,3], [(1,2,1),(1,3,2),(2,3,2)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have hgGood : NumberedGraph ([1,2,3], [(1,2,1),(2,3,2)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have hgBad : NumberedGraph ([1,2,3], [(1,3,2),(2,3,2)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, edges, source, target, nodes]
  have hgood : SpanningTree ([1,2,3], [(1,2,1),(1,3,2),(2,3,2)])
      ([1,2,3], [(1,2,1),(2,3,2)]) := by
    have hs := kruskal_spanning hgGood
      (by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight] : kruskal ([1,2,3], [(1,2,1),(2,3,2)]) =
        some ([1,2,3], [(2,3,2),(1,2,1)]))
    exact ⟨rfl, by decide, spanningEdges_perm (by decide) hs.2.2⟩
  have hbad : SpanningTree ([1,2,3], [(1,2,1),(1,3,2),(2,3,2)])
      ([1,2,3], [(1,3,2),(2,3,2)]) := by
    have hs := kruskal_spanning hgBad
      (by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight] : kruskal ([1,2,3], [(1,3,2),(2,3,2)]) =
        some ([1,2,3], [(2,3,2),(1,3,2)]))
    exact ⟨rfl, by decide, spanningEdges_perm (by decide) hs.2.2⟩
  have hm := kruskal_minimum hg
    (by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight, List.mergeSort] : kruskal ([1,2,3], [(1,2,1),(1,3,2),(2,3,2)]) =
      some ([1,2,3], [(1,3,2),(1,2,1)]))
  have hmin : MinimumSpanningTree ([1,2,3], [(1,2,1),(1,3,2),(2,3,2)])
      ([1,2,3], [(1,2,1),(2,3,2)]) := by
    refine ⟨hgood, ?_⟩
    intro t ht
    have hc := hm.2 t ht
    have heq : costMCST ([1,2,3], [(1,2,1),(2,3,2)]) =
        costMCST ([1,2,3], [(1,3,2),(1,2,1)]) := by decide
    exact heq ▸ hc
  refine ⟨hmin, hbad, by decide, by decide, ?_, by decide⟩
  intro hh
  have hc := hh.2 _ hgood
  have hn : ¬ costMCST ([1,2,3], [(1,3,2),(2,3,2)]) ≤
      costMCST ([1,2,3], [(1,2,1),(2,3,2)]) := by decide
  exact hn hc

/-- Diagnostic D15: a universal integer-weight single-edge optimum. -/
theorem diagnostic15 : ∀ w : Int, kruskal ([1,2], [(1,2,w)]) = some ([1,2], [(1,2,w)]) ∧
    MinimumSpanningTree ([1,2], [(1,2,w)]) ([1,2], [(1,2,w)]) := by
  intro w
  have hg : NumberedGraph ([1,2], [(1,2,w)]) := by
    refine ⟨by simp [nodes], ?_, ?_⟩
    · change ([1,2] : List Vertex).Perm (Connectivity.ListPartition.vertices 2)
      decide
    · simp [EndpointsIn, edges, source, target, nodes]
  have he : kruskal ([1,2], [(1,2,w)]) = some ([1,2], [(1,2,w)]) := by simp +decide [kruskal, kruskalState, startK, applyK, gstepK2, nodes, edges, sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, Connectivity.ListPartition.startDS, Connectivity.ListPartition.vertices, List.range_succ, Connectivity.ListPartition.findDS, Connectivity.ListPartition.unionDS, Connectivity.ListPartition.lookupDS, List.lookup, source, target, selected, weight]
  exact ⟨he, kruskal_minimum hg he⟩

/-- Diagnostic D16: a symbolic skipped loop and exact arbitrary untouched suffix. -/
theorem diagnostic16 : ∀ (a b : Int) (es : List Edge),
    gstepK2 (Connectivity.ListPartition.startDS 3, [], (1,1,a) :: (1,2,b) :: es) =
      some ([(1,[1,2]),(3,[3])], [(1,2,b)], es) := by
  intro a b es
  rw [gstepK2_skip (a := 1) (by change findDS (startDS 3) 1 = some 1; decide)
    (by change findDS (startDS 3) 1 = some 1; decide)]
  exact gstepK2_take (a := 1) (b := 2)
    (by change findDS (startDS 3) 1 = some 1; decide)
    (by change findDS (startDS 3) 2 = some 2; decide) (by decide) (by decide)


/-- The connected domain is justified from the public definedness theorem. -/
def singleEdgeProblem (w : Int) : Problem :=
  let g : Graph := ([1,2], [(1,2,w)])
  have hg : NumberedGraph g := by
    refine ⟨by simp [g, nodes], ?_, ?_⟩
    · change ([1,2] : List Vertex).Perm (Connectivity.ListPartition.vertices 2)
      decide
    simp [g, EndpointsIn, nodes, edges, source, target]
  ⟨g, hg, (kruskal_defined_iff_connected hg).mp ⟨_, (diagnostic15 w).1⟩⟩

example (w : Int) : selectedTree (singleEdgeProblem w) = ([1,2], [(1,2,w)]) := by
  simp [selectedTree, singleEdgeProblem, (diagnostic15 w).1]

example (w : Int) : (costSquare.impl (singleEdgeProblem w)).2 = w := by
  have h := selected_cost_eq (singleEdgeProblem w) _ (diagnostic15 w).2
  simpa [costMCST, edges, weight] using h

example (w : Int) : costResult ([1,2], [(1,2,w)]) = some w := by
  rw [costResult, (diagnostic15 w).1]
  simp [costMCST, edges, weight]

example (i : Problem) : ∃ t, MinimumSpanningTree i.val t ∧ costMCST t = (costSquare.impl i).2 :=
  selected_cost_attained i

example (i : Problem) (t : Tree) (ht : SpanningTree i.val t) :
    (costSquare.impl i).2 ≤ costMCST t := by
  obtain ⟨s, hs, he⟩ := selected_cost_attained i
  rw [← he]
  exact hs.2 t ht

example : costResult ([1,2], []) = none :=
  (costResult_none_iff diagnostic03.1).mpr diagnostic03.2.1

example : costResult ([1], [(99,99,-10)]) = some 0 := by
  rw [costResult, diagnostic02.1]
  rfl

example : Connectivity.observe ([10,20] : List Int).toFinset [(10,20)] 10 20 = some true :=
  (reach_observe_iff [10,20] [(10,20,7)] 10 20).mpr
    (diagnostic09.1 10 (by decide) 20 (by decide))

example : costResult ([1,2,3], [(1,2,3),(2,3,1),(1,3,2)]) = some 3 := by
  rw [costResult, diagnostic04.1]
  exact congrArg some diagnostic04.2.2

example : costResult ([1,2,3], [(1,1,-100),(1,2,-5),(2,3,-2),(1,3,0),(2,2,-99)]) = some (-7) := by
  rw [costResult, diagnostic07.1]
  exact congrArg some diagnostic07.2.2

example (g h : Graph) (hg : NumberedGraph g) (hh : NumberedGraph h)
    (hn : nodes g = nodes h) (he : (edges g).Perm (edges h)) : costResult g = costResult h :=
  costResult_perm hg hh hn he

example : costResult ([1,2,3], [(1,2,1),(2,3,1),(1,3,1)]) =
    costResult ([1,2,3], [(1,3,1),(2,3,1),(1,2,1)]) := by
  apply costResult_perm
  · refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, nodes, edges, source, target]
  · refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, nodes, edges, source, target]
  · rfl
  · decide

example : costResult ([1,2,3], [(1,2,1),(2,3,1),(1,3,1)]) = some 2 := by
  rw [costResult, diagnostic05.1]
  rfl

/-- Exact source correspondence remains available on overlapping raw blocks. -/
example : SourceStep ([(1,[1,2]),(2,[2,3])], [], [(2,3,7)])
    ([(1,[1,2,2,3])], [(2,3,7)], []) :=
  (gstepK2_source_iff ..).mp diagnostic10

example (a b : Int) (es : List Edge) :
    SourceStep (startDS 3, [], (1,1,a) :: (1,2,b) :: es)
      ([(1,[1,2]),(3,[3])], [(1,2,b)], es) :=
  (gstepK2_source_iff ..).mp (diagnostic16 a b es)

example : ∃ pre, sortEdges [(1,2,5),(1,2,1),(2,1,1),(1,2,1)] =
      pre ++ [(2,1,1),(1,2,1),(1,2,5)] ∧ [(1,2,1)].reverse.Sublist pre ∧
      ∀ e ∈ [(2,1,1),(1,2,1),(1,2,5)], Reach [1,2] [(1,2,1)] (source e) (target e) := by
  have hg : NumberedGraph ([1,2], [(1,2,5),(1,2,1),(2,1,1),(1,2,1)]) := by
    refine ⟨by decide, by decide, ?_⟩
    simp [EndpointsIn, nodes, edges, source, target]
  exact (kruskal_order_and_residual hg diagnostic06.1).2

example (i : Problem) : (edges (selectedTree i)).length + 1 = (nodes i.val).length :=
  spanning_edges_length (selectedTree_minimum i).1.2.2

example (i : Problem) : (edges (selectedTree i)).length + 1 ≤ (nodes i.val).length :=
  forest_cardinality_bound i.property.1.1 (selectedTree_minimum i).1.2.2.2.1

end Examples.KruskalCases
