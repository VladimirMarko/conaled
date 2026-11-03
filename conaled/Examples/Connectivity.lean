import Applications.Connectivity.Realizations

/-! Original requests (2,3), (1,2), then (2,4) distinguish the array's size
choice from the list's first-name choice. Observers consume the proved history. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.Connectivity

open _root_.Connectivity _root_.Connectivity.ParentArray _root_.Connectivity.ParentHistory
  _root_.Connectivity.Refinement _root_.Connectivity.ParentCounts

/-- After the first two requests, vertex 4 is still isolated. -/
def beforeArray : DSA := ⟨#[2, 2, 2, 4], #[1, 3, 1, 1]⟩
def beforeList : ListPartition.DS := [(1, [1, 2, 3]), (4, [4])]
def afterArray : DSA := ⟨#[2, 2, 2, 2], #[1, 4, 1, 1]⟩
def afterList : ListPartition.DS := [(1, [1, 2, 3, 4])]

theorem before_history : JointHistory 4 [(2, 3), (1, 2)] beforeArray beforeList := by
  have first : JointHistory 4 [(2, 3)] ⟨#[1, 2, 2, 4], #[1, 2, 1, 1]⟩
      [(2, [2, 3]), (1, [1]), (4, [4])] :=
    joint_request JointHistory.start (by decide) (by decide)
  exact joint_request first (by decide) (by decide)

/-- Equal partitions do not identify the chosen representatives. -/
theorem different_representatives :
    findDSA beforeArray 2 = some 2 ∧ ListPartition.findDS beforeList 2 = some 1 ∧
      ComponentRefines beforeArray beforeList :=
  ⟨by decide, by decide, jointHistory_refines before_history⟩

/-- Reusing array representative 2 as a list name would fail; list find returns 1. -/
theorem own_find_arguments :
    ListPartition.unionDS 2 4 beforeList = none ∧
      request arrayOps beforeArray 2 4 = .merged afterArray ∧
      request listOps beforeList 2 4 = .merged afterList := by decide

theorem after_history :
    JointHistory 4 [(2, 3), (1, 2), (2, 4)] afterArray afterList :=
  joint_request before_history own_find_arguments.2.1 own_find_arguments.2.2

/-- The realization theorem constructs the matching list result from the array step. -/
theorem own_find_realization :
    ∃ l, request listOps beforeList 2 4 = .merged l ∧
      JointHistory 4 [(2, 3), (1, 2), (2, 4)] afterArray l :=
  joint_request_realized before_history own_find_arguments.2.1

/-- Connectivity follows the original vertex edges, independently of both finds. -/
theorem one_three_connected :
    Connected (ListPartition.vertices 4).toFinset [(2, 3), (1, 2)] 1 3 := by
  apply Connected.trans (v := 2)
  · exact Connected.edge (by decide) (by decide) (by decide)
  · exact Connected.edge (by decide) (by decide) (by decide)

theorem query_after_history :
    query arrayOps beforeArray 1 3 = some true ∧ query listOps beforeList 1 3 = some true := by
  have result := (observe_true_iff _ _ _ _).mpr one_three_connected
  have shared := joint_queries before_history 1 3
  exact ⟨shared.1.trans result, shared.2.trans result⟩

/-- The composed observation square certifies the forest builder's retain decision. -/
theorem retain_before_merge :
    (retainEdgeSquare 4 (2, 4)).spec [(2, 3), (1, 2)] = some true ∧
      retainEdge listOps beforeList (2, 4) = some true := by
  have shared := joint_retainEdge before_history (2, 4)
  have actual : retainEdge arrayOps beforeArray (2, 4) = some true := by decide
  have semantic := shared.1.symm.trans actual
  exact ⟨semantic, shared.2.trans semantic⟩

theorem retained_endpoints_disconnected :
    ¬ Connected (ListPartition.vertices 4).toFinset [(2, 3), (1, 2)] 2 4 :=
  ((list_queryLaws before_history).retain_iff 2 4 |>.mp retain_before_merge.2).2.2

/-- A repeated request has an explicit outcome and never enters JointHistory. -/
theorem already_connected :
    request arrayOps beforeArray 1 3 = .alreadyConnected ∧
      request listOps beforeList 1 3 = .alreadyConnected ∧
      ¬ ∃ a l, JointHistory 4 [(2, 3), (1, 2), (1, 3)] a l := by
  have ha := ((array_queryLaws (jointHistory_array before_history)).request_already 1 3).mpr
    one_three_connected
  have hl := ((list_queryLaws before_history).request_already 1 3).mpr one_three_connected
  exact ⟨ha, hl, no_joint_extension_of_already before_history ha⟩

theorem cycle_rejected : retainEdge arrayOps beforeArray (1, 3) = some false ∧
    retainEdge listOps beforeList (1, 3) = some false := by
  have shared := joint_retainEdge before_history (1, 3)
  have semantic := (observe_true_iff _ _ _ _).mpr one_three_connected
  simpa only [semantic, Option.map_some, Bool.not_true] using shared

/-- Two failed finds compare equal, but the public query reports an invalid domain. -/
theorem invalid_vertices :
    findDSA beforeArray 0 = findDSA beforeArray 5 ∧
      query arrayOps beforeArray 0 5 = none ∧ query listOps beforeList 0 5 = none ∧
      request arrayOps beforeArray 0 5 = .missingVertex ∧
      request listOps beforeList 0 5 = .missingVertex := by
  have bad : ¬ (0 ∈ (ListPartition.vertices 4).toFinset ∧
      5 ∈ (ListPartition.vertices 4).toFinset) := by decide
  have semantic := (observe_none_iff _ ([(2, 3), (1, 2)] : List (Int × Int)) _ _).mpr bad
  have queries := joint_queries before_history 0 5
  exact ⟨by decide, queries.1.trans semantic, queries.2.trans semantic,
    ((array_queryLaws (jointHistory_array before_history)).request_missing 0 5).mpr bad,
    ((list_queryLaws before_history).request_missing 0 5).mpr bad⟩

/-- Conservation counts successful requests and components, not runtime operations. -/
theorem logical_counts : afterList.length + ([(2, 3), (1, 2), (2, 4)] : List (Int × Int)).length = 4 ∧
    rootCount afterArray = afterList.length := jointHistory_counts after_history

end Examples.Connectivity
