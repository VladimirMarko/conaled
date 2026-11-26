import Applications.Resources.RedBlackBalance
import Examples.RedBlackTrees

/-!
# Source balance work and observable pattern priority

The exact examples consume the guarded public branch equations. Their costs
were calculated from root selection followed by fresh complete attempts, with
early failure at the first wrong node constructor or color. The same returned
tree can arise with different construction counts; these are source charges.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RedBlackBalanceWork

open RBTree RBTree.RBColor RBTree.RBNode
open Search.RedBlack (Tree)
open Resources.RedBlack

private abbrev r (key : Int) (value : Nat) : Tree Int Nat :=
  node red nil (key, value) nil

private abbrev b (key : Int) (value : Nat) : Tree Int Nat :=
  node black nil (key, value) nil

private def expectedCost (patterns observations constructions : Nat) : Cost :=
  tick .balanceCalls 1 + tick .patternAttempts patterns +
    tick .datatypeObservations observations + tick .nodeConstructions constructions

/-- LL succeeds at its first attempt: one root observation and four pattern observations. -/
theorem left_left_exact :
    balanceRun black (node red (r 0 100) (1, 101) nil) 2 102 nil =
      (node red (b 0 100) (1, 101) (b 2 102), expectedCost 2 5 3) :=
  balanceRun_left_left _ _ _ _ ⟨nil, (0, 100), nil, (1, 101), nil⟩ rfl

/-- The failed LL attempt observes three fields; the succeeding LR attempt observes four. -/
theorem left_right_exact :
    balanceRun black (node red nil (0, 100) (r 1 101)) 2 102 nil =
      (node red (b 0 100) (1, 101) (b 2 102), expectedCost 3 8 3) :=
  balanceRun_left_right _ _ _ _ ⟨nil, (0, 100), nil, (1, 101), nil⟩ rfl rfl

/-- Each left attempt stops at nil before the four-observation RL success. -/
theorem right_left_exact :
    balanceRun black nil 0 100 (node red (r 1 101) (2, 102) nil) =
      (node red (b 0 100) (1, 101) (b 2 102), expectedCost 4 7 3) :=
  balanceRun_right_left _ _ _ _ ⟨nil, (1, 101), nil, (2, 102), nil⟩ rfl rfl rfl

/-- RR also pays the failed RL attempt, which stops at its nil child. -/
theorem right_right_exact :
    balanceRun black nil 0 100 (node red nil (1, 101) (r 2 102)) =
      (node red (b 0 100) (1, 101) (b 2 102), expectedCost 5 10 3) :=
  balanceRun_right_right _ _ _ _ ⟨nil, (1, 101), nil, (2, 102), nil⟩ rfl rfl rfl rfl

/-- Red bypass preserves even a red-red child and does not examine it. -/
theorem red_bypass_exact :
    balanceRun red (node red (r 0 100) (1, 101) nil) 2 102 nil =
      (node red (node red (r 0 100) (1, 101) nil) (2, 102) nil,
        expectedCost 1 1 1) :=
  balanceRun_red _ _ _ _

/-- Four failed patterns at nil give five observations, rather than seventeen. -/
theorem empty_fallback_exact :
    balanceRun black (nil : Tree Int Nat) 0 100 nil =
      (b 0 100, expectedCost 5 5 1) :=
  balanceRun_fallback _ _ _ _ rfl rfl rfl rfl

theorem left_overlap_exact :
    balanceRun black (node red (r 0 100) (1, 101) (r 2 102)) 3 103 nil =
      (node red (b 0 100) (1, 101) (node black (r 2 102) (3, 103) nil),
        expectedCost 2 5 3) :=
  balanceRun_left_left _ _ _ _ ⟨nil, (0, 100), nil, (1, 101), r 2 102⟩ rfl

/-- A matching right side is not examined after the left-left success. -/
theorem both_sides_exact :
    balanceRun black (node red (r 0 100) (1, 101) nil) 3 103
        (node red (r 4 104) (5, 105) nil) =
      (node red (b 0 100) (1, 101)
        (node black nil (3, 103) (node red (r 4 104) (5, 105) nil)),
        expectedCost 2 5 3) :=
  balanceRun_left_left _ _ _ _ ⟨nil, (0, 100), nil, (1, 101), nil⟩ rfl

/-- Both right patterns match; the source still promotes key1, with the RL cost. -/
theorem right_overlap_exact :
    balanceRun black nil 0 100 (node red (r 1 101) (2, 102) (r 3 103)) =
      (node red (b 0 100) (1, 101) (node black nil (2, 102) (r 3 103)),
        expectedCost 4 7 3) :=
  balanceRun_right_left _ _ _ _ ⟨nil, (1, 101), nil, (2, 102), r 3 103⟩ rfl rfl rfl

theorem right_overlap_both_recognizers :
    (leftPairRun (node red (r 1 101) (2, 102) (r 3 103))).1 =
        some ⟨nil, (1, 101), nil, (2, 102), r 3 103⟩ ∧
      (rightPairRun (node red (r 1 101) (2, 102) (r 3 103))).1 =
        some ⟨r 1 101, (2, 102), nil, (3, 103), nil⟩ :=
  ⟨rfl, rfl⟩

/-- Dropping the earlier-failure guard would give the wrong later-case charge. -/
theorem right_overlap_not_right_right_charge :
    (balanceRun black nil 0 100
      (node red (r 1 101) (2, 102) (r 3 103))).2 .patternAttempts ≠ 5 := by
  rw [right_overlap_exact]
  decide

theorem left_overlap_not_left_right_charge :
    (balanceRun black (node red (r 0 100) (1, 101) (r 2 102)) 3 103 nil).2
      .patternAttempts ≠ 3 := by
  rw [left_overlap_exact]
  decide

/-- The measured source value preserves the already checked provider counterexample. -/
theorem measured_right_overlap_differs_provider :
    (balanceRun black nil 0 100
      (node red (r 1 101) (2, 102) (r 3 103))).1 ≠
      RBNode.balance2 nil (0, 100) (node red (r 1 101) (2, 102) (r 3 103)) := by
  rw [balanceRun_value]
  exact Examples.RedBlackTrees.right_overlap_source_ne_provider

/-- Each fresh attempt reaches a black child's color before failing, attaining17. -/
theorem maximum_observations_exact :
    balanceRun black (node red (b 0 100) (1, 101) (b 2 102)) 3 103
        (node red (b 4 104) (5, 105) (b 6 106)) =
      (node black (node red (b 0 100) (1, 101) (b 2 102)) (3, 103)
        (node red (b 4 104) (5, 105) (b 6 106)), expectedCost 5 17 1) :=
  balanceRun_fallback _ _ _ _ rfl rfl rfl rfl

theorem maximum_observations_attains_bound :
    (balanceRun black (node red (b 0 100) (1, 101) (b 2 102)) 3 103
      (node red (b 4 104) (5, 105) (b 6 106))).2 .datatypeObservations = 17 ∧
    (balanceRun black (node red (b 0 100) (1, 101) (b 2 102)) 3 103
      (node red (b 4 104) (5, 105) (b 6 106))).2 .datatypeObservations ≤ 17 := by
  constructor
  · rw [maximum_observations_exact]
    rfl
  · exact balanceRun_datatypeObservations_le _ _ _ _ _

/-- Equal constructed values do not identify the source operations that produced them. -/
theorem same_tree_different_constructions :
    (balanceRun red (b 0 100) 1 101 (b 2 102)).1 =
        (balanceRun black (node red (r 0 100) (1, 101) nil) 2 102 nil).1 ∧
      (balanceRun red (b 0 100) 1 101 (b 2 102)).2 .nodeConstructions = 1 ∧
      (balanceRun black (node red (r 0 100) (1, 101) nil) 2 102 nil).2
        .nodeConstructions = 3 := by
  rw [balanceRun_red, left_left_exact]
  exact ⟨rfl, rfl, rfl⟩

/-- The rotation constructs three source nodes while the represented size stays three. -/
theorem constructions_are_not_net_growth :
    (node black (node red (r 0 100) (1, 101) nil) (2, 102) nil).size = 3 ∧
      (balanceRun black (node red (r 0 100) (1, 101) nil) 2 102 nil).1.size = 3 ∧
      (balanceRun black (node red (r 0 100) (1, 101) nil) 2 102 nil).2
        .nodeConstructions = 3 := by
  rw [left_left_exact]
  exact ⟨rfl, rfl, rfl⟩

universe u v

/-- Balance leaves all search/comparator measurements at zero, on every raw tree. -/
theorem balance_has_no_search_work {κ : Type u} {ν : Type v}
    (color : RBColor) (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν) :
    (balanceRun color left key value right).2 .visits = 0 ∧
      (balanceRun color left key value right).2 .comparisons = 0 ∧
      (balanceRun color left key value right).2 .comparatorWork = 0 := by
  exact ⟨balanceRun_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide),
    balanceRun_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide),
    balanceRun_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)⟩

/-- The all-raw value adapter composes with the existing arbitrary-suffix law. -/
theorem measured_balance_suffix {κ : Type u} {ν : Type v}
    (color : RBColor) (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν)
    (suffix : List (κ × ν)) :
    Search.RedBlack.elementsAux (balanceRun color left key value right).1 suffix =
      (Search.RedBlack.elements left ++ (key, value) :: Search.RedBlack.elements right) ++
        suffix := by
  rw [balanceRun_value, Search.RedBlack.elementsAux_eq, Search.RedBlack.balance_elements]

/-- Key and payload universes remain independent, including type-valued payloads. -/
theorem type_payload_balance (value : Type v) :
    (balanceRun red (nil : Tree Int (Type v)) 0 value nil).1 =
      node red nil (0, value) nil ∧
      (balanceRun red (nil : Tree Int (Type v)) 0 value nil).2 .balanceCalls = 1 := by
  constructor
  · exact congrArg Prod.fst (balanceRun_red _ _ _ _)
  · exact balanceRun_balanceCalls _ _ _ _ _

end Examples.RedBlackBalanceWork
