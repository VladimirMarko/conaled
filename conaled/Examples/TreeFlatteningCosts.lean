import Applications.Resources.TreeFlattening.Growth
import Applications.Resources.TreeFlattening.Observation

/-! Exact output order, source branch costs and composed observations. -/
namespace Examples.TreeFlatteningCosts
open RandomAccess Resources Resources.TreeFlattening Resources.RandomAccessCosts

example : appendWithCost ([] : List Nat) [8,9] = ([8,9],0) := appendWithCost_exact _ _
example : appendWithCost [1,1,2] [3,1] = ([1,1,2,3,1],3) := appendWithCost_exact _ _
example : fromTsWithCost ([] : List (Bracketing.Tree Nat)) = ([],1) := fromTsWithCost_exact _
example : fromTWithCost (.leaf 7) = ([7],1) := rfl
example : fromTsWithCost [.leaf 7] = ([7],2) := fromTsWithCost_exact _
example : 2 * (fromTWithCost (erase (.leaf 7))).2 + 2 = 4 :=
  fromTWithCost_perfect_exact (Perfect.leaf 7)
example : (fromTsWithCost [erase (.leaf 7)]).2 = 2 :=
  fromTsWithCost_perfect_exact (Perfect.leaf 7)
example : ¬ (fromTWithCost (erase (.leaf 7))).2 ≤ 3 * (0 * 2^0) := by decide

private def malformed (n : Nat) : RandomAccess.Tree Nat := .node n (.leaf 1) (.leaf 2)
example : cachedFromTsWithCost [malformed 99,.leaf 3] = ([1,2,3],5) := by
  rw [cachedFromTsWithCost_exact]; rfl
example : cachedFromTsWithCost [malformed 99,.leaf 3] =
    cachedFromTsWithCost [malformed 0,.leaf 3] := by
  rw [cachedFromTsWithCost_erasure, cachedFromTsWithCost_erasure]; rfl
example : cachedFromTWithCost (malformed 99) = cachedFromTWithCost (malformed 0) := by
  rw [cachedFromTWithCost_erasure, cachedFromTWithCost_erasure]; rfl
example : (cachedFromTWithCost (malformed 99)).1 = [1,2] := cachedFromTWithCost_value _
example : ¬ Cached (malformed 99) := by simp [malformed, Cached, size]

private def leftShape : Bracketing.Tree Nat := .fork (.fork (.leaf 1) (.leaf 2)) (.leaf 3)
private def rightShape : Bracketing.Tree Nat := .fork (.leaf 1) (.fork (.leaf 2) (.leaf 3))
example : copies leftShape = 3 ∧ copies rightShape = 2 := ⟨rfl,rfl⟩
example : (fromTWithCost leftShape).1 = (fromTWithCost rightShape).1 := by
  rw [fromTWithCost_value, fromTWithCost_value]; rfl
example : (fromTWithCost leftShape).2 = 8 ∧ (fromTWithCost rightShape).2 = 7 := by
  rw [fromTWithCost_count, fromTWithCost_count]; exact ⟨rfl,rfl⟩
example : (fromTsWithCost [leftShape]).2 = 6 ∧ (fromTsWithCost [rightShape]).2 = 6 := by
  rw [fromTsWithCost_exact, fromTsWithCost_exact]; exact ⟨rfl,rfl⟩
example : fromTs ([Bracketing.Tree.fork (.leaf 1) (.leaf 1)] ++ [.leaf 2,.leaf 1]) =
    [1,1,2,1] := by rw [fromTs_suffix, fromTs_refinement, fromTs_refinement]; rfl
example : fromTs [leftShape] = [1,2,3] := fromTs_singleton _
example : pending ([leftShape] ++ [.leaf 7]) = 6 := by rw [pending_append]; rfl
example : ((flattenAppend [3,1]).impl [.node 99 (.leaf 1) (.leaf 1),.leaf 2]).1 = [1,1,2,3,1] :=
  flattenAppend_value _ _
example : ((flattenAppend [3,1]).impl [.node 99 (.leaf 1) (.leaf 1),.leaf 2]).2 = 8 := by
  rw [flattenAppend_cost]; rfl
example : ((flattenAppend [3,1]).impl ([] : List (RandomAccess.Tree Nat))) = ([3,1],1) := by
  apply Prod.ext
  · exact flattenAppend_value _ _
  · exact flattenAppend_cost _ _

-- Rank three has 15 constructor visits and 12 copied cells recursively.
example : nodes (erase (perfectTree 7 3)) + 1 = 16 := nodes_perfect (perfectTree_valid 7 3)
example : 2 * copies (erase (perfectTree 7 3)) = 24 := copies_perfect (perfectTree_valid 7 3)
example : cachedFromTWithCost (perfectTree 7 3) = (List.replicate 8 7,27) := by
  apply Prod.ext
  · rw [cachedFromTWithCost_value, perfectTree_values]
  · have h := fromTWithCost_perfect_exact (perfectTree_valid 7 3)
    rw [cachedFromTWithCost_erasure]
    omega
example : cachedFromTsWithCost [perfectTree 7 3] = (List.replicate 8 7,16) := by
  apply Prod.ext
  · rw [cachedFromTsWithCost_exact]; simp [perfectTree_values]
  · rw [cachedFromTsWithCost_erasure]
    exact fromTsWithCost_perfect_exact (perfectTree_valid 7 3)
example : 24 ≤ 2 * (fromTWithCost (erase (perfectTree 7 3))).2 ∧
    (fromTWithCost (erase (perfectTree 7 3))).2 ≤ 72 :=
  fromTWithCost_perfect_bounds (perfectTree_valid 7 3) (by decide)

-- Both standard growth claims concern actual executions indexed by rank.
example : Asymptotics.IsBigO Filter.atTop
    (fun p => ((cachedFromTWithCost (perfectTree 7 p)).2 : ℝ))
    (fun p => ((p * 2^p : Nat) : ℝ)) := (recursive_flatten_theta 7).1
example : Asymptotics.IsBigO Filter.atTop
    (fun p => ((2^p : Nat) : ℝ))
    (fun p => ((cachedFromTsWithCost [perfectTree 7 p]).2 : ℝ)) := (stack_flatten_theta 7).2
example (p : Nat) (hp : 1 ≤ p) :
    (cachedFromTWithCost (perfectTree 7 p)).2 ≤ 3 * (p * 2^p) := by
  rw [cachedFromTWithCost_erasure]
  exact (fromTWithCost_perfect_bounds (perfectTree_valid 7 p) hp).2
example (p : Nat) : (cachedFromTsWithCost [perfectTree 7 p]).2 ≤ 2 * 2^p := by
  rw [cachedFromTsWithCost_erasure]
  exact Nat.le_of_eq (fromTsWithCost_perfect_exact (perfectTree_valid 7 p))

example : ((flattenQuery recursiveSquare 1).impl (malformed 99)).1 = some 2 :=
  flattenQuery_value _ _ _
example : ((flattenQuery stackTreeSquare 2).impl (malformed 99)).1 = none :=
  flattenQuery_value _ _ _
example (query : Nat) : ((flattenQuery recursiveSquare query).impl (malformed 99)).1 =
    ((flattenQuery stackTreeSquare query).impl (malformed 99)).1 := flattenQuery_agreement _ _
example : ((flattenQuery recursiveSquare 1).impl (malformed 99)).2 = 11 := by
  rw [flattenQuery_cost]; rfl
example : ((flattenQuery stackTreeSquare 2).impl (malformed 99)).2 = 10 := by
  rw [flattenQuery_cost]
  change (cachedFromTsWithCost [malformed 99]).2 +
    (toRARun (cachedFromTsWithCost [malformed 99]).1).2 +
    (fetchRARun 2 (toRARun (cachedFromTsWithCost [malformed 99]).1).1).2 = 10
  rw [cachedFromTsWithCost_exact]; rfl
example : ((flattenQuery recursiveSquare 0).impl (perfectTree 7 3)).2 = 50 := by
  rw [flattenQuery_cost]; rfl
example : ((flattenQuery stackTreeSquare 0).impl (perfectTree 7 3)).2 = 39 := by
  rw [flattenQuery_cost]
  change (cachedFromTsWithCost [perfectTree 7 3]).2 +
    (toRARun (cachedFromTsWithCost [perfectTree 7 3]).1).2 +
    (fetchRARun 0 (toRARun (cachedFromTsWithCost [perfectTree 7 3]).1).1).2 = 39
  rw [cachedFromTsWithCost_exact]; rfl

end Examples.TreeFlatteningCosts
