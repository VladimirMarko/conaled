import Applications.Sequences.LCA.TreeReduction

set_option autoImplicit false
set_option warningAsError true

/-! Checked Euler reductions for singleton, chain and arbitrary branching. -/
namespace Examples.LCATree
open Sequences.LCA Tree

def one : Tree := .singleton
def chain : Tree := .attach .singleton (.attach .singleton .singleton)
def star : Tree := .attach (.attach (.attach .singleton .singleton) .singleton) .singleton
def branched : Tree := .attach (.attach .singleton (.attach .singleton .singleton)) .singleton

-- The root is 0, the first child's descendant is 2, and the final child is 3.
example : (tour branched).map code = [0, 1, 2, 1, 0, 3, 0] := rfl
example : depthTable branched = [0, 1, 2, 1, 0, 1, 0] := rfl
example : firstTable branched = [0, 1, 2, 5] := rfl
example : depthTable one = [0] := rfl
example : depthTable chain = [0, 1, 2, 1, 0] := rfl
example : depthTable star = [0, 1, 0, 1, 0, 1, 0] := rfl

-- Concrete ancestry results are obtained from the independent universal law.
example : IsLCA (decode branched ⟨1, by decide⟩) (decode branched ⟨2, by decide⟩)
    (decode branched ⟨1, by decide⟩) := by
  exact lca_spec _ _
example : IsLCA (decode branched ⟨2, by decide⟩) (decode branched ⟨3, by decide⟩)
    (root branched) := by
  exact lca_spec _ _
example : IsLCA (root one) (root one) (root one) := lca_spec _ _
example : IsLCA (decode chain ⟨2, by decide⟩) (decode chain ⟨2, by decide⟩)
    (decode chain ⟨2, by decide⟩) := lca_spec _ _

-- The star interval contains the root twice. Either minimum index recovers
-- the same node identity; the downstream RMQ may choose the leftmost one.
example : visit star 2 = lca (decode star ⟨1, by decide⟩) (decode star ⟨3, by decide⟩) := by
  apply rmq_recovers_lca _ _ 2 (by decide) (by decide)
  intro i _ _
  exact Nat.zero_le _
example : visit star 4 = lca (decode star ⟨1, by decide⟩) (decode star ⟨3, by decide⟩) := by
  apply rmq_recovers_lca _ _ 4 (by decide) (by decide)
  intro i _ _
  exact Nat.zero_le _

-- Reversed query endpoints use the same interval theorem.
example : visit star 2 = lca (decode star ⟨3, by decide⟩) (decode star ⟨1, by decide⟩) := by
  apply rmq_recovers_lca_sorted _ _ 2 (by decide) (by decide)
  intro i _ _
  exact Nat.zero_le _

-- This case exercises an interval whose minimum has positive depth.
example : visit chain 1 = lca (decode chain ⟨1, by decide⟩) (decode chain ⟨2, by decide⟩) := by
  apply rmq_recovers_lca _ _ 1 (by decide) (by decide)
  intro i hlo hhi
  have hi : i = 1 ∨ i = 2 := by change 1 ≤ i at hlo; change i ≤ 2 at hhi; omega
  rcases hi with rfl | rfl <;> decide

-- The cached emitter is used through its general refinement theorem.
example : (cache branched).emit 0 0 [] = [(0, 0), (1, 1), (2, 2), (1, 1), (0, 0), (3, 1), (0, 0)] := by
  rw [emit_spec]
  rfl
example : (cache branched).calls + 1 = 8 := cache_calls branched
example : (tour star).length + 1 = 8 := tour_length star
example : depth (visit chain 2) = depth (visit chain 1) + 1 ∨
    depth (visit chain 1) = depth (visit chain 2) + 1 := adjacent_depth chain 1 (by decide)


-- Repeated visits do not overwrite the initialized first-position map.
example : (TreeBackend.prepareFirstM star (TreeBackend.emittedIds star)).2 = 56 := by decide
example : Dijkstra.Store.lookup (TreeBackend.prepareFirstM star (TreeBackend.emittedIds star)).1
    ⟨3, by decide⟩ = 5 := by
  exact TreeBackend.prepareFirstM_lookup star ⟨3, by decide⟩


example : (TreeBackend.prepareEmissionM star).2 = 59 := by decide
example : (TreeBackend.prepareMapsM star).2 = 190 := by decide
example : TreeBackend.Valid branched (TreeBackend.prepareMapsM branched).1 :=
  TreeBackend.prepareMapsM_valid branched
example : TreeBackend.translateM (TreeBackend.prepareMapsM star).1
    ⟨3, by decide⟩ ⟨1, by decide⟩ = ((1,5),3) := by
  exact TreeBackend.translate_valid _ (TreeBackend.prepareMapsM_valid star) _ _
example : TreeBackend.retainedWords star = 18 := rfl


example : TreeBackend.Eligible star 7 80 := by decide
example : TreeBackend.preparationPeak star = 50 := by decide
example : ¬ TreeBackend.preparationPeak star ≤ 32 := by decide
example : TreeBackend.preparationPeak star ≤ 80 ∧ TreeBackend.retainedWords star + 4 ≤ 80 :=
  TreeBackend.eligible_capacity star 7 80 (by decide)


-- The shared Reduction consumes a static tree; future queries are supplied
-- separately. Its target carries the derived +/-1 admission proof.
def starSource : TreeReduction.Source 4 := ⟨star,rfl⟩
def siblingQuery : TreeReduction.Query 4 := (⟨1,by decide⟩,⟨3,by decide⟩)

example :
    ((TreeReduction.reduction 4).decode ((TreeReduction.reduction 4).convert starSource).1.1
      (TreeReduction.rmqSpec ((TreeReduction.reduction 4).convert starSource).1.2
        ((TreeReduction.reduction 4).encode
          ((TreeReduction.reduction 4).convert starSource).1.1 siblingQuery).1)).1 = 0 := by
  exact TreeReduction.translation TreeReduction.rmqSpec (TreeReduction.rmqSpec_correct _)
    starSource siblingQuery

-- Same-capacity source mutation changes the prepared decoder. Reusing this
-- state cannot satisfy the shared reduction's source-linked validity equation.
def starThree : TreeReduction.Source 3 := ⟨.attach (.attach .singleton .singleton) .singleton,rfl⟩
def chainThree : TreeReduction.Source 3 := ⟨chain,rfl⟩
example : (TreeReduction.convertM starThree).1.1 ≠ (TreeReduction.convertM chainThree).1.1 := by
  intro h
  have he := congrArg (fun d : TreeReduction.Decoder 3 => Dijkstra.Store.lookup d.first ⟨2,by decide⟩) h
  change 3 = 2 at he
  omega

end Examples.LCATree
