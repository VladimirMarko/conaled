import Applications.Search.RectangleSweep.Active
import Applications.Search.RectangleSweep.Balanced
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# Finite cardinality of the active occurrence keys

Complete keys retain the input occurrence identifier, so their cardinality is
exactly the number of active occurrences and is bounded by the input length.
The prefix-state results concern the mathematical full update fold, including
prefixes beyond an earlier scan hit. Strict complete-key inorder then identifies
the concrete balanced tree's node count with its observed-set cardinality.
No operation-cost bound follows from these cardinality results alone.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
universe u v w
variable {α : Type u} {β : Type v} {S : Type w}
variable [LE α] [LinearOrder β]

/-- Every active key comes from the finite set of input occurrences. -/
theorem activeKeys_finite (rs : List (Rectangle α β)) (k : Nat) :
    (activeKeys rs k).Finite :=
  (Set.toFinite {i : Fin rs.length | Active rs k i}).image (occurrenceKey rs)

/-- Equal rectangle values do not collapse distinct occurrence identifiers. -/
theorem activeKeys_ncard_eq (rs : List (Rectangle α β)) (k : Nat) :
    (activeKeys rs k).ncard = {i : Fin rs.length | Active rs k i}.ncard :=
  Set.ncard_image_of_injective _ (occurrenceKey_injective rs)

/-- The bound holds for every prefix length, also after schedule exhaustion. -/
theorem activeKeys_ncard_le (rs : List (Rectangle α β)) (k : Nat) :
    (activeKeys rs k).ncard ≤ rs.length := by
  rw [activeKeys_ncard_eq]
  simpa only [Nat.card_fin] using
    (Set.ncard_le_card {i : Fin rs.length | Active rs k i})

/-- Set observations of all mathematical prefix states are finite. -/
theorem stateAfter_take_observe_finite {ops : AbstractSet.DeleteOps (Key α) S}
    {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : AbstractSet.DeleteLaws ops observe Valid)
    (rs : List (Rectangle α β)) (k : Nat) :
    (observe (stateAfter ops ops.empty ((events rs).take k))).Finite := by
  rw [stateAfter_take_observe laws rs k]
  exact activeKeys_finite rs k

/-- Prefix observations count active occurrences, without an injective interval projection. -/
theorem stateAfter_take_observe_ncard_eq {ops : AbstractSet.DeleteOps (Key α) S}
    {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : AbstractSet.DeleteLaws ops observe Valid)
    (rs : List (Rectangle α β)) (k : Nat) :
    (observe (stateAfter ops ops.empty ((events rs).take k))).ncard =
      {i : Fin rs.length | Active rs k i}.ncard := by
  rw [stateAfter_take_observe laws rs k]
  exact activeKeys_ncard_eq rs k

/-- The existing primitive set laws transfer the input-length envelope. -/
theorem stateAfter_take_observe_ncard_le {ops : AbstractSet.DeleteOps (Key α) S}
    {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : AbstractSet.DeleteLaws ops observe Valid)
    (rs : List (Rectangle α β)) (k : Nat) :
    (observe (stateAfter ops ops.empty ((events rs).take k))).ncard ≤ rs.length := by
  rw [stateAfter_take_observe laws rs k]
  exact activeKeys_ncard_le rs k

end Search.RectangleSweep

namespace Search.RectangleSweep
universe u v
variable {α : Type u} {β : Type v}

/-- Strict complete keys identify observed cardinality with concrete node count.
Neither shape balance nor cache correctness is needed for this equality. -/
theorem balanced_observe_ncard_eq_numNodes [LinearOrder α]
    (t : BinaryTree (Key α × (Nat × α)))
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·)) :
    (Trees.setTree (Trees.Cached.erase t)).ncard = t.numNodes := by
  classical
  have contents : Trees.setTree (Trees.Cached.erase t) =
      ((Trees.inorder (Trees.Cached.erase t)).toFinset : Set (Key α)) := by
    ext key
    simp only [Finset.mem_coe, List.mem_toFinset, Trees.mem_inorder_iff_mem_setTree]
  rw [contents, Set.ncard_coe_finset, List.toFinset_card_of_nodup strict.nodup,
    Trees.inorder_length, Trees.Cached.numNodes_erase]

variable [LinearOrder α] [OrderBot α] [LinearOrder β]

/-- Full balanced update prefixes count active occurrences, including repeated
rectangle values with different complete keys. This is not an execution trace. -/
theorem balanced_stateAfter_take_numNodes_eq (rs : List (Rectangle α β)) (k : Nat) :
    (stateAfter (IntervalTree.Balanced.deleteOps keyInterval) .nil
      ((events rs).take k)).numNodes = {i : Fin rs.length | Active rs k i}.ncard := by
  have valid := stateAfter_take_valid
    (IntervalTree.Balanced.setLaws (keyInterval (α := α))) rs k
  change IntervalTree.Balanced.Valid keyInterval
    (stateAfter (IntervalTree.Balanced.deleteOps keyInterval) .nil
      ((events rs).take k)) at valid
  rw [← balanced_observe_ncard_eq_numNodes _ valid.2]
  exact stateAfter_take_observe_ncard_eq
    (IntervalTree.Balanced.setLaws (keyInterval (α := α))) rs k

/-- The selected balanced active representation has at most one node per input
occurrence at every mathematical prefix, also beyond schedule exhaustion. -/
theorem balanced_stateAfter_take_numNodes_le (rs : List (Rectangle α β)) (k : Nat) :
    (stateAfter (IntervalTree.Balanced.deleteOps keyInterval) .nil
      ((events rs).take k)).numNodes ≤ rs.length := by
  rw [balanced_stateAfter_take_numNodes_eq, ← activeKeys_ncard_eq]
  exact activeKeys_ncard_le rs k

end Search.RectangleSweep
