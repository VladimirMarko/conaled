import Applications.Search.IntervalKey
import Mathlib.Data.Set.Prod

/-!
# Closed rectangles and distinct input occurrences

Endpoint data and geometric meaning are separate. The carrier permits two
independent coordinate types with only endpoint relations. Closed regions and
common points use their order laws; neither coordinate needs a bottom element.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search
universe u v

structure Rectangle (α : Type u) (β : Type v) [LE α] [LE β] where
  x : IntervalKey α
  y : IntervalKey β

namespace Rectangle
variable {α : Type u} {β : Type v}

section Endpoints
variable [LE α] [LE β]

def Overlap (r s : Rectangle α β) : Prop := r.x.overlap s.x ∧ r.y.overlap s.y

theorem overlap_comm (r s : Rectangle α β) : Overlap r s ↔ Overlap s r := by
  rw [Overlap, Overlap, IntervalKey.overlap_comm r.x, IntervalKey.overlap_comm r.y]

theorem overlap_self (r : Rectangle α β) : Overlap r r :=
  ⟨r.x.overlap_self, r.y.overlap_self⟩

end Endpoints

section Geometry
variable [Preorder α] [Preorder β]

def toSet (r : Rectangle α β) : Set (α × β) := r.x.toSet ×ˢ r.y.toSet

@[simp] theorem mem_toSet (r : Rectangle α β) (p : α × β) :
    p ∈ r.toSet ↔ (r.x.low ≤ p.1 ∧ p.1 ≤ r.x.high) ∧
      (r.y.low ≤ p.2 ∧ p.2 ≤ r.y.high) := Iff.rfl

theorem toSet_nonempty (r : Rectangle α β) : r.toSet.Nonempty :=
  Set.prod_nonempty_iff.mpr ⟨r.x.toSet_nonempty, r.y.toSet_nonempty⟩

def Intersects (r s : Rectangle α β) : Prop := (r.toSet ∩ s.toSet).Nonempty

theorem intersects_comm (r s : Rectangle α β) : Intersects r s ↔ Intersects s r := by
  unfold Intersects
  rw [Set.inter_comm]

theorem intersects_self (r : Rectangle α β) : Intersects r r := by
  simpa [Intersects] using r.toSet_nonempty

/-- The two objects are distinct occurrences, even if their rectangle values agree. -/
def HasIntersection (rs : List (Rectangle α β)) : Prop :=
  ∃ i j : Fin rs.length, i ≠ j ∧ Intersects (rs.get i) (rs.get j)

@[simp] theorem not_hasIntersection_nil : ¬ HasIntersection ([] : List (Rectangle α β)) := by
  simp [HasIntersection]

@[simp] theorem not_hasIntersection_singleton (r : Rectangle α β) :
    ¬ HasIntersection [r] := by
  simp [HasIntersection]

theorem hasIntersection_pair_iff (r s : Rectangle α β) :
    HasIntersection [r, s] ↔ Intersects r s := by
  simp [HasIntersection, intersects_comm s r]

end Geometry

section LinearOrder
variable [LinearOrder α] [LinearOrder β]

theorem overlap_iff_intersects (r s : Rectangle α β) :
    Overlap r s ↔ Intersects r s := by
  simp only [Overlap, Intersects, toSet, Set.prod_inter_prod, Set.prod_nonempty_iff,
    IntervalKey.overlap_iff_nonempty_inter]

theorem hasIntersection_iff_overlap (rs : List (Rectangle α β)) :
    HasIntersection rs ↔ ∃ i j : Fin rs.length, i ≠ j ∧ Overlap (rs.get i) (rs.get j) := by
  simp only [HasIntersection, overlap_iff_intersects]

end LinearOrder
end Rectangle
end Search
