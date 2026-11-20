import Applications.Search.RectangleSweep.Active

/-!
# Correctness of the closed-rectangle sweep

The active-prefix invariant and the actual sorted event positions connect a
successful insertion query to two distinct input occurrences. Conversely, the
later insertion of an overlapping pair precedes the earlier rectangle's deletion,
including closed boundary contact. The proof uses no balance or cost assumption.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
universe u v w
variable {α : Type u} {β : Type v} {S : Type w}

section Overlap
variable [LE α] [LinearOrder β]

theorem event_y_le_of_position_le (rs : List (Rectangle α β))
    (p q : Fin (events rs).length) (h : p ≤ q) :
    ((events rs).get p).y ≤ ((events rs).get q).y := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact Event.y_le_of_key_le ((events_sorted rs).rel_get_of_lt hlt)
  · exact le_rfl

/-- An active occurrence at an insertion is different and overlaps it in y. -/
theorem active_at_insert (rs : List (Rectangle α β)) (i j : Fin rs.length)
    (active : Active rs (position rs .insert j).val i) :
    i ≠ j ∧ (rs.get i).y.overlap (rs.get j).y := by
  obtain ⟨hi, hd⟩ := (active_iff_positions rs _ i).mp active
  have distinct : i ≠ j := by
    rintro rfl
    exact (lt_irrefl _) hi
  have lower : (rs.get i).y.low ≤ (rs.get j).y.low := by
    simpa only [position_spec, eventAt, eventFor] using
      event_y_le_of_position_le rs (position rs .insert i) (position rs .insert j) hi.le
  have upper : (rs.get j).y.low ≤ (rs.get i).y.high := by
    simpa only [position_spec, eventAt, eventFor] using
      event_y_le_of_position_le rs (position rs .insert j) (position rs .delete i) hd
  exact ⟨distinct, upper, lower.trans (rs.get j).y.low_le_high⟩

/-- A weak ordinate comparison suffices even when insertion and deletion tie. -/
theorem active_at_later_insert (rs : List (Rectangle α β)) (i j : Fin rs.length)
    (earlier : position rs .insert i < position rs .insert j)
    (cross : (rs.get j).y.low ≤ (rs.get i).y.high) :
    Active rs (position rs .insert j).val i := by
  apply (active_iff_positions rs _ i).mpr
  refine ⟨earlier, ?_⟩
  have before : position rs .insert j < position rs .delete i := by
    apply insert_position_lt_delete (events_sorted rs)
      (position rs .insert j) (position rs .delete i)
    · rw [position_spec]
      rfl
    · rw [position_spec]
      rfl
    · simpa only [position_spec, eventAt, eventFor] using cross
  exact before.le

/-- Endpoint overlap needs only the x relation; geometry is a separate theorem. -/
theorem sweep_eq_true_iff_overlap {ops : AbstractSet.DeleteOps (Key α) S}
    {query : S → IntervalKey α → Bool} {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : IntervalSet.Laws ops query keyInterval observe Valid)
    (rs : List (Rectangle α β)) :
    sweep ops query rs = true ↔
      ∃ i j : Fin rs.length, i ≠ j ∧ Rectangle.Overlap (rs.get i) (rs.get j) := by
  rw [sweep, scan_eq_true_iff]
  constructor
  · rintro ⟨p, hkind, hquery⟩
    obtain ⟨kind, j, he⟩ :=
      (mem_events_iff rs ((events rs).get p)).mp (List.get_mem _ _)
    rw [he] at hkind
    change kind = .insert at hkind
    subst kind
    rw [he] at hquery
    change query (stateAfter ops ops.empty ((events rs).take p.val)) (rs.get j).x = true
      at hquery
    obtain ⟨i, active, hx⟩ := (query_stateAfter_take_iff laws rs p.val (rs.get j).x).mp hquery
    have hp := position_eq_of_get rs .insert j p he
    rw [← hp] at active
    obtain ⟨distinct, hy⟩ := active_at_insert rs i j active
    exact ⟨i, j, distinct, hx, hy⟩
  · rintro ⟨i, j, distinct, overlap⟩
    have ne := position_ne_of_id_ne rs .insert .insert distinct
    obtain ⟨a, b, earlier, overlap'⟩ :
        ∃ a b : Fin rs.length, position rs .insert a < position rs .insert b ∧
          Rectangle.Overlap (rs.get a) (rs.get b) := by
      rcases lt_or_gt_of_ne ne with hij | hji
      · exact ⟨i, j, hij, overlap⟩
      · exact ⟨j, i, hji, (Rectangle.overlap_comm _ _).mp overlap⟩
    refine ⟨position rs .insert b, ?_, ?_⟩
    · rw [position_spec]
      rfl
    · rw [position_spec]
      exact (query_stateAfter_take_iff laws rs _ (rs.get b).x).mpr
        ⟨a, active_at_later_insert rs a b earlier overlap'.2.1, overlap'.1⟩

end Overlap

section Geometry
variable [LinearOrder α] [LinearOrder β]

/-- The actual algorithm detects a common point of two distinct occurrences. -/
theorem sweep_eq_true_iff_hasIntersection {ops : AbstractSet.DeleteOps (Key α) S}
    {query : S → IntervalKey α → Bool} {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : IntervalSet.Laws ops query keyInterval observe Valid)
    (rs : List (Rectangle α β)) :
    sweep ops query rs = true ↔ Rectangle.HasIntersection rs :=
  (sweep_eq_true_iff_overlap laws rs).trans (Rectangle.hasIntersection_iff_overlap rs).symm

end Geometry

section KeyOrder
variable [LinearOrder α]

/-- Complete-key order preserves weak low-endpoint order despite duplicate intervals. -/
theorem keyInterval_low_le_of_lt (a b : Key α) (h : a < b) :
    (keyInterval a).low ≤ (keyInterval b).low := by
  apply IntervalKey.low_le_of_le
  rcases Prod.Lex.toLex_lt_toLex.mp h with h | h
  · exact h.le
  · exact h.1.le

end KeyOrder
end Search.RectangleSweep
