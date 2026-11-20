import Applications.Search.RectangleSweep.Scan
import Applications.Search.IntervalSet.Contract
import Mathlib.Data.Set.Function

/-!
# Exact activity of rectangle occurrences

Activity is defined by insertion membership and deletion absence in an event
prefix. Canonical positions give its arithmetic presentation. The complete-key
image transports exact deletion, and the shared update laws supply the prefix
state invariant independently of early-return scan correctness.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
universe u v w
variable {α : Type u} {β : Type v} {S : Type w}

section Keys
variable [LE α] [LE β]

def occurrenceKey (rs : List (Rectangle α β)) (i : Fin rs.length) : Key α :=
  toLex ((rs.get i).x, i.val)

theorem occurrenceKey_injective (rs : List (Rectangle α β)) :
    Function.Injective (occurrenceKey rs) := by
  intro i j h
  exact Fin.ext (congrArg (fun key : Key α => (ofLex key).2) h)

@[simp] theorem keyInterval_occurrenceKey (rs : List (Rectangle α β))
    (i : Fin rs.length) : keyInterval (occurrenceKey rs i) = (rs.get i).x := rfl

@[simp] theorem completeKey_eventAt (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) : (eventAt rs kind i).completeKey = occurrenceKey rs i := rfl

end Keys

section Positions
variable [LE α] [LinearOrder β]

/-- A proof-only selected position; the executable scan never computes it. -/
noncomputable def position (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) : Fin (events rs).length :=
  Classical.choose (existsUnique_position rs kind i)

theorem position_spec (rs : List (Rectangle α β)) (kind : Kind) (i : Fin rs.length) :
    (events rs).get (position rs kind i) = eventAt rs kind i :=
  (Classical.choose_spec (existsUnique_position rs kind i)).1

theorem position_eq_of_get (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) (p : Fin (events rs).length)
    (hp : (events rs).get p = eventAt rs kind i) : position rs kind i = p :=
  (events_nodup rs).injective_get ((position_spec rs kind i).trans hp.symm)

theorem identity_eq_of_position_eq (rs : List (Rectangle α β))
    {left right : Kind} {i j : Fin rs.length}
    (h : position rs left i = position rs right j) : (left, i.val) = (right, j.val) := by
  have hi := congrArg (fun p : Fin (events rs).length => ((events rs).get p).identity) h
  simpa only [position_spec, identity_eventAt] using hi

theorem position_ne_of_id_ne (rs : List (Rectangle α β)) (left right : Kind)
    {i j : Fin rs.length} (h : i ≠ j) : position rs left i ≠ position rs right j := by
  intro heq
  exact h (Fin.ext (congrArg Prod.snd (identity_eq_of_position_eq rs heq)))

theorem own_positions_lt (rs : List (Rectangle α β)) (i : Fin rs.length) :
    position rs .insert i < position rs .delete i :=
  own_insert_position_lt_delete rs i _ _ (position_spec rs .insert i)
    (position_spec rs .delete i)

theorem eventAt_mem_take_iff (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) (k : Nat) :
    eventAt rs kind i ∈ (events rs).take k ↔ (position rs kind i).val < k := by
  constructor
  · intro h
    obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp h
    have hjlen : j < (events rs).length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hp := position_eq_of_get rs kind i ⟨j, hjlen⟩ hget
    rw [hp]
    exact lt_of_lt_of_le hj (Nat.min_le_left _ _)
  · intro h
    exact List.mem_take_iff_getElem.mpr
      ⟨(position rs kind i).val, lt_min h (position rs kind i).isLt,
        position_spec rs kind i⟩

def Active (rs : List (Rectangle α β)) (k : Nat) (i : Fin rs.length) : Prop :=
  eventAt rs .insert i ∈ (events rs).take k ∧
    eventAt rs .delete i ∉ (events rs).take k

theorem active_iff_positions (rs : List (Rectangle α β)) (k : Nat)
    (i : Fin rs.length) :
    Active rs k i ↔ (position rs .insert i).val < k ∧ k ≤ (position rs .delete i).val := by
  simp only [Active, eventAt_mem_take_iff, not_lt]

@[simp] theorem not_active_zero (rs : List (Rectangle α β)) (i : Fin rs.length) :
    ¬ Active rs 0 i := by
  simp [Active]

theorem not_active_of_length_le (rs : List (Rectangle α β)) {k : Nat}
    (hk : (events rs).length ≤ k) (i : Fin rs.length) : ¬ Active rs k i := by
  intro h
  have hd := ((active_iff_positions rs k i).mp h).2
  exact (not_le_of_gt (position rs .delete i).isLt) (hk.trans hd)

theorem active_succ_insert (rs : List (Rectangle α β)) (p : Fin (events rs).length)
    (j : Fin rs.length) (hp : (events rs).get p = eventAt rs .insert j)
    (i : Fin rs.length) :
    Active rs (p.val + 1) i ↔ i = j ∨ Active rs p.val i := by
  rw [active_iff_positions, active_iff_positions]
  have hj := position_eq_of_get rs .insert j p hp
  by_cases hij : i = j
  · subst i
    have before : (position rs .insert j).val < (position rs .delete j).val :=
      own_positions_lt rs j
    rw [hj] at before
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      rw [hj]
      exact ⟨Nat.lt_succ_self _, Nat.succ_le_of_lt before⟩
  · have hi : (position rs .insert i).val ≠ p.val := by
      intro h
      exact position_ne_of_id_ne rs .insert .insert hij ((Fin.ext h).trans hj.symm)
    have hd : (position rs .delete i).val ≠ p.val := by
      intro h
      exact position_ne_of_id_ne rs .delete .insert hij ((Fin.ext h).trans hj.symm)
    simp only [hij, false_or]
    omega

theorem active_succ_delete (rs : List (Rectangle α β)) (p : Fin (events rs).length)
    (j : Fin rs.length) (hp : (events rs).get p = eventAt rs .delete j)
    (i : Fin rs.length) :
    Active rs (p.val + 1) i ↔ i ≠ j ∧ Active rs p.val i := by
  rw [active_iff_positions, active_iff_positions]
  have hj := position_eq_of_get rs .delete j p hp
  by_cases hij : i = j
  · subst i
    rw [hj]
    simp
  · have hi : (position rs .insert i).val ≠ p.val := by
      intro h
      exact position_ne_of_id_ne rs .insert .delete hij ((Fin.ext h).trans hj.symm)
    have hd : (position rs .delete i).val ≠ p.val := by
      intro h
      exact position_ne_of_id_ne rs .delete .delete hij ((Fin.ext h).trans hj.symm)
    constructor
    · rintro ⟨hi', hd'⟩
      exact ⟨hij, by omega, by omega⟩
    · rintro ⟨_, hi', hd'⟩
      constructor <;> omega

def activeKeys (rs : List (Rectangle α β)) (k : Nat) : Set (Key α) :=
  occurrenceKey rs '' {i | Active rs k i}

@[simp] theorem activeKeys_zero (rs : List (Rectangle α β)) : activeKeys rs 0 = ∅ := by
  ext key
  simp [activeKeys]

theorem activeKeys_empty_of_length_le (rs : List (Rectangle α β)) {k : Nat}
    (hk : (events rs).length ≤ k) : activeKeys rs k = ∅ := by
  ext key
  simp [activeKeys, not_active_of_length_le rs hk]

theorem activeKeys_succ_insert (rs : List (Rectangle α β)) (p : Fin (events rs).length)
    (j : Fin rs.length) (hp : (events rs).get p = eventAt rs .insert j) :
    activeKeys rs (p.val + 1) = insert (occurrenceKey rs j) (activeKeys rs p.val) := by
  have h : {i | Active rs (p.val + 1) i} = insert j {i | Active rs p.val i} := by
    ext i
    exact active_succ_insert rs p j hp i
  simp only [activeKeys, h, Set.image_insert_eq]

theorem activeKeys_succ_delete (rs : List (Rectangle α β)) (p : Fin (events rs).length)
    (j : Fin rs.length) (hp : (events rs).get p = eventAt rs .delete j) :
    activeKeys rs (p.val + 1) = activeKeys rs p.val \ {occurrenceKey rs j} := by
  have h : {i | Active rs (p.val + 1) i} = {i | Active rs p.val i} \ {j} := by
    ext i
    simpa only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_comm] using
      active_succ_delete rs p j hp i
  simp only [activeKeys, h, Set.image_sdiff (occurrenceKey_injective rs), Set.image_singleton]

theorem stateAfter_take_valid {ops : AbstractSet.DeleteOps (Key α) S}
    {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : AbstractSet.DeleteLaws ops observe Valid) (rs : List (Rectangle α β)) (k : Nat) :
    Valid (stateAfter ops ops.empty ((events rs).take k)) :=
  laws.execute_valid _ laws.empty_valid

theorem stateAfter_take_observe {ops : AbstractSet.DeleteOps (Key α) S}
    {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : AbstractSet.DeleteLaws ops observe Valid) (rs : List (Rectangle α β)) (k : Nat) :
    observe (stateAfter ops ops.empty ((events rs).take k)) = activeKeys rs k := by
  induction k with
  | zero =>
    rw [List.take_zero, stateAfter_nil, activeKeys_zero]
    ext key
    exact ⟨laws.empty key, False.elim⟩
  | succ k ih =>
    by_cases hk : k < (events rs).length
    · have hevent : (events rs).get ⟨k, hk⟩ ∈ events rs := List.get_mem _ _
      obtain ⟨kind, j, he⟩ := (mem_events_iff rs _).mp hevent
      rw [List.take_succ_eq_append_getElem hk, stateAfter_append, stateAfter_cons, stateAfter_nil,
        laws.step_observe _ _ (stateAfter_take_valid laws rs k), ih]
      have he' : (events rs)[k] = eventAt rs kind j := he
      rw [he']
      cases kind with
      | insert =>
        change AbstractSet.add (occurrenceKey rs j) (activeKeys rs k) = activeKeys rs (k + 1)
        rw [activeKeys_succ_insert rs ⟨k, hk⟩ j he]
        rfl
      | delete =>
        change AbstractSet.remove (occurrenceKey rs j) (activeKeys rs k) = activeKeys rs (k + 1)
        rw [activeKeys_succ_delete rs ⟨k, hk⟩ j he]
        ext key
        change (key ≠ occurrenceKey rs j ∧ key ∈ activeKeys rs k) ↔
          (key ∈ activeKeys rs k ∧ key ≠ occurrenceKey rs j)
        exact and_comm
    · have hle : (events rs).length ≤ k := Nat.le_of_not_gt hk
      have hle' : (events rs).length ≤ k + 1 := Nat.le_succ_of_le hle
      calc
        observe (stateAfter ops ops.empty ((events rs).take (k + 1))) =
            observe (stateAfter ops ops.empty ((events rs).take k)) := by
          rw [List.take_of_length_le hle, List.take_of_length_le hle']
        _ = activeKeys rs k := ih
        _ = activeKeys rs (k + 1) := by
          rw [activeKeys_empty_of_length_le rs hle, activeKeys_empty_of_length_le rs hle']

theorem query_stateAfter_take_iff {ops : AbstractSet.DeleteOps (Key α) S}
    {query : S → IntervalKey α → Bool} {observe : S → Set (Key α)} {Valid : S → Prop}
    (laws : IntervalSet.Laws ops query keyInterval observe Valid)
    (rs : List (Rectangle α β)) (k : Nat) (q : IntervalKey α) :
    query (stateAfter ops ops.empty ((events rs).take k)) q = true ↔
      ∃ i : Fin rs.length, Active rs k i ∧ (rs.get i).x.overlap q := by
  rw [laws.overlap _ (stateAfter_take_valid laws.toDeleteLaws rs k) q,
    stateAfter_take_observe laws.toDeleteLaws rs k, IntervalSet.hasOverlap_image_iff]
  constructor
  · rintro ⟨key, ⟨i, hi, rfl⟩, hq⟩
    exact ⟨i, hi, hq⟩
  · rintro ⟨i, hi, hq⟩
    exact ⟨occurrenceKey rs i, ⟨i, hi, rfl⟩, hq⟩

/-- Prefix lengths clamp at exhaustion; prior misses are an explicit hypothesis. -/
theorem sweep_eq_suffix_of_reachedMisses (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (rs : List (Rectangle α β)) (k : Nat)
    (reached : ReachedMisses ops query ops.empty ((events rs).take k)) :
    sweep ops query rs =
      scan ops query (stateAfter ops ops.empty ((events rs).take k)) ((events rs).drop k) := by
  simpa only [sweep, List.take_append_drop] using
    scan_append_of_reachedMisses ops query ops.empty ((events rs).take k)
      ((events rs).drop k) reached

end Positions
end Search.RectangleSweep
