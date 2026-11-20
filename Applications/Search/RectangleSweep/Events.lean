import Applications.Search.Rectangle
import Applications.Sorting.SourceMergeSort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

/-!
# Occurrence-preserving rectangle events

The generator shares an indexed input and carries each x interval directly.
The actual source merge sort compares `(y, (kind rank, occurrence ID))`, putting
every insertion before every deletion at a shared ordinate. Sorting does not
inspect the x payload, and raw event keys need not identify whole events.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
open Applications.Sorting
universe u v

inductive Kind where
  | insert
  | delete
  deriving DecidableEq

def Kind.rank : Kind → Nat
  | .insert => 0
  | .delete => 1

theorem Kind.rank_injective : Function.Injective Kind.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [Kind.rank]

structure Event (α : Type u) (β : Type v) [LE α] where
  y : β
  x : IntervalKey α
  kind : Kind
  id : Nat

namespace Event
variable {α : Type u} {β : Type v} [LE α]

def identity (e : Event α β) : Kind × Nat := (e.kind, e.id)

def key (e : Event α β) : β ×ₗ (Nat ×ₗ Nat) :=
  toLex (e.y, toLex (e.kind.rank, e.id))

theorem identity_eq_of_key_eq {e f : Event α β} (h : e.key = f.key) :
    e.identity = f.identity := by
  apply Prod.ext
  · apply Kind.rank_injective
    exact congrArg (fun k : β ×ₗ (Nat ×ₗ Nat) => (ofLex (ofLex k).2).1) h
  · exact congrArg (fun k : β ×ₗ (Nat ×ₗ Nat) => (ofLex (ofLex k).2).2) h

theorem y_le_of_key_le [LinearOrder β] {e f : Event α β} (h : e.key ≤ f.key) :
    e.y ≤ f.y := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · exact h.le
  · exact h.1.le

/-- Rank is compared before ID, so this law has no relation between the IDs. -/
theorem insert_key_lt_delete [LinearOrder β] {e f : Event α β}
    (he : e.kind = .insert) (hf : f.kind = .delete) (hy : e.y ≤ f.y) :
    e.key < f.key := by
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases lt_or_eq_of_le hy with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, Prod.Lex.toLex_lt_toLex.mpr (Or.inl ?_)⟩
    simp [he, hf, Kind.rank]

end Event

variable {α : Type u} {β : Type v}

section Generation
variable [LE α] [LE β]

def eventFor (r : Rectangle α β) (kind : Kind) (id : Nat) : Event α β where
  y := match kind with | .insert => r.y.low | .delete => r.y.high
  x := r.x
  kind := kind
  id := id

/-- A total specification lookup, separate from the executable linear generator. -/
def eventAt (rs : List (Rectangle α β)) (kind : Kind) (i : Fin rs.length) : Event α β :=
  eventFor (rs.get i) kind i.val

@[simp] theorem identity_eventAt (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) : (eventAt rs kind i).identity = (kind, i.val) := rfl

def rawEvents (rs : List (Rectangle α β)) : List (Event α β) :=
  let indexed := rs.zipIdx
  indexed.map (fun p => eventFor p.1 .insert p.2) ++
    indexed.map (fun p => eventFor p.1 .delete p.2)

@[simp] theorem rawEvents_nil : rawEvents ([] : List (Rectangle α β)) = [] := rfl

theorem length_rawEvents (rs : List (Rectangle α β)) :
    (rawEvents rs).length = 2 * rs.length := by
  simp [rawEvents, Nat.two_mul]

theorem eventAt_mem_rawEvents (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) : eventAt rs kind i ∈ rawEvents rs := by
  have hi : (rs.get i, i.val) ∈ rs.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simp
  cases kind with
  | insert => exact List.mem_append_left _ (List.mem_map.mpr ⟨_, hi, rfl⟩)
  | delete => exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hi, rfl⟩)

theorem mem_rawEvents_iff (rs : List (Rectangle α β)) (e : Event α β) :
    e ∈ rawEvents rs ↔ ∃ kind, ∃ i : Fin rs.length, e = eventAt rs kind i := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_map.mp h with ⟨⟨r, n⟩, hn, he⟩
      obtain ⟨hn', hr⟩ := List.mem_zipIdx' hn
      refine ⟨.insert, ⟨n, hn'⟩, ?_⟩
      change e = eventFor rs[n] .insert n
      simpa only [← hr] using he.symm
    · rcases List.mem_map.mp h with ⟨⟨r, n⟩, hn, he⟩
      obtain ⟨hn', hr⟩ := List.mem_zipIdx' hn
      refine ⟨.delete, ⟨n, hn'⟩, ?_⟩
      change e = eventFor rs[n] .delete n
      simpa only [← hr] using he.symm
  · rintro ⟨kind, i, rfl⟩
    exact eventAt_mem_rawEvents rs kind i

theorem id_lt_of_mem_rawEvents {rs : List (Rectangle α β)} {e : Event α β}
    (he : e ∈ rawEvents rs) : e.id < rs.length := by
  rcases (mem_rawEvents_iff rs e).mp he with ⟨kind, i, rfl⟩
  exact i.isLt

theorem eq_eventAt_of_mem_rawEvents {rs : List (Rectangle α β)} {e : Event α β}
    (he : e ∈ rawEvents rs) :
    e = eventAt rs e.kind ⟨e.id, id_lt_of_mem_rawEvents he⟩ := by
  rcases (mem_rawEvents_iff rs e).mp he with ⟨kind, i, rfl⟩
  rfl

theorem map_identity_generated (rs : List (Rectangle α β)) (kind : Kind) :
    (rs.zipIdx.map (fun p => eventFor p.1 kind p.2)).map Event.identity =
      (List.range rs.length).map (Prod.mk kind) := by
  simp only [List.map_map]
  change rs.zipIdx.map (fun p => (kind, p.2)) = _
  have h := List.zipIdx_map_snd 0 rs
  rw [← List.range_eq_range'] at h
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map (Prod.mk kind)) h

theorem rawEvents_identities (rs : List (Rectangle α β)) :
    (rawEvents rs).map Event.identity =
      (List.range rs.length).map (Prod.mk Kind.insert) ++
        (List.range rs.length).map (Prod.mk Kind.delete) := by
  unfold rawEvents
  rw [List.map_append, map_identity_generated, map_identity_generated]

theorem rawEvents_ids (rs : List (Rectangle α β)) :
    (rawEvents rs).map Event.id = List.range rs.length ++ List.range rs.length := by
  have h := congrArg (List.map Prod.snd) (rawEvents_identities rs)
  simpa [List.map_map, Function.comp_def, Event.identity] using h

theorem mem_rawEvents_identities (rs : List (Rectangle α β)) (kind : Kind) (id : Nat) :
    (kind, id) ∈ (rawEvents rs).map Event.identity ↔ id < rs.length := by
  rw [rawEvents_identities]
  cases kind <;> simp

theorem rawEvents_identities_nodup (rs : List (Rectangle α β)) :
    ((rawEvents rs).map Event.identity).Nodup := by
  rw [rawEvents_identities, List.nodup_append]
  have hn (kind : Kind) : ((List.range rs.length).map (Prod.mk kind)).Nodup :=
    List.nodup_range.map (fun _ _ h => congrArg Prod.snd h)
  refine ⟨hn .insert, hn .delete, ?_⟩
  intro x hx y hy hxy
  rcases List.mem_map.mp hx with ⟨i, _, hi⟩
  rcases List.mem_map.mp hy with ⟨j, _, hj⟩
  have h : Kind.insert = Kind.delete := congrArg Prod.fst (hi.trans (hxy.trans hj.symm))
  cases h

theorem rawEvents_nodup (rs : List (Rectangle α β)) : (rawEvents rs).Nodup :=
  (rawEvents_identities_nodup rs).of_map

theorem eq_of_identity_eq_of_mem_rawEvents {rs : List (Rectangle α β)}
    {e f : Event α β} (he : e ∈ rawEvents rs) (hf : f ∈ rawEvents rs)
    (h : e.identity = f.identity) : e = f :=
  List.inj_on_of_nodup_map (rawEvents_identities_nodup rs) he hf h

theorem count_identity_rawEvents (rs : List (Rectangle α β)) (kind : Kind) (id : Nat) :
    ((rawEvents rs).map Event.identity).count (kind, id) =
      if id < rs.length then 1 else 0 := by
  rw [(rawEvents_identities_nodup rs).count]
  simp only [mem_rawEvents_identities]

theorem count_id_rawEvents (rs : List (Rectangle α β)) (id : Nat) :
    ((rawEvents rs).map Event.id).count id = if id < rs.length then 2 else 0 := by
  rw [rawEvents_ids, List.count_append]
  by_cases h : id < rs.length <;> simp [List.count_range, h]

end Generation

section Sorting
variable [LE α] [LinearOrder β]

def sortEvents (es : List (Event α β)) : List (Event α β) :=
  SourceMergeSort.sortOn Event.key es

theorem sortEvents_sorted (es : List (Event α β)) : KeySorted Event.key (sortEvents es) :=
  (SourceMergeSort.sortOn_correct Event.key es).1

theorem sortEvents_perm (es : List (Event α β)) : (sortEvents es).Perm es :=
  (SourceMergeSort.sortOn_correct Event.key es).2

/-- One event generation and one sort, ready for a later scan of the returned list. -/
def events (rs : List (Rectangle α β)) : List (Event α β) := sortEvents (rawEvents rs)

theorem events_sorted (rs : List (Rectangle α β)) : KeySorted Event.key (events rs) :=
  sortEvents_sorted _

theorem events_perm (rs : List (Rectangle α β)) : (events rs).Perm (rawEvents rs) :=
  sortEvents_perm _

@[simp] theorem events_nil : events ([] : List (Rectangle α β)) = [] := by
  simp [events, sortEvents, SourceMergeSort.sortOn]

theorem length_events (rs : List (Rectangle α β)) : (events rs).length = 2 * rs.length :=
  (events_perm rs).length_eq.trans (length_rawEvents rs)

theorem mem_events_iff (rs : List (Rectangle α β)) (e : Event α β) :
    e ∈ events rs ↔ ∃ kind, ∃ i : Fin rs.length, e = eventAt rs kind i :=
  (events_perm rs).mem_iff.trans (mem_rawEvents_iff rs e)

theorem eventAt_mem_events (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) : eventAt rs kind i ∈ events rs :=
  (mem_events_iff rs _).mpr ⟨kind, i, rfl⟩

theorem id_lt_of_mem_events {rs : List (Rectangle α β)} {e : Event α β}
    (he : e ∈ events rs) : e.id < rs.length :=
  id_lt_of_mem_rawEvents ((events_perm rs).mem_iff.mp he)

theorem eq_eventAt_of_mem_events {rs : List (Rectangle α β)} {e : Event α β}
    (he : e ∈ events rs) : e = eventAt rs e.kind ⟨e.id, id_lt_of_mem_events he⟩ :=
  eq_eventAt_of_mem_rawEvents ((events_perm rs).mem_iff.mp he)

theorem events_identities_nodup (rs : List (Rectangle α β)) :
    ((events rs).map Event.identity).Nodup :=
  ((events_perm rs).map Event.identity).nodup_iff.mpr (rawEvents_identities_nodup rs)

theorem events_nodup (rs : List (Rectangle α β)) : (events rs).Nodup :=
  (events_perm rs).nodup_iff.mpr (rawEvents_nodup rs)

theorem count_identity_events (rs : List (Rectangle α β)) (kind : Kind) (id : Nat) :
    ((events rs).map Event.identity).count (kind, id) = if id < rs.length then 1 else 0 :=
  ((events_perm rs).map Event.identity).count_eq (kind, id) |>.trans
    (count_identity_rawEvents rs kind id)

theorem count_id_events (rs : List (Rectangle α β)) (id : Nat) :
    ((events rs).map Event.id).count id = if id < rs.length then 2 else 0 :=
  ((events_perm rs).map Event.id).count_eq id |>.trans (count_id_rawEvents rs id)

theorem eq_of_key_eq_of_mem_events {rs : List (Rectangle α β)} {e f : Event α β}
    (he : e ∈ events rs) (hf : f ∈ events rs) (h : e.key = f.key) : e = f :=
  eq_of_identity_eq_of_mem_rawEvents ((events_perm rs).mem_iff.mp he)
    ((events_perm rs).mem_iff.mp hf) (Event.identity_eq_of_key_eq h)

theorem existsUnique_position (rs : List (Rectangle α β)) (kind : Kind)
    (i : Fin rs.length) : ∃! p : Fin (events rs).length, (events rs).get p = eventAt rs kind i := by
  obtain ⟨p, hp⟩ := List.mem_iff_get.mp (eventAt_mem_events rs kind i)
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact (events_nodup rs).injective_get (hq.trans hp.symm)

/-- A strict key comparison determines order of actual positions in a sorted list. -/
theorem position_lt_of_key_lt {es : List (Event α β)} (hs : KeySorted Event.key es)
    (p q : Fin es.length) (h : (es.get p).key < (es.get q).key) : p < q := by
  by_contra hpq
  rcases lt_or_eq_of_le (le_of_not_gt hpq) with hqp | hqp
  · exact (not_lt_of_ge (hs.rel_get_of_lt hqp)) h
  · subst q
    exact (lt_irrefl _) h

theorem insert_position_lt_delete {es : List (Event α β)} (hs : KeySorted Event.key es)
    (p q : Fin es.length) (hp : (es.get p).kind = .insert)
    (hq : (es.get q).kind = .delete) (hy : (es.get p).y ≤ (es.get q).y) : p < q :=
  position_lt_of_key_lt hs p q (Event.insert_key_lt_delete hp hq hy)

/-- Includes zero-height rectangles; the endpoint bound is weak. -/
theorem own_insert_position_lt_delete (rs : List (Rectangle α β)) (i : Fin rs.length)
    (p q : Fin (events rs).length) (hp : (events rs).get p = eventAt rs .insert i)
    (hq : (events rs).get q = eventAt rs .delete i) : p < q := by
  apply insert_position_lt_delete (events_sorted rs) p q
  · rw [hp]; rfl
  · rw [hq]; rfl
  · rw [hp, hq]
    exact (rs.get i).y.low_le_high

/-- This global tie property is stronger than every occurrence's own order. -/
def InsertionsFirst (es : List (Event α β)) : Prop :=
  ∀ p q : Fin es.length, (es.get p).kind = .insert → (es.get q).kind = .delete →
    (es.get p).y = (es.get q).y → p < q

theorem events_insertionsFirst (rs : List (Rectangle α β)) : InsertionsFirst (events rs) := by
  intro p q hp hq hy
  exact insert_position_lt_delete (events_sorted rs) p q hp hq hy.le

end Sorting
end Search.RectangleSweep
