import Applications.Search.RectangleSweep.Events
import Applications.Search.AbstractSet.Deletion

/-!
# A terminating scan of carried rectangle events

Complete keys retain the occurrence identifier after interval projection. The
raw scan queries before insertion and returns immediately on a hit. Its prefix
fold describes every mathematical prefix; `ReachedMisses` identifies prefixes
through which the scan actually continues.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
universe u v w
variable {α : Type u} {β : Type v} {S : Type w} [LE α]

abbrev Key (α : Type u) [LE α] := IntervalKey α ×ₗ Nat

def keyInterval (key : Key α) : IntervalKey α := (ofLex key).1

def Event.completeKey (e : Event α β) : Key α := toLex (e.x, e.id)

@[simp] theorem keyInterval_completeKey (e : Event α β) :
    keyInterval e.completeKey = e.x := rfl

def Event.update (e : Event α β) : AbstractSet.Update (Key α) :=
  match e.kind with
  | .insert => .insert e.completeKey
  | .delete => .delete e.completeKey

def stateAfter (ops : AbstractSet.DeleteOps (Key α) S) (s : S)
    (es : List (Event α β)) : S :=
  AbstractSet.execute ops (es.map Event.update) s

@[simp] theorem stateAfter_nil (ops : AbstractSet.DeleteOps (Key α) S) (s : S) :
    stateAfter ops s ([] : List (Event α β)) = s := rfl

@[simp] theorem stateAfter_cons (ops : AbstractSet.DeleteOps (Key α) S) (s : S)
    (e : Event α β) (es : List (Event α β)) :
    stateAfter ops s (e :: es) = stateAfter ops (AbstractSet.step ops s e.update) es := rfl

theorem stateAfter_append (ops : AbstractSet.DeleteOps (Key α) S) (s : S)
    (pre suffix : List (Event α β)) :
    stateAfter ops s (pre ++ suffix) = stateAfter ops (stateAfter ops s pre) suffix := by
  simp only [stateAfter, List.map_append, AbstractSet.execute, List.foldl_append]

def scan (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) : S → List (Event α β) → Bool
  | _, [] => false
  | s, e :: es =>
    match e.kind with
    | .insert =>
      if query s e.x then true else scan ops query (ops.insert e.completeKey s) es
    | .delete => scan ops query (ops.delete e.completeKey s) es

@[simp] theorem scan_nil (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) :
    scan ops query s ([] : List (Event α β)) = false := rfl

/-- A later disjunct need not be visited when the head query already succeeds. -/
theorem scan_cons_eq_true_iff (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (e : Event α β)
    (es : List (Event α β)) :
    scan ops query s (e :: es) = true ↔
      (e.kind = .insert ∧ query s e.x = true) ∨
        scan ops query (AbstractSet.step ops s e.update) es = true := by
  cases hk : e.kind <;> cases hq : query s e.x <;>
    simp [scan, Event.update, AbstractSet.step, hk, hq]

/-- The existential witness is a mathematical full-prefix query, not a trace. -/
theorem scan_eq_true_iff (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (es : List (Event α β)) :
    scan ops query s es = true ↔
      ∃ p : Fin es.length, (es.get p).kind = .insert ∧
        query (stateAfter ops s (es.take p.val)) (es.get p).x = true := by
  induction es generalizing s with
  | nil => simp [scan]
  | cons e es ih =>
    rw [scan_cons_eq_true_iff, ih]
    constructor
    · rintro (⟨hk, hq⟩ | ⟨p, hk, hq⟩)
      · exact ⟨⟨0, by simp⟩, hk, hq⟩
      · refine ⟨p.succ, hk, ?_⟩
        simpa only [Fin.val_succ, List.take_succ_cons, stateAfter_cons,
          List.get_cons_succ'] using hq
    · rintro ⟨⟨k, hk⟩, hkind, hquery⟩
      cases k with
      | zero => exact Or.inl ⟨hkind, hquery⟩
      | succ k =>
        refine Or.inr ⟨⟨k, by simpa using hk⟩, hkind, ?_⟩
        simpa only [List.take_succ_cons, stateAfter_cons, List.get_cons_succ] using hquery

/-- Every insertion in this prefix misses at its successive pre-update state. -/
def ReachedMisses (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) : S → List (Event α β) → Prop
  | _, [] => True
  | s, e :: es =>
    (e.kind = .insert → query s e.x = false) ∧
      ReachedMisses ops query (AbstractSet.step ops s e.update) es

theorem scan_eq_false_iff_reachedMisses (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (es : List (Event α β)) :
    scan ops query s es = false ↔ ReachedMisses ops query s es := by
  induction es generalizing s with
  | nil => simp [scan, ReachedMisses]
  | cons e es ih =>
    cases hk : e.kind <;> cases hq : query s e.x <;>
      simp [scan, ReachedMisses, Event.update, AbstractSet.step, hk, hq, ih]

/-- Continuing through a prefix executes exactly its full update fold. -/
theorem scan_append_of_reachedMisses (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (pre suffix : List (Event α β))
    (reached : ReachedMisses ops query s pre) :
    scan ops query s (pre ++ suffix) = scan ops query (stateAfter ops s pre) suffix := by
  induction pre generalizing s with
  | nil => rfl
  | cons e pre ih =>
    have htail := ih _ reached.2
    cases hk : e.kind with
    | insert =>
      have hq := reached.1 hk
      simpa [scan, hk, hq, Event.update, AbstractSet.step] using htail
    | delete =>
      simpa [scan, hk, Event.update, AbstractSet.step] using htail

def sweep [LinearOrder β] (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (rs : List (Rectangle α β)) : Bool :=
  let schedule := events rs
  scan ops query ops.empty schedule

end Search.RectangleSweep
