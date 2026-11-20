import Applications.Search.RectangleSweep.Scan
import Applications.Resources.Measured
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.List.Count

/-!
# Measured execution of the early-return rectangle scan

The measured primitives return the values used by the next actual computation.
An insertion first queries the old state; a hit skips insertion and the whole
suffix. Deletion never queries. Entry is charged at each nonempty invocation,
and the terminal charge is paid only on reaching the empty suffix.

Observations need not commute. Natural-number bounds and operation counts are
separate specializations of this executor; they are not machine-time claims.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
universe u v w x y
variable {α : Type u} {β : Type v} {S : Type w} {C : Type x} {D : Type y} [LE α]

open Resources

def scanRun [Zero C] [Add C]
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C) :
    S → List (Event α β) → Measured Bool C
  | _, [] => (false, terminal)
  | s, e :: es =>
    Resources.bind ((), entry) fun _ =>
      match e.kind with
      | .insert =>
        Resources.bind (queryRun s e.x) fun hit =>
          if hit then Resources.pure true
          else Resources.bind (insertRun e.completeKey s) fun next =>
            scanRun insertRun deleteRun queryRun entry terminal next es
      | .delete =>
        Resources.bind (deleteRun e.completeKey s) fun next =>
          scanRun insertRun deleteRun queryRun entry terminal next es

@[simp] theorem scanRun_nil [Zero C] [Add C]
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C) (s : S) :
    scanRun insertRun deleteRun queryRun entry terminal s ([] : List (Event α β)) =
      (false, terminal) := rfl

theorem scanRun_insert_hit [AddZeroClass C]
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C)
    (s : S) (e : Event α β) (es : List (Event α β))
    (kind : e.kind = .insert) (hit : (queryRun s e.x).1 = true) :
    scanRun insertRun deleteRun queryRun entry terminal s (e :: es) =
      (true, entry + (queryRun s e.x).2) := by
  simp [scanRun, Resources.bind, Resources.pure, kind, hit]

theorem scanRun_insert_miss [Zero C] [Add C]
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C)
    (s : S) (e : Event α β) (es : List (Event α β))
    (kind : e.kind = .insert) (miss : (queryRun s e.x).1 = false) :
    scanRun insertRun deleteRun queryRun entry terminal s (e :: es) =
      Resources.bind ((), entry) fun _ => Resources.bind (queryRun s e.x) fun _ =>
        Resources.bind (insertRun e.completeKey s) fun next =>
          scanRun insertRun deleteRun queryRun entry terminal next es := by
  simp [scanRun, Resources.bind, kind, miss]

theorem scanRun_delete [Zero C] [Add C]
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C)
    (s : S) (e : Event α β) (es : List (Event α β)) (kind : e.kind = .delete) :
    scanRun insertRun deleteRun queryRun entry terminal s (e :: es) =
      Resources.bind ((), entry) fun _ => Resources.bind (deleteRun e.completeKey s) fun next =>
        scanRun insertRun deleteRun queryRun entry terminal next es := by
  simp [scanRun, kind]

/-- Value erasure concerns the actual callback results, without set or geometry laws. -/
theorem scanRun_value [Zero C] [Add C]
    (ops : AbstractSet.DeleteOps (Key α) S) (query : S → IntervalKey α → Bool)
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C)
    (insert_value : ∀ key state, (insertRun key state).1 = ops.insert key state)
    (delete_value : ∀ key state, (deleteRun key state).1 = ops.delete key state)
    (query_value : ∀ state interval, (queryRun state interval).1 = query state interval)
    (s : S) (es : List (Event α β)) :
    (scanRun insertRun deleteRun queryRun entry terminal s es).1 = scan ops query s es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    cases kind : e.kind <;> cases hit : query s e.x <;>
      simp [scanRun, scan, Resources.bind, Resources.pure, kind, query_value, hit,
        insert_value, delete_value, ih]

theorem scanRun_reweight [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C)
    (s : S) (es : List (Event α β)) :
    reweight h (scanRun insertRun deleteRun queryRun entry terminal s es) =
      scanRun (fun key state => reweight h (insertRun key state))
        (fun key state => reweight h (deleteRun key state))
        (fun state interval => reweight h (queryRun state interval))
        (h entry) (h terminal) s es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    have value (state : S) := congrArg Prod.fst (ih state)
    have cost (state : S) := congrArg Prod.snd (ih state)
    simp only [reweight] at value cost
    cases kind : e.kind <;> cases hit : (queryRun s e.x).1 <;>
      simp [scanRun, Resources.bind, Resources.pure, reweight, kind, hit,
        map_add, ← value, ← cost]

/-- Number of scheduled events of one kind, independent of actual early return. -/
def kindCount (kind : Kind) (es : List (Event α β)) : Nat :=
  es.countP (fun e => decide (e.kind = kind))

/-- Coordinates count queries, insertions and deletions, in that order. -/
abbrev ScanCounts := Nat × Nat × Nat

def scanCounts (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (es : List (Event α β)) :
    Measured Bool ScanCounts :=
  scanRun (fun key state => (ops.insert key state, (0, 1, 0)))
    (fun key state => (ops.delete key state, (0, 0, 1)))
    (fun state interval => (query state interval, (1, 0, 0))) 0 0 s es

@[simp] theorem scanCounts_nil (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) :
    scanCounts ops query s ([] : List (Event α β)) = (false, (0, 0, 0)) := rfl

theorem scanCounts_value (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (es : List (Event α β)) :
    (scanCounts ops query s es).1 = scan ops query s es :=
  scanRun_value ops query _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) s es

theorem scanCounts_insert_hit (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (e : Event α β) (es : List (Event α β))
    (kind : e.kind = .insert) (hit : query s e.x = true) :
    scanCounts ops query s (e :: es) = (true, (1, 0, 0)) := by
  simp [scanCounts, scanRun, Resources.bind, Resources.pure, kind, hit]

theorem scanCounts_insert_miss (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (e : Event α β) (es : List (Event α β))
    (kind : e.kind = .insert) (miss : query s e.x = false) :
    scanCounts ops query s (e :: es) =
      let r := scanCounts ops query (ops.insert e.completeKey s) es
      (r.1, (r.2.1 + 1, r.2.2.1 + 1, r.2.2.2)) := by
  simp [scanCounts, scanRun, Resources.bind, kind, miss, Prod.add_def, Nat.add_comm]

theorem scanCounts_delete (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (e : Event α β) (es : List (Event α β))
    (kind : e.kind = .delete) :
    scanCounts ops query s (e :: es) =
      let r := scanCounts ops query (ops.delete e.completeKey s) es
      (r.1, (r.2.1, r.2.2.1, r.2.2.2 + 1)) := by
  simp [scanCounts, scanRun, Resources.bind, kind, Prod.add_def, Nat.add_comm]

/-- A successful query is exactly the one query not followed by insertion. -/
theorem scanCounts_queries_eq (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (es : List (Event α β)) :
    (scanCounts ops query s es).2.1 =
      (scanCounts ops query s es).2.2.1 + if (scanCounts ops query s es).1 then 1 else 0 := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
    cases kind : e.kind with
    | insert =>
      cases hit : query s e.x with
      | false =>
        rw [scanCounts_insert_miss ops query s e es kind hit]
        have tail := ih (ops.insert e.completeKey s)
        dsimp only
        omega
      | true => rw [scanCounts_insert_hit ops query s e es kind hit]; rfl
    | delete =>
      rw [scanCounts_delete ops query s e es kind]
      exact ih (ops.delete e.completeKey s)

theorem scanCounts_le_scheduled (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (es : List (Event α β)) :
    (scanCounts ops query s es).2.1 ≤ kindCount .insert es ∧
      (scanCounts ops query s es).2.2.1 ≤ kindCount .insert es ∧
      (scanCounts ops query s es).2.2.2 ≤ kindCount .delete es := by
  induction es generalizing s with
  | nil => simp [kindCount]
  | cons e es ih =>
    cases kind : e.kind with
    | insert =>
      cases hit : query s e.x with
      | false =>
        rw [scanCounts_insert_miss ops query s e es kind hit]
        have tail := ih (ops.insert e.completeKey s)
        simpa [kindCount, kind] using tail
      | true =>
        rw [scanCounts_insert_hit ops query s e es kind hit]
        simp [kindCount, kind]
    | delete =>
      rw [scanCounts_delete ops query s e es kind]
      have tail := ih (ops.delete e.completeKey s)
      simpa [kindCount, kind] using tail

/-- Exhaustion executes every scheduled update and every insertion query. -/
theorem scanCounts_of_false (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (s : S) (es : List (Event α β))
    (exhausted : (scanCounts ops query s es).1 = false) :
    (scanCounts ops query s es).2 =
      (kindCount .insert es, kindCount .insert es, kindCount .delete es) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    cases kind : e.kind with
    | insert =>
      cases hit : query s e.x with
      | false =>
        rw [scanCounts_insert_miss ops query s e es kind hit] at exhausted ⊢
        have tail := ih (ops.insert e.completeKey s) exhausted
        simp [kindCount, kind, tail]
      | true => simp [scanCounts_insert_hit ops query s e es kind hit] at exhausted
    | delete =>
      rw [scanCounts_delete ops query s e es kind] at exhausted ⊢
      have tail := ih (ops.delete e.completeKey s) exhausted
      simp [kindCount, kind, tail]

theorem kindCount_rawEvents [LE β] (rs : List (Rectangle α β)) (kind : Kind) :
    kindCount kind (rawEvents rs) = rs.length := by
  cases kind <;> simp [kindCount, rawEvents, eventFor, List.countP_map, Function.comp_def]

theorem kindCount_events [LinearOrder β] (rs : List (Rectangle α β)) (kind : Kind) :
    kindCount kind (events rs) = rs.length := by
  change (events rs).countP _ = _
  rw [(events_perm rs).countP_eq]
  exact kindCount_rawEvents rs kind

/-- The schedule has one insertion and deletion per occurrence, even for duplicate values. -/
theorem scanCounts_events_le [LinearOrder β]
    (ops : AbstractSet.DeleteOps (Key α) S) (query : S → IntervalKey α → Bool)
    (s : S) (rs : List (Rectangle α β)) :
    (scanCounts ops query s (events rs)).2.1 ≤ rs.length ∧
      (scanCounts ops query s (events rs)).2.2.1 ≤ rs.length ∧
      (scanCounts ops query s (events rs)).2.2.2 ≤ rs.length := by
  simpa only [kindCount_events] using scanCounts_le_scheduled ops query s (events rs)

theorem scanCounts_events_of_false [LinearOrder β]
    (ops : AbstractSet.DeleteOps (Key α) S) (query : S → IntervalKey α → Bool)
    (s : S) (rs : List (Rectangle α β))
    (exhausted : (scanCounts ops query s (events rs)).1 = false) :
    (scanCounts ops query s (events rs)).2 = (rs.length, rs.length, rs.length) := by
  simpa only [kindCount_events] using scanCounts_of_false ops query s (events rs) exhausted

/-- Primitive bounds are required only for admitted keys and invariant states.
The full-schedule right side is a nonnegative envelope, not an executed-work claim. -/
theorem scanRun_cost_le [AddMonoid C] (h : C →+ Nat)
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C)
    (allowed : Key α → Prop) (Valid : S → Prop)
    (insert_closed : ∀ key state, allowed key → Valid state → Valid (insertRun key state).1)
    (delete_closed : ∀ key state, allowed key → Valid state → Valid (deleteRun key state).1)
    (queryBound insertBound deleteBound : Nat)
    (insert_bound : ∀ key state, allowed key → Valid state →
      h (insertRun key state).2 ≤ insertBound)
    (delete_bound : ∀ key state, allowed key → Valid state →
      h (deleteRun key state).2 ≤ deleteBound)
    (query_bound : ∀ key state, allowed key → Valid state →
      h (queryRun state (keyInterval key)).2 ≤ queryBound)
    (es : List (Event α β)) (inputs : ∀ e ∈ es, allowed e.completeKey)
    (s : S) (valid : Valid s) :
    h (scanRun insertRun deleteRun queryRun entry terminal s es).2 ≤
      es.length * h entry + kindCount .insert es * (queryBound + insertBound) +
        kindCount .delete es * deleteBound + h terminal := by
  induction es generalizing s with
  | nil => simp [kindCount]
  | cons e es ih =>
    have admitted := inputs e List.mem_cons_self
    have tail_inputs : ∀ a ∈ es, allowed a.completeKey :=
      fun a inside => inputs a (List.mem_cons_of_mem e inside)
    cases kind : e.kind with
    | insert =>
      have query_cost := query_bound e.completeKey s admitted valid
      change h (queryRun s e.x).2 ≤ queryBound at query_cost
      cases hit : (queryRun s e.x).1 with
      | false =>
        have insert_cost := insert_bound e.completeKey s admitted valid
        have tail := ih tail_inputs (insertRun e.completeKey s).1
          (insert_closed e.completeKey s admitted valid)
        simp [scanRun, Resources.bind, kind, hit, map_add, kindCount, Nat.add_mul] at tail ⊢
        omega
      | true =>
        simp [scanRun, Resources.bind, Resources.pure, kind, hit, map_add,
          kindCount, Nat.add_mul]
        omega
    | delete =>
      have delete_cost := delete_bound e.completeKey s admitted valid
      have tail := ih tail_inputs (deleteRun e.completeKey s).1
        (delete_closed e.completeKey s admitted valid)
      simp [scanRun, Resources.bind, kind, map_add, kindCount, Nat.add_mul] at tail ⊢
      omega

/-- The canonical schedule supplies exactly two events and one call opportunity
of each update kind per input occurrence. Generation and sorting are not charged here. -/
theorem scanRun_events_cost_le [LinearOrder β] [AddMonoid C] (h : C →+ Nat)
    (insertRun deleteRun : Key α → S → Measured S C)
    (queryRun : S → IntervalKey α → Measured Bool C) (entry terminal : C)
    (allowed : Key α → Prop) (Valid : S → Prop)
    (insert_closed : ∀ key state, allowed key → Valid state → Valid (insertRun key state).1)
    (delete_closed : ∀ key state, allowed key → Valid state → Valid (deleteRun key state).1)
    (queryBound insertBound deleteBound : Nat)
    (insert_bound : ∀ key state, allowed key → Valid state →
      h (insertRun key state).2 ≤ insertBound)
    (delete_bound : ∀ key state, allowed key → Valid state →
      h (deleteRun key state).2 ≤ deleteBound)
    (query_bound : ∀ key state, allowed key → Valid state →
      h (queryRun state (keyInterval key)).2 ≤ queryBound)
    (rs : List (Rectangle α β)) (inputs : ∀ e ∈ events rs, allowed e.completeKey)
    (s : S) (valid : Valid s) :
    h (scanRun insertRun deleteRun queryRun entry terminal s (events rs)).2 ≤
      2 * rs.length * h entry + rs.length * (queryBound + insertBound) +
        rs.length * deleteBound + h terminal := by
  simpa only [length_events, kindCount_events] using
    scanRun_cost_le h insertRun deleteRun queryRun entry terminal allowed Valid
      insert_closed delete_closed queryBound insertBound deleteBound
      insert_bound delete_bound query_bound (events rs) inputs s valid

/-- Exact constant tariffs count only performed primitives and visited events.
A terminal charge occurs precisely on exhaustion, including the empty input. -/
theorem scanRun_constant_cost (ops : AbstractSet.DeleteOps (Key α) S)
    (query : S → IntervalKey α → Bool) (queryCost insertCost deleteCost entry terminal : Nat)
    (s : S) (es : List (Event α β)) :
    (scanRun (fun key state => (ops.insert key state, insertCost))
      (fun key state => (ops.delete key state, deleteCost))
      (fun state interval => (query state interval, queryCost)) entry terminal s es).2 =
      let r := scanCounts ops query s es
      r.2.1 * queryCost + r.2.2.1 * insertCost + r.2.2.2 * deleteCost +
        (r.2.1 + r.2.2.2) * entry + if r.1 then 0 else terminal := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
    cases kind : e.kind with
    | insert =>
      cases hit : query s e.x with
      | false =>
        rw [scanCounts_insert_miss ops query s e es kind hit]
        simp only [scanRun, Resources.bind, kind, hit, Bool.false_eq_true,
          ↓reduceIte]
        rw [ih]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      | true =>
        rw [scanCounts_insert_hit ops query s e es kind hit]
        simp [scanRun, Resources.bind, Resources.pure, kind, hit, Nat.add_comm]
    | delete =>
      rw [scanCounts_delete ops query s e es kind]
      simp only [scanRun, Resources.bind, kind]
      rw [ih]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

end Search.RectangleSweep
