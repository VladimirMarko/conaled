import Applications.FRP.PendingMigrationSafety

/-! Conditional bounded draining of the owned protocol traffic. No new enqueue
is scheduled during the drain, and no prepared copy freezes dispatch. -/
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace FRPSpec.PendingMigration

def Message.rank : Message → Nat
  | .reply _ _ => 1
  | _ => 2

def trafficRank (q : Queue) : Nat := (q.messages.map Message.rank).sum

theorem rank_positive (m : Message) : 0 < m.rank := by cases m <;> simp [Message.rank]

theorem rank_bound (q : Queue) : trafficRank q ≤ 8 := by
  have sum_bound (ms : List Message) : (ms.map Message.rank).sum ≤ 2 * ms.length := by
    induction ms with
    | nil => simp
    | cons m ms ih => cases m <;> simp_all [Message.rank] <;> omega
  have := sum_bound q.messages
  have := q.bounded
  unfold trafficRank
  omega

theorem pop_rank (q : Queue) (m : Message) (rest : Queue) (h : q.pop = some (m,rest)) :
    trafficRank q = m.rank + trafficRank rest ∧ rest.messages.length < 4 := by
  rcases q with ⟨ms,bounded⟩
  cases ms with
  | nil => simp [Queue.pop] at h
  | cons first tail =>
    simp only [Queue.pop] at h
    cases h
    constructor
    · rfl
    · change tail.length < 4; simp only [List.length_cons] at bounded; omega

theorem reply_rank (q : Queue) (slot : Bool) (answer : Reply) (h : q.messages.length < 4) :
    trafficRank ((q.push (.reply slot answer)).getD q) = trafficRank q + 1 := by
  simp [Queue.push,h,trafficRank,Message.rank,List.sum_append]

/-- Each dispatch consumes a request (rank two) or a reply (rank one). A
requested response uses the vacated queue cell and adds at most rank one. -/
theorem dispatch_decreases (s : Session) (d : Bool) (m : Message) (q : Queue)
    (hq : s.queue.pop = some (m,q)) :
    trafficRank (dispatch s d).session.queue < trafficRank s.queue := by
  have bound := pop_rank s.queue m q hq
  have positive := rank_positive m
  unfold dispatch
  rw [hq]
  dsimp only
  cases hr : s.requests.get m.slot with
  | none => simpa [reject] using (by omega : trafficRank q < trafficRank s.queue)
  | some r =>
    dsimp only
    cases ho : r.routeOpen with
    | false => simpa [ho,reject] using (by omega : trafficRank q < trafficRank s.queue)
    | true =>
      simp only [ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases m with
      | publish slot x y =>
        cases d <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        · simp only [Message.rank] at bound; omega
        · rw [reply_rank q slot _ bound.2]; simp only [Message.rank] at bound; omega
      | retry slot x y =>
        cases d <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        · simp only [Message.rank] at bound; omega
        · rw [reply_rank q slot _ bound.2]; simp only [Message.rank] at bound; omega
      | query slot =>
        cases d <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
        · simp only [Message.rank] at bound; omega
        · rw [reply_rank q slot _ bound.2]; simp only [Message.rank] at bound; omega
      | reply slot answer =>
        dsimp only
        split <;> simp only [update,reject]
        all_goals simp only [Message.rank] at bound; omega

/-- A finite scheduled drain; no admission, retries or queries are inserted. -/
def drain : Nat → Session → Session
  | 0, s => s
  | n+1, s => drain n (dispatch s true).session

theorem rank_zero_empty (q : Queue) (h : trafficRank q = 0) : q.messages = [] := by
  cases hm : q.messages with
  | nil => rfl
  | cons m ms =>
    have := rank_positive m
    simp [trafficRank,hm] at h
    omega

theorem drain_empty (fuel : Nat) (s : Session) (h : trafficRank s.queue ≤ fuel) :
    (drain fuel s).queue.messages = [] := by
  induction fuel generalizing s with
  | zero => exact rank_zero_empty s.queue (by omega)
  | succ n ih =>
    simp only [drain]
    apply ih
    cases hq : s.queue.pop with
    | none =>
      have empty : s.queue.messages = [] := by
        unfold Queue.pop at hq
        split at hq
        · assumption
        · contradiction
      simp [dispatch,hq,reject,trafficRank,empty]
    | some pair =>
      obtain ⟨m,q⟩ := pair
      have := dispatch_decreases s true m q hq
      omega

/-- Four queued requests need at most eight dispatch opportunities, including
all generated replies. This bound assumes no new traffic is enqueued. -/
theorem eight_dispatches_drain (s : Session) : (drain 8 s).queue.messages = [] :=
  drain_empty 8 s (rank_bound s.queue)

/-- The scheduled drain is the public command execution when preparation does
not freeze business commands. -/
theorem drain_public (fuel : Nat) (s : Session) (h : s.prepared = none) :
    (execute s (List.replicate fuel (.dispatch true))).1 = drain fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,execute,drain]
    have hs : step s (.dispatch true) = dispatch s true := by simp [step,h]
    rw [hs]
    apply ih
    simpa [preparedFlag] using dispatch_unprepared s true h

/-- Every kind of stale reference is absent after the public bounded drain. -/
theorem public_drain_excludes (s : Session) (h : s.prepared = none) (slot : Bool) :
    (execute s (List.replicate 8 (.dispatch true))).1.queue.references slot = false := by
  rw [drain_public 8 s h]
  simp [Queue.references,eight_dispatches_drain]

end FRPSpec.PendingMigration
