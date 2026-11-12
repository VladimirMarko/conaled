import Applications.FRP.RegionalPendingInternal
import Applications.FRP.RegionalPendingSafety

/-! Finite scheduled draining. The scheduler stops fresh admission, retries and
queries while retiring existing references; preparation must first finish. -/
namespace FRPSpec.Regional.Pending

/-- Both ownership stores are physically bounded, including replies generated
by dispatch. This rank counts traffic, not business computations. -/
def traffic (s : Active) : Nat :=
  PendingMigration.trafficRank s.protocol.queue + s.deliveries.rank

theorem traffic_bound (s : Active) : traffic s ≤ 10 := by
  have := PendingMigration.rank_bound s.protocol.queue
  have := delivery_bound s.deliveries
  unfold traffic
  omega

/-- The wrapper dispatch invokes the accepted public protocol operation. -/
theorem external_dispatch (s : Session) (reply : Bool) (h : s.prepared = none)
    (hp : s.active.protocol.prepared = none) :
    (external s (.dispatch reply)).session.active.protocol =
      (PendingMigration.dispatch s.active.protocol reply).session := by
  simp [external,h,PendingMigration.step,hp]
  split <;> simp_all [Active.withResiduals,updateResidual]
  repeat' first | rfl | split

def preparedFlag (s : Session) : Bool := s.prepared.isSome

theorem external_unprepared (s : Session) (reply : Bool)
    (h : s.prepared = none) : (external s (.dispatch reply)).session.prepared = none := by
  have result : preparedFlag (external s (.dispatch reply)).session = false := by
    simp only [external,h,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    simp_all [preparedFlag]
  simpa [preparedFlag] using result

def drainExternal : Nat → Session → Session
  | 0,s => s
  | n+1,s => drainExternal n (external s (.dispatch true)).session

theorem drain_public (n : Nat) (s : Session) :
    (execute s (List.replicate n (.external (.dispatch true)))).1 = drainExternal n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,execute,step,drainExternal] using ih (external s (.dispatch true)).session

theorem drain_protocol (n : Nat) (s : Session) (h : s.prepared = none)
    (hp : s.active.protocol.prepared = none) :
    (drainExternal n s).active.protocol = PendingMigration.drain n s.active.protocol := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [drainExternal,PendingMigration.drain]
    rw [ih _ (external_unprepared s _ h)]
    · rw [external_dispatch s true h hp]
    · rw [external_dispatch s true h hp]
      simpa [PendingMigration.preparedFlag] using PendingMigration.dispatch_unprepared s.active.protocol true hp

theorem external_drained (s : Session) (h : s.prepared = none)
    (hp : s.active.protocol.prepared = none) (slot : Bool) :
    (drainExternal 8 s).active.protocol.queue.references slot = false := by
  rw [drain_protocol 8 s h hp]
  simp [PendingMigration.Queue.references,PendingMigration.eight_dispatches_drain]

theorem public_external_drained (s : Session) (h : s.prepared = none)
    (hp : s.active.protocol.prepared = none) (slot : Bool) :
    (execute s (List.replicate 8 (.external (.dispatch true)))).1.active.protocol.queue.references slot = false := by
  rw [drain_public]
  exact external_drained s h hp slot

/-- Internal delivery can only stall on an uncomputed cache. Reachable producer
work supplies a cache, while cancellation permits draining without computing. -/
def Deliverable (s : Active) : Prop := ∀ slot r,
  (s.deliveries.d = some slot ∨ s.deliveries.n = some slot) →
  s.residuals.get slot = some r → r.cached.isSome = true ∨ r.cancelled = true

theorem deliver_clears (s : Session) (toD : Bool) (h : s.prepared = none)
    (ready : Deliverable s.active) :
    (if toD then (deliver s toD).session.active.deliveries.d
      else (deliver s toD).session.active.deliveries.n) = none := by
  cases toD <;> simp only [deliver,h,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  all_goals
    split
    · simp_all [reject]
    · rename_i slot cell
      split
      · rfl
      · rename_i localState localEq
        have hr := ready slot localState (by simp_all) localEq
        split
        · rfl
        · cases cached : localState.cached <;> simp_all [updateResidual,Active.withResiduals]

theorem invariant_deliverable (s : Active) (hs : Invariant s) : Deliverable s := by
  intro slot r href hr
  have ref : s.deliveries.references slot = true := by
    rcases href with h | h <;> simp [Deliveries.references,h]
  obtain ⟨request,localState,_,hl,hc,_⟩ := hs.delivery slot ref
  have eq := Option.some.inj (hr.symm.trans hl)
  subst localState
  exact Or.inl hc

theorem deliver_unprepared (s : Session) (d : Bool) (hp : s.prepared = none) :
    (deliver s d).session.prepared = none := by
  have result : preparedFlag (deliver s d).session = false := by
    unfold deliver
    rw [hp]
    cases d <;> dsimp only
    all_goals repeat' first | rfl | split | dsimp only
    all_goals simp [preparedFlag,reject,hp]
  simpa [preparedFlag] using result

theorem deliver_other (s : Session) (d : Bool) :
    (if d then (deliver s d).session.active.deliveries.n
      else (deliver s d).session.active.deliveries.d) =
    (if d then s.active.deliveries.n else s.active.deliveries.d) := by
  cases d <;> unfold deliver
  all_goals repeat' first | rfl | split | dsimp only

/-- Two actual internal dispatch opportunities remove both owned references;
this includes cancellation without running either consumer. -/
theorem two_internal_deliveries (s : Session) (hp : s.prepared = none) (hs : Invariant s.active) :
    (execute s [.deliverD,.deliverN]).1.active.deliveries = {} := by
  have hd := deliver_clears s true hp (invariant_deliverable s.active hs)
  let next := (deliver s true).session
  have hn := deliver_clears next false (deliver_unprepared s true hp)
    (invariant_deliverable next.active (deliver_invariant s hs true))
  have keep := deliver_other next false
  simp only [↓reduceIte] at hd
  simp only [Bool.false_eq_true,↓reduceIte] at hn keep
  change (deliver next false).session.active.deliveries = {}
  have df : (deliver next false).session.active.deliveries.d = none := keep.trans hd
  cases h : (deliver next false).session.active.deliveries
  simp_all

theorem external_dispatch_deliveries (s : Session) (reply : Bool) :
    (external s (.dispatch reply)).session.active.deliveries = s.active.deliveries := by
  unfold external
  split
  · rfl
  · dsimp only
    generalize he : PendingMigration.step s.active.protocol (.dispatch reply) = out
    simp only [show (PendingMigration.Command.dispatch reply == .release) = false from rfl,
      Bool.false_and,Bool.false_eq_true,↓reduceIte]
    cases hh : PendingMigration.head s.active.protocol with
    | none => rfl
    | some pair =>
      obtain ⟨slot,r⟩ := pair
      dsimp only
      split
      · rfl
      · split
        · cases hc : ({s.active with protocol := out.session} : Active).residuals.get slot <;> rfl
        · rfl

theorem drain_deliveries (n : Nat) (s : Session) :
    (drainExternal n s).active.deliveries = s.active.deliveries := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [drainExternal,ih,external_dispatch_deliveries]

/-- With fresh enqueues stopped, ten public opportunities retire all callback
references. Terminal/closed-route checks still govern releasing the request. -/
theorem ten_opportunities_retire_references (s : Session) (hs : Invariant s.active)
    (ready : Ready s) (slot : Bool) :
    let afterInternal := (execute s [.deliverD,.deliverN]).1
    let final := (execute afterInternal (List.replicate 8 (.external (.dispatch true)))).1
    final.active.deliveries.references slot = false ∧
      final.active.protocol.queue.references slot = false := by
  dsimp only
  let next := (execute s [.deliverD,.deliverN]).1
  have readyNext : Ready next := execute_ready s [.deliverD,.deliverN] ready (by simp [Business])
  constructor
  · rw [drain_public,drain_deliveries,two_internal_deliveries s ready.1 hs]
    rfl
  · exact public_external_drained next readyNext.1 readyNext.2 slot

end FRPSpec.Regional.Pending
