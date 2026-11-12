import Applications.FRP.RegionalPendingInternal
import Applications.FRP.RegionalPendingSafety
import Applications.FRP.RegionalPendingProtocol

/-! Reachable joint source semantics across changed-cut execution. -/
namespace FRPSpec.Regional.Pending
set_option backward.dsimp.instances true

 theorem checkpoint_wire (a b : Active) (h : wire a = wire b) :
    PendingMigration.checkpoint a.protocol = PendingMigration.checkpoint b.protocol := by
  have hl := congrArg Wire.logical h
  have hr := congrArg Wire.requests h
  have hp := congrArg Wire.peer h
  have ho := congrArg Wire.order h
  have hq := congrArg Wire.external h
  simp only [wire] at hl hr hp ho hq
  unfold PendingMigration.checkpoint
  congr 1
  cases hqa : a.protocol.queue; cases hqb : b.protocol.queue
  simp_all

 theorem projection_checkpoint_wire (a b : Active) (h : wire a = wire b) :
    PendingMigration.checkpoint (delayProjection a.protocol) =
      PendingMigration.checkpoint (delayProjection b.protocol) := by
  have hh := checkpoint_wire a b h
  have hl := congrArg PendingMigration.Checkpoint.logical hh
  have hr := congrArg PendingMigration.Checkpoint.requests hh
  have hp := congrArg PendingMigration.Checkpoint.peer hh
  have ho := congrArg PendingMigration.Checkpoint.order hh
  have hq := congrArg PendingMigration.Checkpoint.queue hh
  simp only [PendingMigration.checkpoint] at hl hr hp ho hq
  simp only [PendingMigration.checkpoint,delayProjection,ownerInput,hl,hr,hp,ho,hq]

 theorem source_wire (a b : Active) (h : wire a = wire b) : source a = source b :=
  source_of_protocol_source a b (PendingMigration.checkpoint_source (checkpoint_wire a b h))

 theorem invariant_wire (a b : Active) (h : wire a = wire b) (ha : Invariant a) : Invariant b := by
  have hl := congrArg Wire.logical h
  have hr := congrArg Wire.requests h
  have ho := congrArg Wire.order h
  have hd := congrArg Wire.deliveries h
  have hc := congrArg Wire.residuals h
  simp only [wire] at hl hr ho hd hc
  constructor
  · exact PendingMigration.checkpoint_valid (projection_checkpoint_wire a b h) ha.protocol
  · simpa only [hr,hc] using ha.residual
  · simpa only [hr,hc,hl] using ha.current
  · simpa only [hr,hc,hd] using ha.delivery
  · simpa only [hr,hc] using ha.cancellation
  · simpa only [ho,hc] using ha.cache_head
  · simpa only [hc] using ha.completed_cache

theorem control_refines (s : Session) (c : Command) (hc : ¬ Business c) :
    SourceStep (source s.active) (step s c) (source (step s c).session.active) := by
  cases c <;> simp only [Business,not_true_eq_false] at hc
  case prepare e t k r a v bad =>
    have hw : source (prepare s e t k r a v bad).session.active = source s.active := by
      rw [prepare_preserves]
    change SourceStep (source s.active) (prepare s e t k r a v bad)
      (source (prepare s e t k r a v bad).session.active)
    rw [hw]
    have h := prepare_silent s e t k r a v bad
    have ha := congrArg (fun x => x.1) h
    have hb := congrArg (fun x => x.2.1) h
    have hx : (prepare s e t k r a v bad).cancellation = none := congrArg (fun x => x.2.2) h
    exact .internal _ _ ha hb (by rw [hx]; decide)
  case commit =>
    change SourceStep (source s.active) (commit s) (source (commit s).session.active)
    rw [source_wire _ _ (commit_preserves s)]
    have h := commit_silent s
    exact .internal _ _ (congrArg (fun x => x.1) h) (congrArg (fun x => x.2.1) h)
      (by have hx : (commit s).cancellation = none := congrArg (fun x => x.2.2) h
          rw [hx]; decide)
  case cancel =>
    change SourceStep (source s.active) (cancel s) (source (cancel s).session.active)
    rw [cancel_preserves]
    have h := cancel_silent s
    exact .internal _ _ (congrArg (fun x => x.1) h) (congrArg (fun x => x.2.1) h)
      (by have hx : (cancel s).cancellation = none := congrArg (fun x => x.2.2) h
          rw [hx]; decide)

theorem control_invariant (s : Session) (c : Command) (hc : ¬ Business c)
    (hs : Invariant s.active) : Invariant (step s c).session.active := by
  cases c <;> simp only [Business,not_true_eq_false] at hc
  case prepare e t k r a v bad => simpa only [step,prepare_preserves] using hs
  case commit => exact invariant_wire _ _ (commit_preserves s).symm hs
  case cancel => simpa only [step,cancel_preserves] using hs

def preparedInner (s : Session) : Bool :=
  (s.prepared.map (fun p => p.target.protocol.prepared.isNone)).getD true

/-- The wrapper owns migration; no nested protocol preparation is live. -/
def InnerReady (s : Session) : Prop :=
  s.active.protocol.prepared = none ∧ preparedInner s = true

theorem business_innerReady (s : Session) (c : Command) (hc : Business c)
    (hs : InnerReady s) : InnerReady (step s c).session := by
  cases hp : s.prepared with
  | none =>
    have ready := step_ready s c hc ⟨hp,hs.1⟩
    exact ⟨ready.2,by simp [preparedInner,ready.1]⟩
  | some p =>
    rw [(prepared_freezes s c hc (by simp [hp])).1]
    exact hs

theorem prepare_innerReady (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad : Bool) (hs : InnerReady s) : InnerReady (prepare s e t k r a v bad).session := by
  refine ⟨by rw [prepare_preserves]; exact hs.1,?_⟩
  unfold prepare
  repeat' first | exact hs.2 | rfl | split | dsimp only

theorem control_innerReady (s : Session) (c : Command) (hc : ¬ Business c)
    (hs : InnerReady s) : InnerReady (step s c).session := by
  cases c <;> simp only [Business,not_true_eq_false] at hc
  case prepare e t k r a v bad => exact prepare_innerReady s e t k r a v bad hs
  case commit =>
    cases hp : s.prepared with
    | none => simpa [step,commit,hp,reject] using hs
    | some p =>
      have eq : (step s .commit).session = ⟨p.target,none,false⟩ := by
        simp only [step,commit,hp]
      rw [eq]
      refine ⟨?_,rfl⟩
      have hh := hs.2
      simpa [preparedInner,hp] using hh
  case cancel =>
    cases hp : s.prepared with
    | none => simpa [step,cancel,hp,reject] using hs
    | some p =>
      have eq : (step s .cancel).session = ⟨s.active,none,false⟩ := by
        simp only [step,cancel,hp]
      rw [eq]
      exact ⟨hs.1,rfl⟩

/-- Independent source steps account for every accepted occurrence. -/
theorem source_step_balance (before after : Source) (out : Outcome)
    (h : SourceStep before out after) :
    before.waiting.length + out.accepted.toList.length =
      after.waiting.length + out.business.toList.length +
        (if out.cancellation = some true then 1 else 0) := by
  cases h with
  | internal s o ha hb hc => simp [ha,hb,hc]
  | accept s o x ha hb hc => simp [ha,hb,hc]
  | prevent b x pre post o ha hb hc => simp [ha,hb,hc,List.length_append]; omega
  | publish b x xs o ha hb hc => simp [ha,hb,hc]

/-- A ghost execution records actual command outcomes, not an alternative evaluator. -/
inductive SourceRun : Source → List Outcome → Source → Prop where
  | nil (s : Source) : SourceRun s [] s
  | cons {a b c : Source} {out : Outcome} {outs : List Outcome} :
      SourceStep a out b → SourceRun b outs c → SourceRun a (out::outs) c

def acceptedCount (outs : List Outcome) : Nat := (outs.map (fun o => o.accepted.toList.length)).sum
def publishedCount (outs : List Outcome) : Nat := (outs.map (fun o => o.business.toList.length)).sum
def preventedCount (outs : List Outcome) : Nat :=
  (outs.map (fun o => if o.cancellation = some true then 1 else 0)).sum

theorem source_run_balance {a b : Source} {outs : List Outcome} (h : SourceRun a outs b) :
    a.waiting.length + acceptedCount outs =
      b.waiting.length + publishedCount outs + preventedCount outs := by
  induction h with
  | nil => simp [acceptedCount,publishedCount,preventedCount]
  | @cons a b c out outs h run ih =>
    have step := source_step_balance a b out h
    simp only [acceptedCount,publishedCount,preventedCount,List.map_cons,List.sum_cons] at *
    omega

theorem step_refines (s : Session) (c : Command) (hs : Invariant s.active) (hi : InnerReady s) :
    SourceStep (source s.active) (step s c) (source (step s c).session.active) := by
  by_cases business : Business c
  · cases c <;> simp only [Business] at business
    case accept x => exact accept_refines s x hs
    case producer => exact producer_refines s
    case deliverD => exact deliver_refines s true
    case deliverN => exact deliver_refines s false
    case join => exact join_refines s
    case whole => exact whole_refines s
    case external cmd => exact external_refines s cmd hs hi.1
  · exact control_refines s c business

theorem step_invariant (s : Session) (c : Command) (hs : Invariant s.active) (hi : InnerReady s) :
    Invariant (step s c).session.active := by
  by_cases business : Business c
  · cases c <;> simp only [Business] at business
    case accept x => exact accept_invariant s x hs
    case producer => exact producer_invariant s hs
    case deliverD => exact deliver_invariant s hs true
    case deliverN => exact deliver_invariant s hs false
    case join => exact join_invariant s hs
    case whole => exact whole_invariant s hs
    case external cmd => exact external_invariant s cmd hs hi.1
  · exact control_invariant s c business hs

theorem step_innerReady (s : Session) (c : Command) (hi : InnerReady s) :
    InnerReady (step s c).session := by
  by_cases business : Business c
  · exact business_innerReady s c business hi
  · exact control_innerReady s c business hi

/-- Ghost outcomes are extracted from the same step function used by public IO. -/
def outcomes : Session → List Command → List Outcome
  | _,[] => []
  | s,c::cs => let out := step s c; out :: outcomes out.session cs

theorem execute_refines (s : Session) (cs : List Command)
    (hs : Invariant s.active) (hi : InnerReady s) :
    Invariant (execute s cs).1.active ∧ InnerReady (execute s cs).1 ∧
      SourceRun (source s.active) (outcomes s cs) (source (execute s cs).1.active) := by
  induction cs generalizing s with
  | nil => exact ⟨hs,hi,.nil _⟩
  | cons c cs ih =>
    have next := ih (step s c).session (step_invariant s c hs hi) (step_innerReady s c hi)
    exact ⟨next.1,next.2.1,.cons (step_refines s c hs hi) next.2.2⟩

theorem execute_no_loss (s : Session) (cs : List Command)
    (hs : Invariant s.active) (hi : InnerReady s) :
    (source s.active).waiting.length + acceptedCount (outcomes s cs) =
      (source (execute s cs).1.active).waiting.length + publishedCount (outcomes s cs) +
        preventedCount (outcomes s cs) :=
  source_run_balance (execute_refines s cs hs hi).2.2

theorem initial_innerReady (cut : Cut) (kind : Migration.Kind) : InnerReady (initial cut kind) := by
  exact ⟨rfl,rfl⟩

/-- Arbitrary public command traces, including failed and repeated repartitioning. -/
theorem reachable_refinement (cut : Cut) (kind : Migration.Kind) (cs : List Command) :
    Invariant (execute (initial cut kind) cs).1.active ∧
      InnerReady (execute (initial cut kind) cs).1 ∧
      SourceRun (source (initial cut kind).active) (outcomes (initial cut kind) cs)
        (source (execute (initial cut kind) cs).1.active) :=
  execute_refines (initial cut kind) cs (initial_invariant cut kind) (initial_innerReady cut kind)

theorem execute_outputs (s : Session) (cs : List Command) :
    (execute s cs).2 = (outcomes s cs).flatMap (fun o => o.business.toList) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [execute,outcomes,List.flatMap_cons,ih]

/-- Every reachable accepted owner appears exactly once in admission order. -/
theorem reachable_owners (cut : Cut) (kind : Migration.Kind) (cs : List Command) :
    let p := (execute (initial cut kind) cs).1.active.protocol
    p.order.Nodup ∧ ∀ slot, slot ∈ p.order ↔ (p.requests.get slot).isSome = true := by
  have valid := (reachable_refinement cut kind cs).1.protocol
  exact ⟨valid.order,by simpa [delayProjection] using valid.occupied⟩

end FRPSpec.Regional.Pending
