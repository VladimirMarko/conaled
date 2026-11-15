import Applications.FRP.RegionalPendingRefinement
import Applications.FRP.RegionalPendingResources

/-! Whole-wrapper service storage. Native derivations are connected to the
actual selected call and the value stored by the public wrapper transition. -/
namespace FRPSpec.Regional.Pending
open Applications.Circuits

/-- No evaluator or protocol command is called on these branches. The second
case drains an owned delivery without executing its cancelled consumer. -/
def Quiet (out : Outcome) : Prop :=
  out.events = [.inspect] ∨ out.events = [.retireInternal]

/-- Realization relates actual call arguments, native results and retained
wrapper values. A resource derivation cannot be attached to unrelated code. -/
def Realizes (s : Session) (c : Command) (out : Outcome) : ServiceCall → ServiceValue → Prop
  | .quiet,.quiet => Quiet out
  | .producer x,.scalar y => c = .producer ∧ ∃ slot r localState,
      headResidual s.active = some (slot,r,localState) ∧ r.input = x ∧
      ((out.session.active.residuals.get slot).map Residual.cached) = some (some y) ∧
      out.status = .produced
  | .delay x b,.pair y => c = .deliverD ∧ ∃ slot localState,
      s.active.deliveries.d = some slot ∧ s.active.residuals.get slot = some localState ∧
      localState.cached = some x ∧ localState.oldState = b ∧
      ((out.session.active.residuals.get slot).map Residual.dResult) = some (some y.1) ∧
      ((out.session.active.residuals.get slot).map Residual.candidate) = some (some y.2) ∧
      out.status = .deliveredD
  | .negate x,.scalar y => c = .deliverN ∧ ∃ slot localState,
      s.active.deliveries.n = some slot ∧ s.active.residuals.get slot = some localState ∧
      localState.cached = some x ∧
      ((out.session.active.residuals.get slot).map Residual.nResult) = some (some y) ∧
      out.status = .deliveredN
  | .join d n,.scalar y => c = .join ∧ ∃ slot r localState,
      headResidual s.active = some (slot,r,localState) ∧
      localState.dResult = some d ∧ localState.nResult = some n ∧
      ((out.session.active.protocol.requests.get slot).map PendingMigration.Request.output) = some y ∧
      out.status = .joined
  | .whole x b,.pair y => c = .whole ∧ ∃ slot r localState,
      headResidual s.active = some (slot,r,localState) ∧
      localState.cached = some x ∧ localState.oldState = b ∧
      ((out.session.active.protocol.requests.get slot).map PendingMigration.Request.output) = some y.1 ∧
      ((out.session.active.residuals.get slot).map Residual.candidate) = some (some y.2) ∧
      out.status = .completed
  | .protocol raw,.protocol p =>
      (c = .external raw ∨ ∃ x, c = .accept x ∧ raw = .accept x) ∧
      out.session.active.protocol = p.session ∧
      out.accepted = p.accepted ∧ out.business = p.business ∧ out.cancellation = p.cancellation
  | _,_ => False

/-- The peer/request arena is shared by old and prepared executors. Only the
new native backend and retained consumer representation coexist with it. -/
def wrapperRetained (s : Session) : Nat :=
  PendingMigration.stateSlots s.active.protocol + 16 + 4 + retainedCells s.active.cut +
    (s.prepared.map (fun p => p.target.protocol.active.cells + retainedCells p.target.cut)).getD 0

def wrapperServiceTrace (s : Session) (out : Outcome) (call : ServiceCall) : List Nat :=
  [wrapperRetained s] ++ serviceTrace s.active (serviceAllocations s.active call) ++
    [wrapperRetained out.session]

def ServiceExecution (s : Session) (c : Command) (out : Outcome) (trace : List Nat) : Prop :=
  out = step s c ∧ ∃ call,
    Realizes s c out call (serviceValue s.active call) ∧
    NativeServiceRuns s.active call (serviceValue s.active call) (serviceAllocations s.active call) ∧
    trace = wrapperServiceTrace s out call

theorem producer_realizes (s : Session) :
    ∃ call, Realizes s .producer (producer s) call (serviceValue s.active call) := by
  generalize he : producer s = out
  unfold producer at he
  split at he
  · cases he; exact ⟨.quiet,Or.inl rfl⟩
  · cases hh : headResidual s.active with
    | none => simp only [hh] at he; cases he; exact ⟨.quiet,Or.inl rfl⟩
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      simp only [hh] at he
      split at he
      · cases he; exact ⟨.quiet,Or.inl rfl⟩
      · cases he
        refine ⟨.producer r.input,rfl,slot,r,localState,hh,rfl,?_,rfl⟩
        simp [updateResidual,Active.withResiduals,Active.residuals]

theorem deliver_realizes (s : Session) (d : Bool) :
    ∃ call, Realizes s (if d then .deliverD else .deliverN) (deliver s d) call (serviceValue s.active call) := by
  generalize he : deliver s d = out
  unfold deliver at he
  split at he
  · cases he; exact ⟨.quiet,Or.inl rfl⟩
  · cases hc : (if d then s.active.deliveries.d else s.active.deliveries.n) with
    | none => simp only [hc] at he; cases he; exact ⟨.quiet,Or.inl rfl⟩
    | some slot =>
      simp only [hc] at he
      cases hl : s.active.residuals.get slot with
      | none => simp only [hl] at he; cases he; exact ⟨.quiet,Or.inr rfl⟩
      | some localState =>
        simp only [hl] at he
        split at he
        · cases he; exact ⟨.quiet,Or.inr rfl⟩
        · cases cached : localState.cached with
          | none => simp only [cached] at he; cases he; exact ⟨.quiet,Or.inl rfl⟩
          | some x =>
            simp only [cached] at he
            cases d
            · simp only [Bool.false_eq_true,↓reduceIte] at he hc ⊢
              cases he
              refine ⟨.negate x,rfl,slot,localState,hc,hl,cached,?_,rfl⟩
              simp [updateResidual,Active.withResiduals,Active.residuals,serviceValue]
            · simp only [↓reduceIte] at he hc ⊢
              cases he
              refine ⟨.delay x localState.oldState,rfl,slot,localState,hc,hl,cached,rfl,?_,?_,rfl⟩
              all_goals simp [updateResidual,Active.withResiduals,Active.residuals,serviceValue]

theorem join_realizes (s : Session) :
    ∃ call, Realizes s .join (join s) call (serviceValue s.active call) := by
  generalize he : join s = out
  unfold join at he
  split at he
  · cases he; exact ⟨.quiet,Or.inl rfl⟩
  · cases hh : headResidual s.active with
    | none => simp only [hh] at he; cases he; exact ⟨.quiet,Or.inl rfl⟩
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      simp only [hh] at he
      split at he
      · cases he; exact ⟨.quiet,Or.inl rfl⟩
      · cases hd : localState.dResult <;> cases hn : localState.nResult <;> cases hp : localState.candidate
        all_goals simp only [hd,hn,hp] at he
        all_goals try { cases he; exact ⟨.quiet,Or.inl rfl⟩ }
        rename_i d n next
        cases he
        refine ⟨.join d n,rfl,slot,r,localState,hh,hd,hn,?_,rfl⟩
        simp [PendingMigration.update,serviceValue]

theorem whole_realizes (s : Session) :
    ∃ call, Realizes s .whole (whole s) call (serviceValue s.active call) := by
  generalize he : whole s = out
  unfold whole at he
  split at he
  · cases he; exact ⟨.quiet,Or.inl rfl⟩
  · cases hh : headResidual s.active with
    | none => simp only [hh] at he; cases he; exact ⟨.quiet,Or.inl rfl⟩
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      simp only [hh] at he
      split at he
      · cases he; exact ⟨.quiet,Or.inl rfl⟩
      · cases hc : localState.cached with
        | none => simp only [hc] at he; cases he; exact ⟨.quiet,Or.inl rfl⟩
        | some x =>
          simp only [hc] at he
          cases he
          refine ⟨.whole x localState.oldState,rfl,slot,r,localState,hh,hc,rfl,?_,?_,rfl⟩
          · simp [updateResidual,Active.withResiduals,PendingMigration.update,serviceValue]
          · simp [updateResidual,Active.withResiduals,Active.residuals,serviceValue]

theorem accept_realizes (s : Session) (x : Bool) :
    ∃ call, Realizes s (.accept x) (accept s x) call (serviceValue s.active call) := by
  by_cases frozen : s.prepared.isSome = true
  · refine ⟨.quiet,Or.inl ?_⟩
    simp [accept,frozen,reject]
  · refine ⟨.protocol (.accept x),Or.inr ⟨x,rfl,rfl⟩,?_⟩
    unfold accept
    rw [ite_eq_right frozen]
    dsimp only [serviceValue]
    generalize he : PendingMigration.step s.active.protocol (.accept x) = p
    refine ⟨?_,rfl,rfl,rfl⟩
    split
    · cases p.session.order.getLast? <;> rfl
    · rfl

def serviceReleaseBlocked (s : Session) (c : PendingMigration.Command) : Bool :=
  c == .release && ((PendingMigration.head s.active.protocol
    (match c with | .cancelWork second => second | _ => false)).map
    (fun p => s.active.deliveries.references p.1)).getD false

theorem external_native_fields (s : Session) (c : PendingMigration.Command)
    (hc : ExternalCommand c) (hp : s.prepared.isSome = false)
    (hb : serviceReleaseBlocked s c = false) :
    (external s c).session.active.protocol = (PendingMigration.step s.active.protocol c).session ∧
      (external s c).accepted = (PendingMigration.step s.active.protocol c).accepted ∧
      (external s c).business = (PendingMigration.step s.active.protocol c).business ∧
      (external s c).cancellation = (PendingMigration.step s.active.protocol c).cancellation := by
  cases c <;> simp only [ExternalCommand] at hc
  all_goals try contradiction
  all_goals dsimp only [serviceReleaseBlocked] at hb
  all_goals dsimp only [external]
  all_goals simp only [hp,hb,Bool.false_eq_true,↓reduceIte]
  all_goals simp only [and_true]
  all_goals repeat' first | rfl | split | dsimp only [updateResidual,Active.withResiduals]

theorem external_realizes (s : Session) (c : PendingMigration.Command) :
    ∃ call, Realizes s (.external c) (external s c) call (serviceValue s.active call) := by
  by_cases frozen : s.prepared.isSome = true
  · refine ⟨.quiet,Or.inl ?_⟩
    simp [external,frozen,reject]
  by_cases allowed : ExternalCommand c
  · by_cases blocked : serviceReleaseBlocked s c = true
    · refine ⟨.quiet,Or.inl ?_⟩
      cases c <;> simp only [ExternalCommand] at allowed
      all_goals try contradiction
      all_goals simp only [serviceReleaseBlocked] at blocked
      all_goals simp only [external,frozen,blocked,Bool.false_eq_true,↓reduceIte]
      all_goals rfl
    · exact ⟨.protocol c,Or.inl rfl,
        external_native_fields s c allowed (by simpa using frozen) (by simpa using blocked)⟩
  · refine ⟨.quiet,Or.inl ?_⟩
    cases c <;> simp only [ExternalCommand,not_true_eq_false] at allowed
    all_goals simp [external,frozen,reject]

/-- Every actual business branch selects an execution whose result is retained
or observed by that branch; refused branches select the no-evaluator case. -/
theorem service_realizes (s : Session) (c : Command) (hc : Business c) :
    ∃ call, Realizes s c (step s c) call (serviceValue s.active call) := by
  cases c <;> simp only [Business] at hc
  case accept x => exact accept_realizes s x
  case producer => exact producer_realizes s
  case deliverD => exact deliver_realizes s true
  case deliverN => exact deliver_realizes s false
  case join => exact join_realizes s
  case whole => exact whole_realizes s
  case external raw => exact external_realizes s raw

theorem invariant_protocol_bounded (s : Active) (hs : Invariant s) : PendingMigration.Bounded s.protocol := by
  have length := List.Nodup.length_le_card hs.protocol.order
  simpa [PendingMigration.Bounded,delayProjection] using length

theorem wrapper_retained_bound (s : Session) (bounded : PendingMigration.Bounded s.active.protocol)
    (certificate : ServiceCertified s.active.cut capacity) : wrapperRetained s ≤ capacity := by
  have copy : (s.prepared.map (fun p => p.target.protocol.active.cells + retainedCells p.target.cut)).getD 0 ≤ 26 := by
    cases hp : s.prepared with
    | none => simp [hp]
    | some p =>
      have backend := Migration.backend_cells p.target.protocol.active
      have store : retainedCells p.target.cut ≤ 24 := by cases p.target.cut <;> decide
      simp only [hp,Option.map_some,Option.getD_some]
      omega
  have certified := certificate s.active rfl bounded .quiet
    (PendingMigration.stateSlots s.active.protocol + 16 + 4 + 2 * retainedCells s.active.cut + 44 + 8)
    (by simp [serviceTrace,serviceAllocations,occupancies]; omega)
  unfold wrapperRetained
  omega

theorem service_cut (s : Session) (c : Command) (hc : Business c) :
    (step s c).session.active.cut = s.active.cut := by
  cases c <;> simp only [Business] at hc
  case accept input =>
    simp only [step,accept]
    generalize PendingMigration.step s.active.protocol (.accept input) = out
    repeat' first | rfl | split | dsimp only [updateResidual,Active.withResiduals]
  case external raw =>
    simp only [step]
    unfold external
    split
    · rfl
    · generalize PendingMigration.step s.active.protocol raw = out
      cases raw <;> dsimp only
      all_goals try rfl
      all_goals split
      all_goals try rfl
      all_goals try dsimp only
      all_goals split
      all_goals try rfl
      all_goals try dsimp only
      all_goals split
      all_goals try rfl
      all_goals split
      all_goals try rfl
      all_goals split <;> rfl
  all_goals simp only [step,producer,deliver,join,whole]
  all_goals repeat' first | rfl | split | dsimp only [updateResidual,Active.withResiduals]

/-- The complete actual-command execution trace is admitted by the same
service certificate stored on a replacement target. Readiness and the live
invariant justify inherited queue and successor-state bounds. -/
theorem service_execution_bound (s : Session) (c : Command) (hc : Business c)
    (hs : Invariant s.active) (ready : InnerReady s)
    (certificate : ServiceCertified s.active.cut capacity) :
    ∃ trace, ServiceExecution s c (step s c) trace ∧ ∀ live ∈ trace, live ≤ capacity := by
  obtain ⟨call,realized⟩ := service_realizes s c hc
  have bounded := invariant_protocol_bounded s.active hs
  have afterBounded := invariant_protocol_bounded _ (step_invariant s c hs ready)
  have targetCertificate : ServiceCertified (step s c).session.active.cut capacity := by
    rw [service_cut s c hc]; exact certificate
  refine ⟨wrapperServiceTrace s (step s c) call,
    ⟨rfl,call,realized,native_service_runs s.active call,rfl⟩,?_⟩
  intro live mem
  simp only [wrapperServiceTrace,List.mem_append,List.mem_singleton] at mem
  rcases mem with (rfl | mem) | rfl
  · exact wrapper_retained_bound s bounded certificate
  · exact certificate s.active rfl bounded call live mem
  · exact wrapper_retained_bound _ afterBounded targetCertificate

/-- Stored replacement evidence is instantiated on the actual ownership-cut
result, including its next service command and all live storage checkpoints. -/
theorem committed_service_execution (s : Active) (p : Prepared s) (permission : Bool)
    (c : Command) (hc : Business c) (hs : Invariant p.target)
    (inner : p.target.protocol.prepared = none) :
    ∃ r trace, Certificate r p.target.cut p.target.protocol.active.kind ∧
      ServiceExecution (commit ⟨s,some p,permission⟩).session c
        (step (commit ⟨s,some p,permission⟩).session c) trace ∧
      ∀ live ∈ trace, live ≤ r.capacity := by
  obtain ⟨r,cert,_⟩ := p.evidence
  obtain ⟨trace,run,bound⟩ := service_execution_bound
    (commit ⟨s,some p,permission⟩).session c hc hs ⟨inner,rfl⟩ cert.service
  exact ⟨r,trace,cert,run,bound⟩

theorem reachable_service_bound (cut : Cut) (kind : Migration.Kind) (cs : List Command)
    (c : Command) (hc : Business c) :
    let s := (execute (initial cut kind) cs).1
    ∃ trace, ServiceExecution s c (step s c) trace ∧
      ∀ live ∈ trace, live ≤ serviceCapacity s.active.cut := by
  have reached := reachable_refinement cut kind cs
  exact service_execution_bound _ c hc reached.1 reached.2.1 (service_certified _ _ (Nat.le_refl _))

end FRPSpec.Regional.Pending
