import Applications.FRP.RegionalPendingInternal

/-! Logical live-cell and evaluator witnesses for the bounded pending client.
These counts describe the modeled evaluator, not the host allocator. -/
namespace FRPSpec.Regional.Pending
open Applications.Circuits

/-- The producer witness evaluates the actual rich code, including its selected
sum branch; it is not merely the equation identifying its Boolean result. -/
theorem producer_execution (input : Bool) :
    Rich.Executes Rich.code ((),Sum.inl input) (produce input)
      (Rich.dispatches Rich.code ((),Sum.inl input)) :=
  Rich.executes Rich.code Rich.code_analyzable ((),Sum.inl input)

theorem producer_allocation (input : Bool) :
    Rich.Allocates Rich.code ((),Sum.inl input) (produce input)
      (Rich.allocations Rich.code ((),Sum.inl input)) ∧
    (Rich.allocations Rich.code ((),Sum.inl input)).sum ≤ Rich.arena Rich.code :=
  ⟨Rich.allocates Rich.code Rich.code_analyzable _,Rich.allocations_le _ _⟩

/-- Work includes protocol queue scans and retirement, actual producer and
consumer interpreters, all copied cells, and one command/response adapter unit. -/
def WorkEvent.work : WorkEvent → Nat
  | .producer => Rich.dispatches Rich.code ((),Sum.inl false)
  | .deliverD => Indefinite.delay.body.work
  | .deliverN => Circuit.not.work
  | .join => Circuit.xor.work
  | .consumers cut nodes => nodes + (if cut == .checked then 4 else 0)
  | .protocol work _ => work
  | .copy cells => cells
  | .policy work => work
  | _ => 1

def work (o : Outcome) : Nat := 1 + (o.events.map WorkEvent.work).sum

/-- Both Boolean inputs take the selected rich sum branch. No producer event
can be replaced by a free oracle computation under this billing rule. -/
theorem producer_bill (input : Bool) :
    WorkEvent.producer.work = Rich.dispatches Rich.code ((),Sum.inl input) := by
  cases input <;> rfl

/-- A successful public producer step stores the result of the witnessed rich
execution and charges exactly that execution and its retained-store copy. -/
theorem public_producer_execution (s : Session) (slot : Bool) (r : PendingMigration.Request)
    (localState : Residual) (hp : s.prepared = none)
    (hh : headResidual s.active = some (slot,r,localState))
    (phase : r.phase = .accepted) (cache : localState.cached = none)
    (live : localState.cancelled = false) :
    ((producer s).session.active.residuals.get slot).map Residual.cached = some (some (produce r.input)) ∧
      (producer s).events = [.producer,.copy (retainedCells s.active.cut)] ∧
      Rich.Executes Rich.code ((),Sum.inl r.input) (produce r.input)
        (Rich.dispatches Rich.code ((),Sum.inl r.input)) := by
  let next := updateResidual s.active slot
    {localState with cached := some (produce r.input),oldState := s.active.protocol.active.logical}
  have he : producer s = ⟨⟨{next with deliveries := ⟨some slot,some slot⟩},none,s.permitted⟩,
      .produced,none,none,none,[.producer,.copy (retainedCells s.active.cut)]⟩ := by
    simp [producer,hp,hh,phase,cache,live,next]
  rw [he]
  refine ⟨?_,rfl,producer_execution r.input⟩
  simp [next,updateResidual,Active.withResiduals,Active.residuals]

/-- Actual conversion retains the old owner while decoding and encoding its
complete continuation. The last state releases only the decoded scratch. -/
inductive TransferRuns : Active → Cut → Migration.Kind → Active → List Nat → Prop where
  | convert (s : Active) (cut : Cut) (kind : Migration.Kind) :
    TransferRuns s cut kind (convert s cut kind)
      [transferBase s,transferBase s+23,transferBase s+23+targetCells cut kind,
       transferBase s+targetCells cut kind]

theorem transfer_runs (s : Active) (cut : Cut) (kind : Migration.Kind) :
    ∃ trace, TransferRuns s cut kind (convert s cut kind) trace ∧
      ∀ live ∈ trace, live ≤ transitionPeak s cut kind := by
  refine ⟨_,.convert s cut kind,?_⟩
  intro live member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp only [transitionPeak] <;> omega

theorem admitted_transfer (s : Active) (cut : Cut) (kind : Migration.Kind) (capacity : Nat)
    (h : requiredCapacity s cut kind ≤ capacity) :
    ∃ trace, TransferRuns s cut kind (convert s cut kind) trace ∧
      (∀ live ∈ trace, live ≤ capacity) ∧
      serviceCapacity s.cut ≤ capacity ∧ serviceCapacity cut ≤ capacity := by
  obtain ⟨trace,run,bound⟩ := transfer_runs s cut kind
  have peak : transitionPeak s cut kind ≤ capacity :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans h
  refine ⟨trace,run,fun live hl => (bound live hl).trans peak,?_,?_⟩
  · exact (Nat.le_max_left _ _).trans h
  · exact ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans h

/-- This evidence belongs to the prepared target actually installed by commit.
It covers the transfer overlap and both executors, independently of ranking. -/
theorem stored_admission (s : Active) (p : Prepared s) :
    ∃ r, Certificate r p.target.cut p.target.protocol.active.kind ∧
      serviceCapacity s.cut ≤ r.capacity ∧ serviceCapacity p.target.cut ≤ r.capacity ∧
      transitionPeak s p.target.cut p.target.protocol.active.kind ≤ r.capacity := by
  obtain ⟨r,cert,bound⟩ := p.evidence
  refine ⟨r,cert,(Nat.le_max_left _ _).trans bound,?_,?_⟩
  · exact ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans bound
  · exact ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans bound

def preparedTarget (s : Session) : Option Active := s.prepared.map (fun p => p.target)
@[simp] theorem preparedTarget_some (s : Active) (p : Prepared s) (permission : Bool) :
    preparedTarget ⟨s,some p,permission⟩ = some p.target := rfl

/-- Resource admission and the exact copied target are linked to a successful
public preparation, including the allocation/release event trace. -/
theorem prepare_execution (s : Session) (expected cut : Cut) (kind : Migration.Kind)
    (r : Requirements) (a v : Bool)
    (h : (prepare s expected cut kind r a v false).status = .prepared) :
    preparedTarget (prepare s expected cut kind r a v false).session =
        some (convert s.active cut kind) ∧
      requiredCapacity s.active cut kind ≤ r.capacity ∧
      (prepare s expected cut kind r a v false).events =
        [.allocate (23+targetCells cut kind),.copy 23,.copy (targetCells cut kind),.validate,.release 23] := by
  generalize outEq : prepare s expected cut kind r a v false = out at h ⊢
  unfold prepare at outEq
  repeat' first | (split at outEq) | (cases outEq; simp_all [reject])
  all_goals cases v <;> simp_all

/-- The successful public transition supplies the evaluator lifetime witness,
not just a standalone maximum formula. Admission bounds every live checkpoint. -/
theorem prepare_lifetime (s : Session) (expected cut : Cut) (kind : Migration.Kind)
    (r : Requirements) (a v : Bool)
    (h : (prepare s expected cut kind r a v false).status = .prepared) :
    ∃ trace, TransferRuns s.active cut kind (convert s.active cut kind) trace ∧
      (∀ live ∈ trace, live ≤ r.capacity) ∧
      preparedTarget (prepare s expected cut kind r a v false).session =
        some (convert s.active cut kind) := by
  have checked := prepare_execution s expected cut kind r a v h
  obtain ⟨trace,run,bound,_,_⟩ := admitted_transfer s.active cut kind r.capacity checked.2.1
  exact ⟨trace,run,bound,checked.1⟩

/-- Validation failure releases both actual candidate storage and decoded scratch. -/
theorem prepare_validation_release (s : Session) (expected cut : Cut) (kind : Migration.Kind)
    (r : Requirements) (a v bad : Bool)
    (h : (prepare s expected cut kind r a v bad).status = .validation) :
    (prepare s expected cut kind r a v bad).events =
      [.allocate (23+targetCells cut kind),.copy 23,.copy (targetCells cut kind),.validate,
       .release (23+targetCells cut kind)] := by
  generalize outEq : prepare s expected cut kind r a v bad = out at h ⊢
  unfold prepare at outEq
  repeat' first | (split at outEq) | (cases outEq; simp_all [reject])
  all_goals repeat' first | (split at h) | (simp_all)

theorem commit_release (s : Active) (p : Prepared s) (permission : Bool) :
    (commit ⟨s,some p,permission⟩).session.active = p.target ∧
      (commit ⟨s,some p,permission⟩).events =
        [.release (targetCells s.cut s.protocol.active.kind)] := ⟨rfl,rfl⟩

theorem cancel_release (s : Active) (p : Prepared s) (permission : Bool) :
    (cancel ⟨s,some p,permission⟩).session.active = s ∧
      (cancel ⟨s,some p,permission⟩).events =
        [.release (targetCells p.target.cut p.target.protocol.active.kind)] := ⟨rfl,rfl⟩

end FRPSpec.Regional.Pending
