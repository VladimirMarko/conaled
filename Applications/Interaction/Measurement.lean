import SquareKit.InteractionContracts

/-!
# One measurement attempt

Experimental executable decisions for #216. Observations report primitive facts;
this module does not establish that an OS adapter reports them truthfully.
Publication confirms an observed write, not crash durability. Unknown process
completion remains unknown even if cleanup later succeeds.
-/
namespace Interaction.Measurement

inductive Completion where
  | exited (code : Nat)
  | spawnFailed
  | timedOut
  | unknown
  deriving DecidableEq, Repr

inductive Status where
  | confirmed
  | failed
  | unknown
  deriving DecidableEq, Repr

structure Observation where
  completion : Completion
  outputComplete : Bool
  cleanup : Status
  publication : Status
  deriving DecidableEq, Repr

/-- Independent requirement: all four kinds of evidence are necessary. -/
def Good (o : Observation) : Prop :=
  o.completion = .exited 0 ∧ o.outputComplete = true ∧
    o.cleanup = .confirmed ∧ o.publication = .confirmed

/-- The executable decision used by the target adapter. -/
def decide (o : Observation) : Bool :=
  match o.completion, o.outputComplete, o.cleanup, o.publication with
  | .exited 0, true, .confirmed, .confirmed => true
  | _, _, _, _ => false

theorem decide_iff (o : Observation) : decide o = true ↔ Good o := by
  rcases o with ⟨c, b, k, p⟩
  cases c with
  | exited n => cases n <;> cases b <;> cases k <;> cases p <;>
      simp [decide, Good]
  | spawnFailed | timedOut | unknown => simp [decide, Good]

structure Controller where
  started : Bool := false
  observation : Option Observation := none
  deriving DecidableEq, Repr

def initial : Controller := {}

/-- A successful return authorizes exactly one launch; retain the returned state. -/
def begin (s : Controller) : Option Controller :=
  if s.started then none else some { s with started := true }

/-- Recording does not authorize another execution. -/
def record (s : Controller) (o : Observation) : Controller :=
  { s with observation := some o }

def successful (s : Controller) : Bool :=
  s.started && (s.observation.map decide).getD false

/-- Independent postcondition includes the retained evidence, not only a flag. -/
def ResultValid (s : Controller) : Prop :=
  successful s = true → s.started = true ∧ ∃ o, s.observation = some o ∧ Good o

theorem result_valid (s : Controller) : ResultValid s := by
  intro h
  simp only [successful, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  cases ho : s.observation with
  | none => simp [ho] at h
  | some o => exact ⟨o, rfl, (decide_iff o).mp (by simpa [ho] using h.2)⟩

/-- Every emitted record refines the independently specified allowed records. -/
theorem recording_refines (s : Controller) (o : Observation) :
    Refines Eq {t | t.started = s.started ∧ t.observation = some o ∧ ResultValid t}
      {record s o} := by
  intro t ht
  have ht : t = record s o := ht
  subst t
  exact ⟨record s o, ⟨rfl, rfl, result_valid _⟩, rfl⟩

theorem recording_safe (s : Controller) (o : Observation) :
    ResultValid (record s o) := by
  exact (recording_refines s o).property
    (P := ResultValid) (Q := ResultValid)
    (fun _ h => h.2.2) (fun _ _ h hp => h ▸ hp) _ rfl

theorem begin_safe : Safe (fun _ => True)
    (fun s t => begin s = some t) (fun t => t.started = true) := by
  intro s t _ h
  unfold begin at h
  split at h
  · cases h
  · cases h
    rfl

theorem recording_started : Stable
    (fun s t => ∃ o, t = record s o) (fun s => s.started = true) := by
  rintro s t hs ⟨o, rfl⟩
  exact hs

/-- Arbitrarily many observation updates cannot reauthorize the attempt. -/
theorem no_reexecution {s t : Controller} (hs : s.started = true)
    (h : Relation.ReflTransGen (fun s t => ∃ o, t = record s o) s t) :
    begin t = none := by
  have ht := recording_started.closure hs h
  simp [begin, ht]

/-- Facts about the external attempt, separate from the controller's knowledge. -/
structure World where
  exitCode : Option Nat
  outputFinished : Bool
  cleaned : Bool
  published : Bool

/-- Primitive trust obligations. Negative or unknown observations assert no
positive fact. This is not an assumption of successful measurement. -/
def Corresponds (w : World) (o : Observation) : Prop :=
  (∀ n, o.completion = .exited n → w.exitCode = some n) ∧
  (o.outputComplete = true → w.outputFinished = true) ∧
  (o.cleanup = .confirmed → w.cleaned = true) ∧
  (o.publication = .confirmed → w.published = true)

def Completed (w : World) : Prop :=
  w.exitCode = some 0 ∧ w.outputFinished = true ∧
    w.cleaned = true ∧ w.published = true

/-- The adapter owes four primitive correspondences; the controller supplies
conjunction and selection. No claim about arbitrary OS behavior is implicit. -/
theorem successful_world (s : Controller) (o : Observation) (w : World)
    (observed : s.observation = some o) (truth : Corresponds w o)
    (success : successful s = true) : Completed w := by
  obtain ⟨_, q, hq, good⟩ := result_valid s success
  have eq : q = o := Option.some.inj (hq.symm.trans observed)
  subst q
  exact ⟨truth.1 0 good.1, truth.2.1 good.2.1,
    truth.2.2.1 good.2.2.1, truth.2.2.2 good.2.2.2⟩

end Interaction.Measurement
