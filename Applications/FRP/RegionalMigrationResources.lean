import Applications.FRP.RegionalMigrationSafety

/-! Execution-linked copied-value traces for quiescent state transfer. These are
logical cells, not a verification of Lean's allocator or garbage collector. -/
namespace FRPSpec.Regional.Reconfiguration
open Progress Progress.Feedback Selection

/-- Copy the two observed delay cells, construct the exact target representation,
then release the two-cell conversion buffer. Old state remains live throughout. -/
inductive TransferRuns : Selection.Session → Sites → Selection.Session → List Nat → Prop where
  | copy (s : Selection.Session) (c : Sites) :
    TransferRuns s c (transfer s c)
      [8+s.sites.plan.retained, 8+s.sites.plan.retained+2,
       8+s.sites.plan.retained+2+c.plan.retained,
       8+s.sites.plan.retained+c.plan.retained]

theorem transfer_runs (s : Selection.Session) (c : Sites) :
    ∃ target trace, TransferRuns s c target trace ∧
      observation target = observation s ∧
      ∀ live ∈ trace, live ≤ transferPeak s c := by
  refine ⟨transfer s c,_,.copy s c,transfer_observation s c,?_⟩
  intro live hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> simp only [transferPeak] <;> omega

/-- A transfer derivation certifies the executable target, not just its budget. -/
theorem TransferRuns.result {s c target trace} (h : TransferRuns s c target trace) :
    target = transfer s c ∧ observation target = observation s := by
  cases h
  exact ⟨rfl,transfer_observation _ _⟩

/-- The successful command stores precisely the executor in the allocation
judgment. This links the resource witness to the public transition. -/
theorem preparation_execution (s : Session) (e c : Sites) (r : Requirements) (a v : Bool)
    (h : (prepare s e c r a v).status = .prepared) :
    ∃ target trace, (prepare s e c r a v).session.prepared.map (fun p => p.target) = some target ∧
      TransferRuns s.active c target trace ∧ ∀ live ∈ trace, live ≤ transferPeak s.active c := by
  obtain ⟨target,trace,hr,_,hb⟩ := transfer_runs s.active c
  refine ⟨target,trace,?_,hr,hb⟩
  rw [hr.result.1]
  exact prepare_target s e c r a v h

/-- Sufficient admission covers the live transfer and both steady executors. -/
theorem admitted_transfer (s : Selection.Session) (c : Sites) (n : Nat)
    (h : required s c ≤ n) :
    ∃ trace, TransferRuns s c (transfer s c) trace ∧
      (∀ live ∈ trace, live ≤ n) ∧ 8+c.plan.storage ≤ n ∧ 8+s.sites.plan.storage ≤ n := by
  obtain ⟨target,trace,hr,_,hb⟩ := transfer_runs s c
  rw [hr.result.1] at hr
  refine ⟨trace,hr,fun live hl => (hb live hl).trans ?_,?_,?_⟩
  · exact (Nat.le_max_right _ _ |>.trans (Nat.le_max_right _ _)).trans h
  · exact (Nat.le_max_left _ _).trans h
  · exact ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans h

/-- All supplied cuts have checked execution analysis; direct native functions
outside this finite family remain unsupported for resource analysis. -/
theorem sites_analyzed (c : Sites) : c.plan.analyzed = true := by
  rcases c with ⟨l,r⟩
  cases l <;> cases r <;> rfl

theorem tick_allocation (s : Session) (x : Input × Input)
    (h : s.prepared.isSome = false) :
    ∃ trace, Plan.SpaceRuns s.active.sites.plan x s.active.state
      (s.active.sites.plan.machine.step (x,s.active.state)) trace ∧
      (∀ live ∈ trace, 8+s.active.sites.plan.retained+live ≤ 8+s.active.sites.plan.storage) ∧
      bill (tick s x).events = s.active.sites.plan.stepWork x s.active.state + 2 := by
  obtain ⟨trace,ht,hb⟩ := s.active.sites.plan.sufficient_storage
    (sites_analyzed _) s.active.sites.plan.storage (Nat.le_refl _) x s.active.state
  refine ⟨trace,ht,?_,?_⟩
  · intro live hl
    have := hb live hl
    omega
  · simp [tick,h,bill,Event.work]

/-- Commit drops the old representation; cancellation drops the new one.
Neither action allocates another copy or executes a business tick. -/
def releaseTrace (s : Session) (commitTarget : Bool) : List Nat :=
  match s.prepared with
  | none => [8+s.active.sites.plan.retained]
  | some p => [8+s.active.sites.plan.retained+p.target.sites.plan.retained,
      8+(if commitTarget then p.target.sites.plan.retained else s.active.sites.plan.retained)]

theorem prepared_capacity (s : Session) (p : Prepared s.active) :
    ∃ r, Selection.Certificate r p.target.sites ∧
      (∀ live ∈ releaseTrace ⟨s.active,some p,false⟩ true, live ≤ r.capacity) ∧
      (∀ live ∈ releaseTrace ⟨s.active,some p,false⟩ false, live ≤ r.capacity) := by
  obtain ⟨r,hc,hp⟩ := p.evidence
  have hh : transferPeak s.active p.target.sites ≤ r.capacity :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans hp
  refine ⟨r,hc,?_,?_⟩ <;> intro live hl <;>
    simp only [releaseTrace,Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hl
  all_goals rcases hl with rfl | rfl <;> simp only [transferPeak] at hh <;> omega

end FRPSpec.Regional.Reconfiguration
