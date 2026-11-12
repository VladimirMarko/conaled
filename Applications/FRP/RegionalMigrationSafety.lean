import Applications.FRP.RegionalMigration

/-! Joint continuation and permission preservation through quiescent transfers. -/
namespace FRPSpec.Regional.Reconfiguration
open Progress Progress.Feedback Selection

theorem prepare_preserves (s : Session) (e c : Sites) (r : Requirements) (a v : Bool) :
    (prepare s e c r a v).session.active = s.active := by
  simp only [prepare,validate_transfer,Bool.true_and,validate_transfer,Bool.true_and]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

/-- Success exposes the converted executor actually stored by prepare. -/
theorem prepare_target (s : Session) (e c : Sites) (r : Requirements) (a v : Bool)
    (h : (prepare s e c r a v).status = .prepared) :
    (prepare s e c r a v).session.prepared.map (fun p => p.target) = some (transfer s.active c) := by
  by_cases h0 : s.prepared.isSome = true
  · simp [prepare,h0,refuse] at h
  by_cases h1 : (!s.permitted) = true
  · simp [prepare,h0,h1,refuse] at h
  by_cases h2 : e ≠ s.active.sites
  · simp [prepare,h0,h1,h2,refuse] at h
  by_cases h3 : eligible r c
  · by_cases h4 : required s.active c ≤ r.capacity
    · by_cases h5 : (!a) = true
      · simp [prepare,h0,h1,h2,h3,h4,h5,refuse] at h
      by_cases h6 : (!v) = true
      · simp [prepare,h0,h1,h2,h3,h4,h5,h6,refuse] at h
      let p : Prepared s.active := ⟨transfer s.active c,transfer_observation _ _,
        ⟨r,certificate r c h3,h4⟩⟩
      have ho : prepare s e c r a v =
          ⟨⟨s.active,some p,false⟩,.prepared,none,
            [.check,.allocate 2,.copy 2,.allocate c.plan.retained,
             .copy c.plan.retained,.check,.release 2]⟩ := by
        simp [prepare,h0,h1,h2,h3,h4,h5,h6,p]
      rw [ho]
      rfl
    · simp [prepare,h0,h1,h2,h3,h4,refuse] at h
  · simp [prepare,h0,h1,h2,h3,refuse] at h

theorem commit_preserves (s : Session) :
    observation (commit s).session.active = observation s.active := by
  cases h : s.prepared with
  | none => simp [commit,h,refuse]
  | some p => simpa [commit,h] using p.continuation

theorem cancel_preserves (s : Session) : (cancel s).session.active = s.active := by
  cases h : s.prepared <;> simp [cancel,h,refuse]

theorem prepared_freezes (s : Session) (h : s.prepared.isSome = true) (x : Input × Input) :
    (tick s x).session = s ∧ (tick s x).output = none := by simp [tick,h,refuse]

theorem transfer_not_reset (c : Sites) :
    observation (transfer ⟨c,resume c (true,false)⟩ c) = (true,false) ∧
    observation (Selection.Session.start c) = (false,false) := by
  constructor
  · rw [transfer_observation]; exact observe_resume _ _
  · exact c.initial_correct

/-- A non-tick command cannot manufacture another reconfiguration permission. -/
theorem prepare_consumes (s : Session) (e c : Sites) (r : Requirements) (a v : Bool)
    (hp : s.prepared.isSome = false) (ht : s.permitted = true) :
    (prepare s e c r a v).session.permitted = false := by
  simp only [prepare,validate_transfer,Bool.true_and,hp,ht,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem throttled (s : Session) (e c : Sites) (r : Requirements) (a v : Bool)
    (hp : s.prepared.isSome = false) (ht : s.permitted = false) :
    (prepare s e c r a v).status = .throttled ∧
    (prepare s e c r a v).session = s := by
  simp [prepare,hp,ht,refuse]

theorem propose_preserves (s : Session) (r : Requirements) (w : String)
    (e : Option Optimization.Choice.Epoch) (cs : List Sites) :
    (propose s r w e cs).session.active = s.active := by
  dsimp only [propose]
  split
  · rfl
  · exact prepare_preserves _ _ _ _ _ _

/-- Every admitted tick uses the original actual regional executor. -/
theorem tick_refines (s : Session) (x : Input × Input) :
    ((tick s x).output = none ∧ observation (tick s x).session.active = observation s.active) ∨
    ((tick s x).output = some (!(observation s.active).1,!(observation s.active).2) ∧
      observation (tick s x).session.active = (Rich.oracle x.1,Rich.oracle x.2)) := by
  by_cases h : s.prepared.isSome = true
  · exact Or.inl ⟨by simp [tick,h,refuse],by simp [tick,h,refuse]⟩
  · right
    have hc := s.active.sites.step_correct s.active.state x
    exact ⟨by simpa [tick,h,observation] using congrArg some hc.1,
      by unfold tick; rw [ite_eq_right_iff.mpr (fun hh => (h hh).elim)]; exact hc.2⟩

/-- The ordinary source consumes only actually executed ticks, not frozen inputs. -/
def acceptedInputs : Session → List Command → List (Input × Input)
  | _, [] => []
  | s, c::cs =>
      let next := step s c
      (match c with
        | .input x => if next.output.isSome then [x] else []
        | _ => []) ++ acceptedInputs next.session cs

theorem command_preserves (s : Session) (c : Command) :
    (step s c).output = none → observation (step s c).session.active = observation s.active := by
  intro h
  cases c with
  | input x =>
    rcases tick_refines s x with h' | h'
    · exact h'.2
    · simp only [step] at h
      rw [h'.1] at h
      contradiction
  | prepare e c r a v => exact congrArg observation (prepare_preserves s e c r a v)
  | commit => exact commit_preserves s
  | cancel => exact congrArg observation (cancel_preserves s)
  | unsupported => rfl
  | policy r w e cs => exact congrArg observation (propose_preserves s r w e cs)

theorem prepare_output (s : Session) (e c : Sites) (r : Requirements) (a v : Bool) :
    (prepare s e c r a v).output = none := by
  simp only [prepare,validate_transfer,Bool.true_and,validate_transfer,Bool.true_and]
  repeat first | split | rfl

theorem propose_output (s : Session) (r : Requirements) (w : String)
    (e : Option Optimization.Choice.Epoch) (cs : List Sites) :
    (propose s r w e cs).output = none := by
  dsimp only [propose]
  split
  · rfl
  · exact prepare_output _ _ _ _ _ _

theorem commit_output (s : Session) : (commit s).output = none := by
  cases h : s.prepared <;> simp [commit,h,refuse]
theorem cancel_output (s : Session) : (cancel s).output = none := by
  cases h : s.prepared <;> simp [cancel,h,refuse]

/-- Every finite schedule, including repeated transfers and failed attempts,
refines the independent source on precisely its accepted execution ticks. -/
theorem execute_refines (s : Session) (cs : List Command) :
    (execute s cs).2 = (run Selection.oracle.mealy (observation s.active) (acceptedInputs s cs)).1 ∧
    observation (execute s cs).1.active =
      (run Selection.oracle.mealy (observation s.active) (acceptedInputs s cs)).2 := by
  induction cs generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons c cs ih =>
    have hi := ih (step s c).session
    cases c with
    | input x =>
      rcases tick_refines s x with h | h
      · simp only [execute,acceptedInputs,step,h.1,Option.toList_none,Option.isSome_none,
          Bool.false_eq_true,↓reduceIte,List.nil_append] at *
        simpa only [h.2] using hi
      · simp only [step] at hi
        rw [h.2] at hi
        simpa only [execute,acceptedInputs,step,h.1,Option.toList_some,Option.isSome_some,
          ↓reduceIte,List.singleton_append,run,Selection.oracle,Initialized.mealy,
          List.cons.injEq,true_and,eq_self] using
          (And.intro (congrArg (fun ys => (!(observation s.active).1,!(observation s.active).2)::ys) hi.1) hi.2)
    | prepare e c r a v =>
      simp only [step] at hi
      rw [prepare_preserves] at hi
      simpa only [execute,acceptedInputs,step,prepare_output,Option.toList_none,List.nil_append] using hi
    | commit =>
      simp only [step] at hi
      rw [commit_preserves] at hi
      simpa only [execute,acceptedInputs,step,commit_output,Option.toList_none,List.nil_append] using hi
    | cancel =>
      simp only [step] at hi
      rw [cancel_preserves] at hi
      simpa only [execute,acceptedInputs,step,cancel_output,Option.toList_none,List.nil_append] using hi
    | unsupported => simpa [execute,acceptedInputs,step,refuse] using hi
    | policy r w e catalog =>
      simp only [step] at hi
      rw [propose_preserves] at hi
      simpa only [execute,acceptedInputs,step,propose_output,Option.toList_none,List.nil_append] using hi

/-- Without a service tick, no control command restores consumed permission. -/
theorem control_permission (s : Session) (c : Command)
    (h : s.permitted = false) (hc : ∀ x, c ≠ .input x) :
    (step s c).session.permitted = false := by
  cases c with
  | input x => exact (hc x rfl).elim
  | prepare e c r a v =>
    simp only [step,prepare,h,Bool.not_false,↓reduceIte]
    split <;> simpa [refuse] using h
  | commit => cases hp : s.prepared <;> simp [step,commit,hp,refuse,h]
  | cancel => cases hp : s.prepared <;> simp [step,cancel,hp,refuse,h]
  | unsupported => exact h
  | policy r w e cs =>
    simp only [step]
    dsimp only [propose]
    split
    · exact h
    · simp only [prepare,h,Bool.not_false,↓reduceIte]
      split <;> simpa [refuse] using h

theorem commit_unprepared (s : Session) : (commit s).session.prepared = none := by
  rcases s with ⟨active,prepared,permitted⟩
  cases prepared <;> rfl

/-- A finite scheduler round resolves preparation and then executes one tick.
External fairness must actually schedule this round; control traffic alone is
not assumed to do so. -/
theorem finishing_round (s : Session) (x : Input × Input) :
    (tick (commit s).session x).output =
      some (!(observation s.active).1,!(observation s.active).2) ∧
    observation (tick (commit s).session x).session.active =
      (Rich.oracle x.1,Rich.oracle x.2) := by
  have hc := tick_refines (commit s).session x
  rcases hc with hc | hc
  · have hn := hc.1
    simp [tick,commit_unprepared] at hn
  · simpa only [commit_preserves] using hc

/-- Existing placement-only transfer remains a separate control. -/
theorem placement_control (b : Bool) (xs : List Bool) :
    (run MigrationPair.redundant.machine.mealy (MigrationPair.forward b) xs).1 =
      (run Indefinite.delay.machine.mealy b xs).1 :=
  (MigrationPair.finite_suffix b (MigrationPair.forward b) rfl xs).1.symm

end FRPSpec.Regional.Reconfiguration
