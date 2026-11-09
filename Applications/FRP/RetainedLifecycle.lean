import Applications.FRP.RetainedSource
import Applications.FRP.LifecyclePipeline

/-! Optional admission and reclamation around the identified lifecycle.
The full-history state appears only in the simulation relation. -/
namespace FRPSpec.Frontier.Retention
open Trace
variable {T α : Type} [LinearOrder T]

def cropLifecycle (q : T) (s : Lifecycle.State T α) : Lifecycle.State T α :=
  ⟨cropEngine q s.engine,s.last⟩

theorem cropEngine_comp (q q' : T) (s : Engine.MachineState T α) (h : q ≤ q') :
    cropEngine q' (cropEngine q s) = cropEngine q' s := by
  cases s
  simp [cropEngine,crop_comp q q' _ h]

theorem cropLifecycle_comp (q q' : T) (s : Lifecycle.State T α) (h : q ≤ q') :
    cropLifecycle q' (cropLifecycle q s) = cropLifecycle q' s := by
  cases s
  simp [cropLifecycle,cropEngine_comp q q' _ h]

theorem lifecycle_step_crop (q : T) (s : Lifecycle.State T α) (c : Lifecycle.Command T α)
    (h : PendingWithin q s.engine.request) :
    cropLifecycle q (Lifecycle.step (cropLifecycle q s) c).1 =
      cropLifecycle q (Lifecycle.step s c).1 ∧
    (Lifecycle.step (cropLifecycle q s) c).2 = (Lifecycle.step s c).2 := by
  have hc : Lifecycle.classify (cropLifecycle q s) = Lifecycle.classify s := by
    funext id; rfl
  cases c with
  | begin id t =>
    simp only [Lifecycle.step,hc]
    split <;> simp [cropLifecycle,Lifecycle.registered,cropEngine,crop_comp q q _ le_rfl]
  | source r m =>
    have he := engine_step_crop q s.engine (Lifecycle.active s.last (.source r m)) h
    simpa [Lifecycle.step,cropLifecycle] using
      And.intro (congrArg (fun e => Lifecycle.State.mk e s.last) he.1)
        (congrArg (fun out => Lifecycle.Event.mk none (Lifecycle.tag s.last out)) he.2)
  | process id =>
    have he := engine_step_crop q s.engine (Lifecycle.active s.last (.process id)) h
    simpa [Lifecycle.step,cropLifecycle] using
      And.intro (congrArg (fun e => Lifecycle.State.mk e s.last) he.1)
        (congrArg (fun out => Lifecycle.Event.mk none (Lifecycle.tag s.last out)) he.2)
  | idle =>
    have he := engine_step_crop q s.engine (Lifecycle.active s.last .idle) h
    simpa [Lifecycle.step,cropLifecycle] using
      And.intro (congrArg (fun e => Lifecycle.State.mk e s.last) he.1)
        (congrArg (fun out => Lifecycle.Event.mk none (Lifecycle.tag s.last out)) he.2)

def Admitted (q : T) : Lifecycle.Command T α → Prop
  | .begin _ t => q ≤ t
  | _ => True
instance (q : T) (c : Lifecycle.Command T α) : Decidable (Admitted q c) := by
  cases c <;> unfold Admitted <;> infer_instance

theorem pending_next (q : T) (sources : Inputs T α) (r : Demand.Request T)
    (a : Demand.Action T) (h : PendingWithin q r)
    (ha : ∀ t, a = .register t → q ≤ t) : PendingWithin q (Demand.next sources a r) := by
  cases r with
  | absent =>
    cases a with
    | register t => exact ha t rfl
    | source r => trivial
    | process => trivial
    | idle => trivial
  | pending t =>
    cases a with
    | register u => exact h
    | source r => exact h
    | idle => exact h
    | process =>
      simp only [Demand.next]
      split
      · trivial
      · exact h
  | done => cases a <;> trivial

theorem lifecycle_pending (q : T) (s : Lifecycle.State T α) (c : Lifecycle.Command T α)
    (h : PendingWithin q s.engine.request) (ha : Admitted q c) :
    PendingWithin q (Lifecycle.step s c).1.engine.request := by
  cases c with
  | begin id t =>
    simp only [Lifecycle.step]
    split
    · exact ha
    · exact h
  | source r m => exact pending_next q _ _ _ h (by intro t ht; cases ht)
  | process id =>
    apply pending_next q _ _ _ h
    intro t ht
    simp only [Lifecycle.active] at ht
    split at ht <;> cases ht
  | idle => exact pending_next q _ _ _ h (by intro t ht; cases ht)

structure State (T α : Type) where
  lower : T
  machine : Lifecycle.State T α
  deriving DecidableEq, Repr
inductive Command (T α : Type)
  | native (command : Lifecycle.Command T α)
  | advanceLower (bound : T)
  deriving DecidableEq, Repr
inductive Notice | outsideRetention | advanced | decreasing | pendingConflict
  deriving DecidableEq, Repr
structure Event (T α : Type) where
  notice : Option Notice
  native : Lifecycle.Event T α
  deriving DecidableEq, Repr

def init (q : T) (sources : Inputs T α) : State T α :=
  ⟨q,cropLifecycle q (Lifecycle.init sources)⟩

def forward (s : State T α) (c : Lifecycle.Command T α) : State T α × Event T α :=
  let next := Lifecycle.step s.machine c
  (⟨s.lower,cropLifecycle s.lower next.1⟩,⟨none,next.2⟩)

/-- Expiry takes priority over native busy/stale classification. No expired begin
is forwarded or reserves an ID. Bound failures stutter and do not emit. -/
def step (s : State T α) : Command T α → State T α × Event T α
  | .native c => if Admitted s.lower c then forward s c
      else (s,⟨some .outsideRetention,⟨none,none⟩⟩)
  | .advanceLower q =>
    if s.lower ≤ q then
      if PendingWithin q s.machine.engine.request then
        (⟨q,cropLifecycle q s.machine⟩,⟨some .advanced,⟨none,none⟩⟩)
      else (s,⟨some .pendingConflict,⟨none,none⟩⟩)
    else (s,⟨some .decreasing,⟨none,none⟩⟩)

theorem expired (s : State T α) (id : Nat) (t : T) (h : t < s.lower) :
    step s (.native (.begin id t)) = (s,⟨some .outsideRetention,⟨none,none⟩⟩) := by
  have hn : ¬s.lower ≤ t := not_le.mpr h
  simp [step,Admitted,hn]

/-- Rejected queries and retention commands stutter in the unrestricted reference. -/
def project (s : State T α) : Command T α → Lifecycle.Command T α
  | .native c => if Admitted s.lower c then c else .idle
  | .advanceLower _ => .idle

def Related (s : State T α) (full : Lifecycle.State T α) : Prop :=
  s.machine = cropLifecycle s.lower full ∧ PendingWithin s.lower full.engine.request

theorem init_related (q : T) (sources : Inputs T α) :
    Related (init q sources) (Lifecycle.init sources) := ⟨rfl,trivial⟩

theorem lifecycle_idle (s : Lifecycle.State T α) : Lifecycle.step s .idle = (s,⟨none,none⟩) := by
  cases s with | mk e last =>
    cases e with | mk l r request =>
      cases last <;> cases request <;> rfl

theorem step_refines (s : State T α) (full : Lifecycle.State T α) (h : Related s full)
    (c : Command T α) :
    Related (step s c).1 (Lifecycle.step full (project s c)).1 ∧
    (step s c).2.native = (Lifecycle.step full (project s c)).2 := by
  obtain ⟨hm,hp⟩ := h
  cases c with
  | native c =>
    by_cases ha : Admitted s.lower c
    · have he := lifecycle_step_crop s.lower full c hp
      simp only [step,project,ite_eq_left ha,forward,Related,hm]
      exact ⟨⟨he.1,lifecycle_pending _ _ _ hp ha⟩,he.2⟩
    · simp only [step,project,ite_eq_right ha,lifecycle_idle]
      exact ⟨⟨hm,hp⟩,trivial⟩
  | advanceLower q =>
    by_cases hq : s.lower ≤ q
    · by_cases hpending : PendingWithin q s.machine.engine.request
      · have hf : PendingWithin q full.engine.request := by simpa [hm,cropLifecycle,cropEngine] using hpending
        simp only [step,project,ite_eq_left hq,ite_eq_left hpending,lifecycle_idle]
        refine ⟨⟨?_,hf⟩,trivial⟩
        exact (congrArg (cropLifecycle q) hm).trans (cropLifecycle_comp _ _ _ hq)
      · simp only [step,project,ite_eq_left hq,ite_eq_right hpending,lifecycle_idle]
        exact ⟨⟨hm,hp⟩,trivial⟩
    · simp only [step,project,ite_eq_right hq,lifecycle_idle]
      exact ⟨⟨hm,hp⟩,trivial⟩

theorem response_admitted (s : State T α) (full : Lifecycle.State T α)
    (h : Related s full) (c : Command T α) (r : Lifecycle.Response T α)
    (he : (step s c).2.native.response = some r) : s.lower ≤ r.time := by
  have hn : (Lifecycle.step full (project s c)).2.response = some r := by
    rw [← (step_refines s full h c).2]
    exact he
  have hp := (Lifecycle.emitted hn).2.2.1
  simpa [hp,PendingWithin] using h.2

/-- Truth is supplied for the unrestricted source reference, never for erased
history in the runtime. Exact native-event comparison transfers its answer. -/
theorem response_sound (s : State T α) (full : Lifecycle.State T α)
    (h : Related s full) (c : Command T α) (r : Lifecycle.Response T α)
    (he : (step s c).2.native.response = some r) (left right : T → List α)
    (hl : (full.engine.sources .left).Completes left)
    (hr : (full.engine.sources .right).Completes right) :
    r.batch = left r.time ++ right r.time := by
  have hn : (Lifecycle.step full (project s c)).2.response = some r := by
    rw [← (step_refines s full h c).2]
    exact he
  exact Lifecycle.response_sound hn left right hl hr

theorem lower_mono (s : State T α) (c : Command T α) : s.lower ≤ (step s c).1.lower := by
  cases c <;> simp only [step,forward]
  all_goals repeat' split
  all_goals simp_all

theorem advance_preserves_pending (s : State T α) (q t : T)
    (h : s.machine.engine.request = .pending t) :
    (step s (.advanceLower q)).1.machine.engine.request = .pending t := by
  simp only [step]
  split <;> try exact h
  split <;> exact h

def run (s : State T α) : List (Command T α) → State T α × List (Event T α)
  | [] => (s,[])
  | c::cs => let next := step s c; let rest := run next.1 cs; (rest.1,next.2::rest.2)

def projected (s : State T α) : List (Command T α) → List (Lifecycle.Command T α)
  | [] => []
  | c::cs => project s c :: projected (step s c).1 cs

theorem run_refines (s : State T α) (full : Lifecycle.State T α) (h : Related s full)
    (cs : List (Command T α)) :
    Related (run s cs).1 (Lifecycle.run full (projected s cs)).1 ∧
    (run s cs).2.map Event.native = (Lifecycle.run full (projected s cs)).2 := by
  induction cs generalizing s full with
  | nil => exact ⟨h,rfl⟩
  | cons c cs ih =>
    obtain ⟨hn,he⟩ := step_refines s full h c
    obtain ⟨hr,ho⟩ := ih _ _ hn
    exact ⟨hr,by simpa [run,projected,Lifecycle.run,he] using congrArg (List.cons (step s c).2.native) ho⟩

theorem run_append (s : State T α) (xs ys : List (Command T α)) :
    run s (xs ++ ys) = let a := run s xs; let b := run a.1 ys; (b.1,a.2 ++ b.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [run,ih]

end FRPSpec.Frontier.Retention
