import Applications.FRP.PendingCrash.Runtime

/-! Independent ordered delay behavior. This source has no backend, journal,
slot, callback queue or peer table. Identities select the admitted occurrence
removed by prevention; effective outputs must consume the admission head. -/
namespace FRPSpec.PendingCrash

structure DelaySource where
  state : Bool := false
  waiting : List (Nat × Bool) := []
  deriving DecidableEq, Repr

inductive SourceLabel where
  | internal
  | admit (identity : Nat) (input : Bool)
  | prevent (identity : Nat) (input : Bool)
  | output (identity : Nat) (value : Bool)
  deriving DecidableEq, Repr

inductive DelayStep : SourceLabel → DelaySource → DelaySource → Prop
  | internal (s) : DelayStep .internal s s
  | admit (s identity input) : DelayStep (.admit identity input) s
      {s with waiting := s.waiting ++ [(identity,input)]}
  | prevent (state identity input pre post) :
      DelayStep (.prevent identity input) ⟨state, pre ++ (identity,input) :: post⟩
        ⟨state, pre ++ post⟩
  | output (state identity input rest) :
      DelayStep (.output identity state) ⟨state, (identity,input) :: rest⟩ ⟨input,rest⟩

/-- Simultaneous contradictory observable labels are refused, not silently
projected to whichever one would make the source trace pass. -/
def sourceLabel (entry : LogEntry) : Option SourceLabel :=
  match entry.accepted, entry.effect, entry.prevented with
  | none, none, none => some .internal
  | some (i,x), none, none => some (.admit i x)
  | none, some (i,y), none => some (.output i y)
  | none, none, some (i,x) => some (.prevent i x)
  | _, _, _ => none

/-- The selected occurrence is retained in the proof of a successful removal. -/
def removePending (identity : Nat) (input : Bool) :
    (waiting : List (Nat × Bool)) → Option {remaining : List (Nat × Bool) //
      ∃ pre post, waiting = pre ++ (identity,input) :: post ∧ remaining = pre ++ post}
  | [] => none
  | entry :: rest =>
    if h : entry = (identity,input) then
      some ⟨rest, [], rest, by simp [h], rfl⟩
    else match removePending identity input rest with
      | none => none
      | some result => some ⟨entry :: result.val, by
          obtain ⟨pre, post, before, after⟩ := result.property
          exact ⟨entry :: pre, post, by simp [before], by simp [after]⟩⟩

def delayAdvance (s : DelaySource) (label : SourceLabel) :
    Option {next : DelaySource // DelayStep label s next} :=
  match label with
  | .internal => some ⟨s, .internal s⟩
  | .admit identity input => some ⟨{s with waiting := s.waiting ++ [(identity,input)]},
      .admit s identity input⟩
  | .prevent identity input =>
    match removePending identity input s.waiting with
    | none => none
    | some result => some ⟨{s with waiting := result.val}, by
        obtain ⟨pre, post, before, after⟩ := result.property
        cases s with
        | mk state waiting =>
          simp only at before after ⊢
          exact (congrArg₂ (DelayStep (.prevent identity input))
            (congrArg (DelaySource.mk state) before)
            (congrArg (DelaySource.mk state) after)).mpr
              (.prevent state identity input pre post)⟩
  | .output identity value =>
    match h : s.waiting with
    | [] => none
    | (key,input) :: rest =>
      if hi : identity = key then
        if hv : value = s.state then
          some ⟨⟨input, rest⟩, by
            cases s with
            | mk state waiting =>
              simp only at h hv ⊢
              subst waiting; subst identity; subst value
              exact .output state key input rest⟩
        else none
      else none

inductive DelayRun : DelaySource → List LogEntry → DelaySource → Prop
  | nil (s) : DelayRun s [] s
  | cons {s mid t entry entries label} : sourceLabel entry = some label →
      DelayStep label s mid → DelayRun mid entries t → DelayRun s (entry :: entries) t

/-- This checker certifies an observed execution against the independent
source. It does not direct the adapter or read its peer table. -/
def delayCheck : (s : DelaySource) → (entries : List LogEntry) → Option {t // DelayRun s entries t}
  | s, [] => some ⟨s, .nil s⟩
  | s, entry :: entries =>
    match h : sourceLabel entry with
    | none => none
    | some label => match delayAdvance s label with
      | none => none
      | some next => match delayCheck next.val entries with
        | none => none
        | some final => some ⟨final.val, .cons h next.property final.property⟩

def observedSource (s : DelaySource) (run : Execution) : Option DelaySource :=
  (delayCheck s run.observations).map Subtype.val

theorem observedSource_sound (s : DelaySource) (run : Execution) (t : DelaySource)
    (checked : observedSource s run = some t) : DelayRun s run.observations t := by
  unfold observedSource at checked
  cases h : delayCheck s run.observations with
  | none => simp [h] at checked
  | some result =>
    simp only [h, Option.map_some, Option.some.injEq] at checked
    exact checked ▸ result.property

/-- Erase only lifetime names in the independent source, not callback queues
in a native pending session. -/
def DelaySource.erase (s : DelaySource) : PendingMigration.Source :=
  ⟨s.state, s.waiting.map Prod.snd⟩

/-- The old pending machine remains available under its actual queue invariant;
this bridge makes no claim that stale keyed replies satisfy that invariant. -/
theorem native_pending_step (s : PendingMigration.Session) (command : PendingMigration.Command)
    (valid : PendingMigration.Valid s) :
    PendingMigration.SourceStep (PendingMigration.source s) (PendingMigration.step s command)
      (PendingMigration.source (PendingMigration.step s command).session) :=
  PendingMigration.step_refines s command valid

/-- Only the old source's observation fields matter here. This is an observer
translation, not an execution of an invented queue-free pending session. -/
def sourceOutcome (label : SourceLabel) : PendingMigration.Outcome :=
  {session := PendingMigration.initial .delay, status := .inspect,
   accepted := match label with | .admit _ x => some x | _ => none,
   business := match label with | .output _ y => some y | _ => none,
   cancellation := match label with | .prevent _ _ => some true | _ => none}

theorem DelayStep.erase {label : SourceLabel} {s t : DelaySource} (step : DelayStep label s t) :
    PendingMigration.SourceStep s.erase (sourceOutcome label) t.erase := by
  cases step with
  | internal s => exact .internal _ _ rfl rfl (by decide)
  | admit s identity input =>
    simpa [DelaySource.erase, sourceOutcome] using
      (PendingMigration.SourceStep.accept s.erase (sourceOutcome (.admit identity input)) input rfl rfl rfl)
  | prevent state identity input pre post =>
    simpa [DelaySource.erase, List.map_append] using
      (PendingMigration.SourceStep.prevent state input (pre.map Prod.snd) (post.map Prod.snd)
        (sourceOutcome (.prevent identity input)) rfl rfl rfl)
  | output state identity input rest =>
    simpa [DelaySource.erase] using
      (PendingMigration.SourceStep.publish state input (rest.map Prod.snd)
        (sourceOutcome (.output identity state)) rfl rfl rfl)

end FRPSpec.PendingCrash
