import Applications.Interaction.BehavioralCaller

/-! Finite diagnostic replay delegates every local transition to wireStep. -/
namespace Interaction.PrefixDiagnostics
open FiniteStrategies OverlappingStrategies OverlappingCaller BehavioralCaller

abbrev Stages := Fin arena.slots → Stage

def updateStage (states : Stages) (i : Fin arena.slots) (q : Stage) : Stages :=
  fun j => if j = i then q else states j

def dispatch (s t : Strategy arena) (states : Stages) (event : Event arena WireMove) : Option Stages :=
  (wireStep (s.response event.1) (t.response event.1) (states event.1) event.2).map
    (updateStage states event.1)

/-- Contains no duplicate client-state machine. Ordered history is retained
because stages reset after delivery and do not retain the delivered value. -/
structure Detailed where
  stages : Stages
  history : Wire

def inspect (s t : Strategy arena) (wire : Wire) : Option Detailed :=
  (FiniteStrategies.execute (dispatch s t) (fun _ => .idle) wire).map (fun states => ⟨states, wire⟩)

theorem execute_path (h : FiniteStrategies.execute step start xs = some finish) :
    Path step start xs finish := by
  induction xs generalizing start with
  | nil => simp [FiniteStrategies.execute] at h; cases h; exact .nil
  | cons m ms ih =>
    simp only [FiniteStrategies.execute] at h
    cases hs : step start m with
    | none => simp [hs] at h
    | some mid =>
      simp only [hs, Option.bind_some] at h
      exact .cons hs (ih h)

/-- Global replay is only dispatch of the existing local transition systems. -/
theorem projects {s t : Strategy arena} (h : Path (dispatch s t) start xs finish)
    (i : Fin arena.slots) :
    Path (wireStep (s.response i) (t.response i)) (start i) (project i xs) (finish i) := by
  induction h with
  | nil => exact .nil
  | @cons st ev mid tail final hs ht ih =>
    rcases ev with ⟨j,m⟩
    unfold dispatch at hs
    cases localStep : wireStep (s.response j) (t.response j) (st j) m with
    | none => simp [localStep] at hs
    | some q =>
      simp only [localStep, Option.map_some, Option.some.injEq] at hs
      subst mid
      by_cases e : j = i
      · subst j
        simp only [updateStage, ite_true] at ih
        simpa [project] using Path.cons localStep ih
      · simpa [project, e, updateStage, Ne.symm e] using ih

/-- Matched local paths determine a single globally ordered interleaving. -/
theorem assemble {s t : Strategy arena} (h : ∀ i,
    Path (wireStep (s.response i) (t.response i)) (start i) (project i xs) (finish i)) :
    Path (dispatch s t) start xs finish := by
  induction xs generalizing start with
  | nil =>
    have e : start = finish := by
      funext i
      have hi := h i
      exact (hi.deterministic Path.nil).symm
    cases e
    exact .nil
  | cons ev xs ih =>
    rcases ev with ⟨j,m⟩
    have hj : Path (wireStep (s.response j) (t.response j))
        (start j) (m :: project j xs) (finish j) := by simpa [project] using h j
    cases hj with
    | @cons _ _ q _ _ step tail =>
      apply Path.cons (t := updateStage start j q)
      · simp [dispatch, step]
      · apply ih
        intro i
        by_cases e : j = i
        · subst i
          simpa [updateStage] using tail
        · have hi := h i
          simpa [project, e, updateStage, Ne.symm e] using hi

theorem inspect_characterization {s t : Strategy arena} {wire : Wire} {d : Detailed} :
    inspect s t wire = some d ↔ d.history = wire ∧
      ∀ i, Path (wireStep (s.response i) (t.response i)) .idle (project i wire) (d.stages i) := by
  constructor
  · intro h
    unfold inspect at h
    cases run : FiniteStrategies.execute (dispatch s t) (fun _ => .idle) wire with
    | none => simp [run] at h
    | some states =>
      simp only [run, Option.map_some, Option.some.injEq] at h
      cases h
      exact ⟨rfl, fun i => projects (execute_path run) i⟩
  · rintro ⟨history, paths⟩
    have run := (assemble paths).execute_eq
    cases d
    simp_all [inspect]

theorem accepted_iff (s t : Strategy arena) (wire : Wire) :
    (∃ d, inspect s t wire = some d) ↔ InteractionPlay s t wire := by
  constructor
  · rintro ⟨d,h⟩ i
    exact ⟨d.stages i, (inspect_characterization.mp h).2 i⟩
  · intro h
    classical
    let finish : Stages := fun i => Classical.choose (h i)
    have paths : ∀ i, Path (wireStep (s.response i) (t.response i))
        .idle (project i wire) (finish i) := fun i => Classical.choose_spec (h i)
    exact ⟨⟨finish,wire⟩, inspect_characterization.mpr ⟨rfl,paths⟩⟩

theorem unique (h : inspect s t wire = some d) (k : inspect s t wire = some e) : d = e :=
  Option.some.inj (h.symm.trans k)

theorem endpoint_unique (h : inspect s t wire = some d)
    (path : Path (wireStep (s.response i) (t.response i)) .idle (project i wire) endpoint) :
    endpoint = d.stages i := path.deterministic ((inspect_characterization.mp h).2 i)

/-- The detailed endpoint also explains the existing relay-visible phase.
This observation boundary still includes service requests and replies. -/
theorem relay_projection (h : inspect s t wire = some d) (i : Fin arena.slots) :
    Path (relayStep (s.response i ∘ t.response i)) .idle
      (project i (hide wire)) (outerState (s.response i) (t.response i) (d.stages i)) := by
  rw [hide, project_translate]
  exact ((inspect_characterization.mp h).2 i).project
    (outerState (s.response i) (t.response i)) hideMiddle (fun _ _ _ => hide_local)

/-- Projection replays the existing native client evaluator over retained history. -/
def Detailed.external (d : Detailed) : Output := observeWire d.history

theorem projection_history (h : inspect s t wire = some d) : d.external = observeWire wire := by
  rw [Detailed.external, (inspect_characterization.mp h).1]

end Interaction.PrefixDiagnostics
