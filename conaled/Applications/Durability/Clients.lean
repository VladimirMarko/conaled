import Applications.Durability.Simulation

namespace Durability

/-- Every observable source step preserves the ordered committed prefix. -/
theorem SpecStep.prefix {P : Type} {ev} {a b : Abstract P}
    (step : SpecStep ev a b) : ∃ suffix, b.history = a.history ++ suffix := by
  cases step with
  | commit => exact ⟨[_], rfl⟩
  | _ => exact ⟨[], by simp⟩

theorem spec_script_prefix {P : Type} {events : List (Event P)} {a b : Abstract P}
    (run : Interaction.Events.interpret SpecStep events a b) :
    ∃ suffix, b.history = a.history ++ suffix := by
  induction events generalizing a with
  | nil => cases run; exact ⟨[], by simp⟩
  | cons ev events ih =>
    obtain ⟨mid, first, rest⟩ := run
    obtain ⟨xs, hx⟩ := first.prefix
    obtain ⟨ys, hy⟩ := ih rest
    exact ⟨xs ++ ys, by rw [hy, hx, List.append_assoc]⟩

theorem SpecStep.no_duplicate_commit {P : Type} {a b : Abstract P} {e}
    (already : e ∈ a.history) : ¬ SpecStep (.commit e) a b := by
  intro step
  cases step with
  | commit online active fresh => exact fresh e already rfl

theorem SpecStep.keys_unique {P : Type} {a b : Abstract P} {ev}
    (step : SpecStep ev a b) (unique : (a.history.map Record.key).Nodup) :
    (b.history.map Record.key).Nodup := by
  cases step with
  | commit online active fresh =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨unique, by simp, ?_⟩
    intro key mem key' mem'
    simp only [List.mem_singleton] at mem'
    subst key'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp mem
    exact fresh r hr
  | _ => exact unique

theorem spec_script_unique {P : Type} {events : List (Event P)} {a b : Abstract P}
    (run : Interaction.Events.interpret SpecStep events a b)
    (unique : (a.history.map Record.key).Nodup) : (b.history.map Record.key).Nodup := by
  induction events generalizing a with
  | nil => cases run; exact unique
  | cons ev events ih =>
    obtain ⟨mid, first, rest⟩ := run
    exact ih rest (first.keys_unique unique)

/-- An acknowledged record survives every later finite execution, including
arbitrary repeated crashes. It retains position because the entire prefix does. -/
theorem acknowledged_survives {P : Type} {a b c : Abstract P} {e events}
    (ack : SpecStep (.acknowledge e) a b)
    (later : Interaction.Events.interpret SpecStep events b c) :
    e ∈ c.history ∧ ∃ suffix, c.history = a.history ++ suffix := by
  cases ack with
  | acknowledge online active mem =>
    obtain ⟨suffix, eq⟩ := spec_script_prefix later
    exact ⟨by rw [eq]; simp [mem], suffix, eq⟩

/-- The ordered-fold client is independent of layout and payload commutativity. -/
theorem Related.fold {P M : Type} {s : Machine P} {a : Abstract P}
    (rel : Related s a) {h} (ready : s.cache = some h)
    (f : M → Record P → M) (seed : M) : h.foldl f seed = a.history.foldl f seed := by
  rw [(rel.ready ready).2]

def sourceBehaviors {P : Type} (events : List (Event P)) : Set (Abstract P) :=
  {a | Interaction.Events.interpret SpecStep events initialAbstract a}

def targetBehaviors {P : Type} (events : List (Event P)) : Set (Machine P) :=
  {s | Interaction.Events.interpret Step events initial s}

/-- Reuse the repository's observation-refinement interface, not an equality of
storage representations. -/
theorem history_refinement {P : Type} (events : List (Event P)) :
    Interaction.Refines (fun a s => Related s a)
      (sourceBehaviors events) (targetBehaviors events) := by
  intro s run
  exact script_simulation events related_initial run

/-- A single client proof transported through either concrete layout. -/
theorem unique_client {P : Type} (events : List (Event P)) :
    ∀ s ∈ targetBehaviors events, ∀ h, s.cache = some h → (h.map Record.key).Nodup := by
  apply (history_refinement events).property
    (P := fun a => (a.history.map Record.key).Nodup)
    (Q := fun s => ∀ h, s.cache = some h → (h.map Record.key).Nodup)
  · intro a run
    exact spec_script_unique run (by simp [initialAbstract])
  · intro a s rel unique h ready
    simpa [(rel.ready ready).2] using unique

/-- One observer transport covers ordered folds, identities and acknowledged
prefix properties. It imposes no representation-specific client premise. -/
theorem history_client {P : Type} (events : List (Event P)) (Q : List (Record P) → Prop)
    (source : ∀ a ∈ sourceBehaviors events, Q a.history) :
    ∀ s ∈ targetBehaviors events, ∀ h, s.cache = some h → Q h := by
  apply (history_refinement events).property (P := fun a => Q a.history)
    (Q := fun s => ∀ h, s.cache = some h → Q h) source
  intro a s rel property h ready
  exact (rel.ready ready).2 ▸ property

/-- Acknowledgment survival is transported once for all layouts and failure
histories, retaining payload identity as well as the committed prefix. -/
theorem acknowledged_client {P : Type} (before after : List (Event P)) (e : Record P) :
    ∀ s ∈ targetBehaviors (before ++ .acknowledge e :: after),
      ∀ h, s.cache = some h → e ∈ h := by
  apply history_client _ (fun h => e ∈ h)
  intro a run
  change Interaction.Events.interpret SpecStep (before ++ .acknowledge e :: after) initialAbstract a at run
  rw [Interaction.Events.interpret_append] at run
  obtain ⟨mid, first, next, ack, rest⟩ := run
  exact (acknowledged_survives ack rest).1

end Durability
