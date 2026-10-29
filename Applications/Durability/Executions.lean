import Applications.Durability.Encoding

namespace Durability

abbrev invokeState (s : Machine P) (e : Record P) : Machine P := { s with active := some e }
abbrev prepareState (s : Machine P) (p : Plan P) : Machine P :=
  { s with pending := some p, buffered := (fun _ => none), used := s.used ∪ {i | ∃ c, p.writes i = some c} }
abbrev writeState (s : Machine P) (i : Nat) (c : Cell P) : Machine P :=
  { s with buffered := put s.buffered i c }
abbrev persistState (s : Machine P) (i : Nat) (c : Cell P) : Machine P :=
  { s with disk := put s.disk i c }
abbrev publishState (s : Machine P) (p : Plan P) : Machine P :=
  { s with root := p.root, cache := some p.after, pending := none, buffered := fun _ => none }
abbrev acknowledgeState (s : Machine P) : Machine P := { s with active := none }
abbrev crashState (s : Machine P) : Machine P :=
  { s with cache := none, active := none, pending := none, buffered := (fun _ => none), cursor := none }

/-- Constructive execution of a fresh append through the actual layout builder.
This supplies inhabited successful traces, not merely a safety implication. -/
theorem append_execution {P : Type} (s : Machine P) (h : List (Record P))
    (ready : s.cache = some h) (idle : s.active = none) (noplan : s.pending = none)
    (rep : Represents s.disk s.root h) (a : Nat) (e : Record P)
    (space : s.disk a = none) (unused : a ∉ s.used) (fresh : Fresh h e) :
    let p := appendPlan s.disk s.root h rep a e space
    let prepared := prepareState (invokeState s e) p
    let written := writeState prepared a (.node s.root.tail e)
    let persisted := persistState written a (.node s.root.tail e)
    Interaction.Events.interpret Step
      [.invoke e, .internal, .internal, .internal, .commit e, .acknowledge e] s
      (acknowledgeState (publishState persisted p)) := by
  dsimp only
  let p := appendPlan s.disk s.root h rep a e space
  let u := prepareState (invokeState s e) p
  let v := writeState u a (.node s.root.tail e)
  let w := persistState v a (.node s.root.tail e)
  have prep : Step .internal (invokeState s e) u := by
    apply Step.prepare (s := invokeState s e) (p := p) ready noplan rfl rfl rfl
    · intro r eq
      have eq' : e = r := Option.some.inj eq
      subst r; exact fresh
    · intro i c hw
      by_cases eq : i = a
      · simpa [eq] using unused
      · simp [p, appendPlan, put, eq] at hw
  have wr : Step .internal u v := Step.write rfl (by simp [p, appendPlan, put])
  have per : Step .internal v w := Step.persist rfl (by simp [p, appendPlan, put])
    (by simp [v, put]) (Or.inl space)
  have pub : Step (.commit e) w (publishState w p) := by
    apply Step.publish (p := p) rfl
    intro i c hw
    by_cases eq : i = a
    · subst i
      have same : Cell.node s.root.tail e = c := by simpa [p, appendPlan, put] using hw
      subst c
      simp [w, put]
    · simp [p, appendPlan, put, eq] at hw
  have ack : Step (.acknowledge e) (publishState w p) (acknowledgeState (publishState w p)) :=
    Step.acknowledge rfl rfl rfl (by simp [p, appendPlan])
  exact ⟨invokeState s e, Step.invoke ready idle noplan,
    u, prep, v, wr, w, per, publishState w p, pub, _, ack, rfl⟩

/-- Query correctness after any completed recovery follows from the common
observer, independently of log versus checkpoint layout. -/
theorem recovered_query {P : Type} {s t : Machine P} {a : Abstract P} {h}
    (rel : Related s a) (step : Step (.recover h) s t) :
    h = a.history ∧ t.cache = some a.history := by
  obtain ⟨b, spec, after⟩ := step.simulation rel
  cases spec with
  | recover offline => exact ⟨rfl, by simpa using after.cache⟩

end Durability
