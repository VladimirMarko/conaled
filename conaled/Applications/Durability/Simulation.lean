import Applications.Durability.Protocol

namespace Durability

/-- Primitive storage/recovery transitions simulate the independent history
contract. Layout correctness is established by appendPlan/checkpointPlan;
publication uses only completed writes, not a history-equality guard. -/
theorem Step.simulation {P : Type} {s t : Machine P} {a : Abstract P} {ev}
    (step : Step ev s t) (rel : Related s a) :
    ∃ b, SpecStep ev a b ∧ Related t b := by
  cases step with
  | invoke hc ha hp =>
    obtain ⟨online, rfl⟩ := rel.ready hc
    refine ⟨_, .invoke online (rel.active.symm.trans ha), ?_⟩
    refine { root := rel.root, cache := rel.cache, active := rfl, pending := ?_, cursor := rel.cursor, cursor_offline := rel.cursor_offline, offline_pending := ?_, offline_active := ?_ }
    · simp [hp]
    · simp [online]
    · simp [online]
  | @prepare _ h p hc hp source before appended fresh unused =>
    obtain ⟨online, rfl⟩ := rel.ready hc
    refine ⟨a, .internal, ?_⟩
    refine { root := rel.root, cache := rel.cache, active := rel.active, pending := ?_, cursor := rel.cursor, cursor_offline := rel.cursor_offline, offline_pending := ?_, offline_active := rel.offline_active }
    · intro q eq
      cases Option.some.inj eq
      exact ⟨before, appended.trans rel.active, source ▸ Extends.refl _, fresh, online⟩
    · simp [online]
  | write hp hw =>
    exact ⟨a, .internal, { rel with }⟩
  | @persist _ p i c hp hw hb compat =>
    obtain ⟨before, appended, source, fresh, online⟩ := rel.pending p hp
    have ext := put_compatible compat
    have noCursor := rel.noCursor online
    refine ⟨a, .internal, { root := rel.root.mono ext, cache := rel.cache, active := rel.active, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := rel.offline_active }⟩
    · intro q eq
      have equal : q = p := Option.some.inj (eq.symm.trans hp)
      subst q
      exact ⟨before, appended, source.trans ext, fresh, online⟩
    · simp [noCursor]
    · simp [noCursor]
    · simp [online]
  | @publish _ p hp persisted =>
    obtain ⟨before, appended, source, fresh, online⟩ := rel.pending p hp
    have noCursor := rel.noCursor online
    have valid := p.valid.mono (overlay_extends persisted source)
    have shape := p.shape
    cases eq : p.appended with
    | none =>
      have after : p.after = a.history := by simpa [eq, before] using shape
      refine ⟨a, ?_, { root := after ▸ valid, cache := ?_, active := rel.active, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := rel.offline_active }⟩
      · simp; exact .internal
      · simp [after, online]
      · simp
      · simp [noCursor]
      · simp [noCursor]
      · simp
    | some e =>
      have active : a.active = some e := appended.symm.trans eq
      have after : p.after = a.history ++ [e] := by simpa [eq, before] using shape
      refine ⟨{ a with history := a.history ++ [e] }, ?_, ?_⟩
      · simp; exact .commit online active (fresh e eq)
      · refine { root := after ▸ valid, cache := ?_, active := rel.active, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := ?_ }
        · simp [after, online]
        · simp
        · simp [noCursor]
        · simp [noCursor]
        · simp
        · simp [online]
  | acknowledge hc ha hp mem =>
    obtain ⟨online, rfl⟩ := rel.ready hc
    refine ⟨_, .acknowledge online (rel.active.symm.trans ha) mem, ?_⟩
    refine { root := rel.root, cache := rel.cache, active := rfl, pending := ?_, cursor := rel.cursor, cursor_offline := rel.cursor_offline, offline_pending := ?_, offline_active := ?_ }
    · simp [hp]
    · simp [hp]
    · simp
  | reject hc ha hp mem key different =>
    obtain ⟨online, rfl⟩ := rel.ready hc
    refine ⟨_, .reject online (rel.active.symm.trans ha) mem key different, ?_⟩
    refine { root := rel.root, cache := rel.cache, active := rfl, pending := ?_, cursor := rel.cursor, cursor_offline := rel.cursor_offline, offline_pending := ?_, offline_active := ?_ }
    · simp [hp]
    · simp [hp]
    · simp
  | query hc ha hp =>
    obtain ⟨online, rfl⟩ := rel.ready hc
    exact ⟨a, .query online (rel.active.symm.trans ha), rel⟩
  | crash =>
    refine ⟨_, .crash, { root := rel.root, cache := rfl, active := rfl, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := ?_ }⟩ <;> simp
  | startRead hc hcur start =>
    have offline := rel.offline hc
    refine ⟨a, .internal, { root := rel.root, cache := rel.cache, active := rel.active, pending := rel.pending, cursor := ?_, cursor_offline := ?_, offline_pending := rel.offline_pending, offline_active := rel.offline_active }⟩
    · intro c eq; cases Option.some.inj eq
      exact start.correct rel.root
    · intro c eq; exact offline
  | read hc hcur rd =>
    have offline := rel.offline hc
    refine ⟨a, .internal, { root := rel.root, cache := rel.cache, active := rel.active, pending := rel.pending, cursor := ?_, cursor_offline := ?_, offline_pending := rel.offline_pending, offline_active := rel.offline_active }⟩
    · intro c eq; cases Option.some.inj eq
      exact rd.preserves (rel.cursor _ hcur)
    · intro c eq; exact offline
  | recover hc hcur =>
    have offline := rel.offline hc
    have rep := rel.cursor _ hcur
    cases rep
    refine ⟨_, .recover offline, { root := rel.root, cache := rfl, active := rel.active, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := ?_ }⟩
    · simp [rel.offline_pending offline]
    · simp
    · simp
    · simp
    · simp
  | reclaim hc ha hp keep subset =>
    obtain ⟨online, rfl⟩ := rel.ready hc
    have noCursor := rel.noCursor online
    refine ⟨a, .internal, { root := rel.root.keep keep, cache := rel.cache, active := rel.active, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := rel.offline_active }⟩
    · simp [hp]
    · simp [noCursor]
    · simp [noCursor]
    · simp [hp]

/-- Existing finite-script simulation supplies the composition proof. -/
theorem script_simulation {P : Type} (events : List (Event P))
    {s t : Machine P} {a : Abstract P} (rel : Related s a)
    (run : Interaction.Events.interpret Step events s t) :
    ∃ b, Interaction.Events.interpret SpecStep events a b ∧ Related t b :=
  Interaction.Events.interpret_simulation Step SpecStep Related
    (fun _ _ _ _ h step => step.simulation h) events rel run

end Durability
