import Applications.Interaction.PrefixClientObservation

/-! Diagnostic interpretation retains the actual shared witness and endpoints. -/
namespace Interaction.PrefixDiagnostics
open FiniteStrategies OverlappingStrategies OverlappingCaller BehavioralCaller BehavioralTransport

def Detailed.interpret (a b c : Boundary arena) (d : Detailed) : Detailed where
  stages i := wireState (c i) (d.stages i)
  history := mapWire a b c d.history

/-- The observer's exact endpoint equation comes from the existing wire_path
interpretation, not merely preservation of membership in a trace language. -/
theorem inspect_interpret {a b c : Boundary arena} {s t s' t' : Strategy arena}
    (left : Preserves a b s s') (right : Preserves b c t t')
    (h : inspect s t wire = some d) :
    inspect s' t' (mapWire a b c wire) = some (d.interpret a b c) := by
  obtain ⟨history, paths⟩ := inspect_characterization.mp h
  apply inspect_characterization.mpr
  constructor
  · simp [Detailed.interpret, history]
  · intro i
    rw [mapWire, project_mapEvents]
    exact wire_path (left i) (right i) (paths i)

abbrev keep : Boundary arena := fun _ => id
abbrev flip : Boundary arena := fun _ b => !b

theorem mapRelay_keep (xs : Relay) : mapRelay keep keep xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [mapRelay, mapEvents, relayMove, keep]

theorem middle_external (d : Detailed) (b : Boundary arena) :
    (d.interpret keep b keep).external = d.external := by
  unfold Detailed.external Detailed.interpret observeWire
  rw [hide_map, mapRelay_keep]

theorem middle_stages (d : Detailed) (b : Boundary arena) :
    (d.interpret keep b keep).stages = d.stages := by
  funext i
  change wireState id (d.stages i) = d.stages i
  cases d.stages i <;> rfl

theorem simplify_left : Preserves keep flip negate forwarding := by intro i b; rfl
theorem simplify_right : Preserves flip keep negate forwarding := by intro i b; cases b <;> rfl
theorem restore_left : Preserves keep flip forwarding negate := by intro i b; cases b <;> rfl
theorem restore_right : Preserves flip keep forwarding negate := by intro i b; rfl

/-- A concrete nonidentity interpretation changes middle-value history but
retains stage endpoints and the complete external client observation. -/
theorem simplify_observer (h : inspect negate negate wire = some d) :
    inspect forwarding forwarding (mapWire keep flip keep wire) = some (d.interpret keep flip keep) ∧
    (d.interpret keep flip keep).stages = d.stages ∧
    (d.interpret keep flip keep).external = d.external :=
  ⟨inspect_interpret simplify_left simplify_right h, middle_stages _ _, middle_external _ _⟩

theorem twice_history (wire : Wire) : mapWire keep flip keep (mapWire keep flip keep wire) = wire := by
  induction wire with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [mapWire, mapEvents, wireMove, keep, flip]

theorem twice_detailed (d : Detailed) :
    (d.interpret keep flip keep).interpret keep flip keep = d := by
  have stages : ((d.interpret keep flip keep).interpret keep flip keep).stages = d.stages :=
    (middle_stages _ _).trans (middle_stages _ _)
  have history : ((d.interpret keep flip keep).interpret keep flip keep).history = d.history :=
    twice_history d.history
  cases d
  simp_all [Detailed.interpret]

/-- Both stages run on the same explicitly translated wire. -/
theorem twice_inspect (h : inspect negate negate wire = some d) :
    inspect negate negate (mapWire keep flip keep (mapWire keep flip keep wire)) = some d := by
  have first := inspect_interpret simplify_left simplify_right h
  have second := inspect_interpret restore_left restore_right first
  simpa only [twice_detailed] using second

/-- The pre-existing shared-witness theorem supplies both component projections;
the new observer assigns a valid external observation to that same witness. -/
theorem shared_observed_witness (h : inspect negate negate wire = some d) :
    ∃ lifted observed, inspect forwarding forwarding lifted = some observed ∧
      translate (fun _ => leftMoves) lifted = mapRelay keep flip (translate (fun _ => leftMoves) wire) ∧
      translate (fun _ => rightMoves) lifted = mapRelay flip keep (translate (fun _ => rightMoves) wire) ∧
      observed.external = d.external := by
  have legal := (accepted_iff negate negate wire).mp ⟨d,h⟩
  obtain ⟨lifted, hl, left, right, hidden⟩ := interaction_compatible simplify_left simplify_right legal
  obtain ⟨observed, ho⟩ := (accepted_iff forwarding forwarding lifted).mpr hl
  refine ⟨lifted, observed, ho, left, right, ?_⟩
  rw [projection_history ho, projection_history h]
  unfold observeWire
  rw [hidden, mapRelay_keep]

/-- External compatibility of vertically composed boundary interpretations is
inherited from the exact shared-wire interchange law. -/
theorem two_stage_external (wire : Wire) :
    observeWire (mapWire (fun i => keep i ∘ keep i) (fun i => flip i ∘ flip i)
      (fun i => keep i ∘ keep i) wire) = observeWire wire := by
  unfold observeWire
  rw [interchange, mapRelay_keep, mapRelay_keep]

end Interaction.PrefixDiagnostics
