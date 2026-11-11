import Applications.Interaction.BehavioralCaller

/-! Behavioral correctness differs from arena legality; concrete boundary
translations lift one shared wire and retain every finite pending prefix. -/
namespace Examples.BehavioralGames
open Interaction Interaction.FiniteStrategies Interaction.OverlappingStrategies
open Interaction.OverlappingCaller Interaction.BehavioralTransport Interaction.BehavioralCaller

abbrev keep : Boundary arena := fun _ => id
abbrev flip : Boundary arena := fun _ b => !b

theorem simplify_left : Preserves keep flip negate forwarding := by intro i b; rfl
theorem simplify_right : Preserves flip keep negate forwarding := by intro i b; cases b <;> rfl
theorem restore_left : Preserves keep flip forwarding negate := by intro i b; cases b <;> rfl
theorem restore_right : Preserves flip keep forwarding negate := by intro i b; rfl

theorem relay_keep (xs : Relay) : mapRelay keep keep xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [mapRelay, mapEvents, relayMove, keep]

theorem hidden_simplification (wire : Wire) : hide (mapWire keep flip keep wire) = hide wire := by
  rw [hide_map, relay_keep]

/-- Concrete inhabited local certificates instantiate the general shared-witness
law, for all finite legal interactions, not only complete caller rounds. -/
theorem simplify_interaction (h : InteractionPlay negate negate wire) :
    ∃ lifted, InteractionPlay forwarding forwarding lifted ∧
      translate (fun _ => leftMoves) lifted = mapRelay keep flip (translate (fun _ => leftMoves) wire) ∧
      translate (fun _ => rightMoves) lifted = mapRelay flip keep (translate (fun _ => rightMoves) wire) ∧
      hide lifted = hide wire := by
  obtain ⟨lifted, hw, hl, hr, hh⟩ := interaction_compatible simplify_left simplify_right h
  exact ⟨lifted, hw, hl, hr, hh.trans (relay_keep _)⟩

/-- The second, nonidentity vertical stage uses the same middle wire produced
by the first. Both component certificates are pasted pointwise. -/
theorem twice_admissible (h : InteractionPlay negate negate wire) :
    InteractionPlay negate negate (mapWire keep flip keep (mapWire keep flip keep wire)) :=
  interaction_map restore_left restore_right (interaction_map simplify_left simplify_right h)

theorem twice_is_original (wire : Wire) :
    mapWire keep flip keep (mapWire keep flip keep wire) = wire := by
  induction wire with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [mapWire, mapEvents, wireMove, keep, flip]

/-- Interchange compares the actual two-stage witness with vertically pasted
boundary maps, then hiding. No computation-associativity theorem is used. -/
theorem concrete_interchange (wire : Wire) :
    hide (mapWire (fun i => keep i ∘ keep i) (fun i => flip i ∘ flip i)
      (fun i => keep i ∘ keep i) wire) = hide wire := by
  rw [interchange, relay_keep, relay_keep]

theorem pasted_left : Preserves (fun i => keep i ∘ keep i)
    (fun i => flip i ∘ flip i) negate negate := preserves_comp simplify_left restore_left

theorem pasted_right : Preserves (fun i => flip i ∘ flip i)
    (fun i => keep i ∘ keep i) negate negate := preserves_comp simplify_right restore_right

/-- Vertically pasted component certificates establish admissibility of the
same composed witness used by the structural interchange equation. -/
theorem vertical_interaction (h : InteractionPlay negate negate wire) :
    InteractionPlay negate negate
      (mapWire (fun i => keep i ∘ keep i) (fun i => flip i ∘ flip i)
        (fun i => keep i ∘ keep i) wire) ∧
    hide (mapWire (fun i => keep i ∘ keep i) (fun i => flip i ∘ flip i)
      (fun i => keep i ∘ keep i) wire) = hide wire :=
  ⟨interaction_map pasted_left pasted_right h, concrete_interchange wire⟩

/-- Contextual compatibility includes a prefix that ends before a B request
has propagated. This is not a caller block boundary. -/
def administrativePrefix : Wire := [(slot false, .aAsk)]

theorem administrative_legal : InteractionPlay negate negate administrativePrefix := by
  intro i
  by_cases h : i = slot false
  · subst i
    exact ⟨.aAsked, by simp [administrativePrefix, project]; exact .cons rfl .nil⟩
  · refine ⟨.idle, ?_⟩
    simpa [administrativePrefix, project, Ne.symm h] using
      (Path.nil : Path (wireStep (negate.response i) (negate.response i)) .idle [] .idle)

example : InteractionPlay forwarding forwarding (mapWire keep flip keep administrativePrefix) :=
  interaction_map simplify_left simplify_right administrative_legal

/-- Original consumer recovery and explicit accepted-environment coverage. -/
example : ∃ r w, forwarding.Play r ∧ InteractionPlay negate negate w ∧
    firstComparison (some ⟨none, .pending, .pending, OverlappingQueries.requests⟩) r ∧
    secondComparison r w ∧ observeWire w =
      some ⟨none, .pending, .pending, OverlappingQueries.requests⟩ :=
  accepted_coverage OverlappingQueries.both_pending

example (q : Schedule) : observeWire (network negate negate q) = OverlappingQueries.native q :=
  pasted_recovers q

/-- Independent local changes to the middle boundary cannot be joined. The
unchanged bad observer would leave the source's false B answer where the
forwarding target requires true. -/
theorem unmatched_middle_rejected :
    ¬ InteractionPlay forwarding forwarding (network negate negate [(true,true)]) := by
  intro h
  obtain ⟨q,hq⟩ := h (slot true)
  have bad := hq.execute_eq
  have rejected : FiniteStrategies.execute
      (wireStep (forwarding.response (slot true)) (forwarding.response (slot true))) .idle
      (project (slot true) (network negate negate [(true,true)])) = none := rfl
  rw [rejected] at bad
  cases bad

example : InteractionPlay negate negate (network negate negate [(true,true)]) :=
  network_legal _ _ OverlappingQueries.right_only

example : ¬ CoversAccepted (fun _ => ∅) := empty_fails_coverage
example : ¬ CoversAccepted silent := silent_fails_coverage

end Examples.BehavioralGames
