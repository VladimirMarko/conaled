import Applications.Interaction.OverlappingCaller
import Applications.Interaction.OverlappingArenaLaws

/-! Ordinary callers of the finite-slot game API, including rejected positions. -/
namespace Examples.OverlappingStrategies
open Interaction Interaction.FiniteStrategies Interaction.OverlappingStrategies
open Interaction.OverlappingCaller

def twoPending : List (Event arena RelayMove) :=
  [(slot false,.leftAsk),(slot true,.leftAsk)]

/-- Two Opponent questions are legal consecutively on distinct slots. -/
theorem overlap_legal : forwarding.Play twoPending := by
  intro i
  have hi : i = slot false ∨ i = slot true := by
    have := i.isLt
    simp only [slot, Bool.false_eq_true, ↓reduceIte]
    change i.val < 2 at this
    omega
  rcases hi with rfl | rfl
  all_goals exact ⟨.requested, .cons rfl .nil⟩

theorem overlap_arena_legal :
    arena.Legal (translate (fun _ => clientBoundary) twoPending) :=
  (forwarding.boundaries overlap_legal).1

/-- Erasing correlation does not turn the overlapping play into a serial play. -/
theorem serial_cannot_accept_overlap : ¬ RelayPlay id [.leftAsk,.leftAsk] :=
  rejected_not_play rfl

private theorem reject_slot (s : Strategy arena) (i : Fin arena.slots)
    (h : execute (relayStep (s.response i)) .idle (project i xs) = none) : ¬ s.Play xs := by
  intro hp
  exact rejected_not_play h (hp i)

theorem unmatched_rejected :
    ¬ forwarding.Play [(slot false,.rightReply true)] :=
  reject_slot forwarding (slot false) rfl

theorem wrong_slot_rejected : ¬ forwarding.Play
    [(slot false,.leftAsk),(slot false,.rightAsk),(slot true,.rightReply true)] :=
  reject_slot forwarding (slot true) rfl

theorem duplicate_rejected : ¬ forwarding.Play
    [(slot false,.leftAsk),(slot false,.rightAsk),
      (slot false,.rightReply true),(slot false,.rightReply true)] :=
  reject_slot forwarding (slot false) rfl

theorem illegal_order_rejected :
    ¬ forwarding.Play [(slot false,.rightAsk)] :=
  reject_slot forwarding (slot false) rfl

/-- A caller supplies a schedule, obtains a legal three-channel interaction, and
uses the reusable client observation theorem. -/
theorem ordinary_network :
    InteractionPlay forwarding forwarding
      (network forwarding forwarding [(true,true),(false,false)]) :=
  network_legal _ _ OverlappingQueries.right_first

theorem ordinary_result :
    clientRun forwarding forwarding [(true,true),(false,false)] =
      some ⟨some false,.answered false,.answered true,
        OverlappingQueries.trace [(true,true),(false,false)]⟩ := by
  rw [client_native]
  exact OverlappingQueries.right_first

theorem ordinary_pending : clientRun forwarding forwarding [(true,true)] =
    some ⟨none,.pending,.answered true,OverlappingQueries.trace [(true,true)]⟩ := by
  rw [client_native]
  exact OverlappingQueries.right_only

theorem same_result_different_history :
    (clientRun forwarding forwarding [(true,true),(false,false)]).map
        OverlappingQueries.Observation.result =
      (clientRun forwarding forwarding [(false,false),(true,true)]).map
        OverlappingQueries.Observation.result ∧
    clientRun forwarding forwarding [(true,true),(false,false)] ≠
      clientRun forwarding forwarding [(false,false),(true,true)] := by
  simp only [client_native]
  exact ⟨OverlappingQueries.equal_results, OverlappingQueries.different_interactions⟩

end Examples.OverlappingStrategies
