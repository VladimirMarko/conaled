import Applications.Interaction.FiniteStrategies

/-! Environment-sensitive selected executions of the finite strategy protocol. -/
namespace Interaction.FiniteStrategies
open FiniteQueries

def serviceMoves : WireMove → List Move
  | .cAsk => [.ask] | .cReply b => [.reply b] | _ => []

def relayServiceMoves : RelayMove → List Move
  | .rightAsk => [.ask] | .rightReply b => [.reply b] | _ => []

theorem service_hiding (xs : List WireMove) :
    (xs.flatMap hideMiddle).flatMap relayServiceMoves = xs.flatMap serviceMoves := by
  induction xs with
  | nil => rfl
  | cons m xs ih => cases m <;> simp [hideMiddle, relayServiceMoves, serviceMoves, ih]

/-- A finite client drives the two-component protocol against an adaptive
responder. Internal matching moves are actually emitted before they are hidden. -/
def network (env : Environment) (f g : Bool → Bool) :
    Nat → Bool → List Bool → Option Bool × List WireMove
  | 0, last, _ => (some last, [])
  | n+1, _, h => match env h with
    | none => (none, [.aAsk, .bAsk, .cAsk])
    | some b => let out := network env f g n (f (g b)) (h ++ [b])
                (out.1, wireRound f g b ++ out.2)

def observe (out : Option Bool × List WireMove) : Outcome :=
  (out.1, out.2.flatMap serviceMoves)

theorem network_legal (env : Environment) (f g : Bool → Bool) (n : Nat)
    (last : Bool) (h : List Bool) :
    ∃ t, Path (wireStep f g) .idle (network env f g n last h).2 t := by
  induction n generalizing last h with
  | zero => exact ⟨_, .nil⟩
  | succ n ih =>
    cases he : env h with
    | none => exact ⟨.waiting, by
        simp only [network, he]
        exact .cons rfl (.cons rfl (.cons rfl .nil))⟩
    | some b =>
      obtain ⟨t, hp⟩ := ih (f (g b)) (h ++ [b])
      exact ⟨t, by simpa only [network, he] using (wire_round f g b).append hp⟩

/-- Policy changes alter returned values but retain the raw service history. -/
theorem network_native (env : Environment) (f g : Bool → Bool) (n : Nat)
    (last : Bool) (h : List Bool) :
    observe (network env f g n (f (g last)) h) =
      ((native env n last h).1.map (f ∘ g), (native env n last h).2) := by
  induction n generalizing last h with
  | zero => rfl
  | succ n ih =>
    cases he : env h with
    | none => simp [network, native, he, observe, serviceMoves]
    | some b =>
      have hp := ih b (h ++ [b])
      have hr := congrArg Prod.fst hp
      have ht := congrArg Prod.snd hp
      simp only [observe] at hr ht
      simp [network, native, he, observe, wireRound, serviceMoves, hr, ht]

theorem forwarding_native (env : Environment) (n : Nat) (last : Bool) (h : List Bool) :
    observe (network env id id n last h) = native env n last h := by
  simpa using network_native env id id n last h

theorem forwarding_handler (env : Environment) (n : Nat) (last : Bool) (h : List Bool) :
    observe (network env id id n last h) = handler env n last h [] := by
  rw [forwarding_native, handler_native]
  simp

/-- The selected execution has two legal component projections and a legal
hidden composition, while retaining the complete native result. -/
theorem selected_contract (env : Environment) (n : Nat) (last : Bool) (h : List Bool) :
    let out := network env id id n last h
    RelayPlay id (out.2.flatMap leftMoves) ∧
    RelayPlay id (out.2.flatMap rightMoves) ∧
    CompositePlay id id (out.2.flatMap hideMiddle) ∧ observe out = native env n last h := by
  obtain ⟨t, ht⟩ := network_legal env id id n last h
  obtain ⟨hl, hr⟩ := components ht
  exact ⟨hl, hr, ⟨_, t, ht, rfl⟩, forwarding_native env n last h⟩

/-- The new reply cannot be matched with a different middle-channel reply. -/
theorem unmatched_middle : wireStep id id (.cAnswered false) (.bReply true) = none := rfl

/-- A second service query before forwarding the first response is rejected. -/
theorem duplicate_query_rejected : relayStep id (.answered false) .rightAsk = none := rfl

/-- Returning a cached answer without the newly requested service call is rejected. -/
theorem cached_reply_rejected : relayStep id .requested (.leftReply false) = none := rfl

end Interaction.FiniteStrategies
