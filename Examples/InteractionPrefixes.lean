import Applications.Interaction.PrefixInterpretation

/-! Diagnostic and external observations separate internal propagation from
client-visible progress on actual finite traces. -/
namespace Examples.InteractionPrefixes
open Interaction Interaction.FiniteStrategies Interaction.OverlappingStrategies
open Interaction.OverlappingCaller Interaction.BehavioralCaller Interaction.PrefixDiagnostics
open Interaction.OverlappingQueries

abbrev ff := forwarding

def asked : Wire := [(slot false,.aAsk)]
def forwarded : Wire := asked ++ [(slot false,.bAsk)]
def buffered : Wire := forwarded ++ [(slot false,.cAsk),(slot false,.cReply true)]
def delivered : Wire := buffered ++ [(slot false,.bReply true),(slot false,.aReply true)]

def stagePair (d : Detailed) : Stage × Stage := (d.stages (slot false), d.stages (slot true))
def leftStage (wire : Wire) := (inspect ff ff wire).map (fun d => d.stages (slot false))

example : leftStage asked = some .aAsked := rfl
example : leftStage forwarded = some .bAsked := rfl
example : leftStage buffered = some (.cAnswered true) := rfl
example : leftStage delivered = some .idle := rfl

theorem asked_accepted : ∃ d, inspect ff ff asked = some d := ⟨_,rfl⟩
theorem forwarded_accepted : ∃ d, inspect ff ff forwarded = some d := ⟨_,rfl⟩
theorem buffered_accepted : ∃ d, inspect ff ff buffered = some d := ⟨_,rfl⟩
theorem delivered_accepted : ∃ d, inspect ff ff delivered = some d := ⟨_,rfl⟩

theorem unchanged_hiding : hide asked = hide forwarded := rfl

/-- Hiding erases a real transition, not an illegal or rejected input. -/
theorem cannot_recover_stage : ¬ ∃ recover : Relay → Option Stage,
    ∀ wire, InteractionPlay ff ff wire → recover (hide wire) = leftStage wire := by
  rintro ⟨recover,h⟩
  have a := h asked ((accepted_iff ff ff asked).mp asked_accepted)
  have b := h forwarded ((accepted_iff ff ff forwarded).mp forwarded_accepted)
  have bad : (some Stage.aAsked : Option Stage) = some .bAsked := a.symm.trans b
  cases bad

example : observeWire asked = some ⟨none, .pending, .idle, [.ask false]⟩ := rfl
example : observeWire forwarded = observeWire asked := rfl
example : observeWire buffered = some ⟨none, .pending, .idle, [.ask false]⟩ := rfl

/-- The service reply appears at the relay boundary but stutters at the client. -/
example : clientMoves (slot false, .cReply true) = [] := rfl
example : hideMiddle (.cReply true) = [.rightReply true] := rfl
example : observeWire (forwarded ++ [(slot false,.cAsk),(slot false,.cReply true)]) =
    observeWire (forwarded ++ [(slot false,.cAsk)]) :=
  external_stutter (wire := forwarded ++ [(slot false,.cAsk)]) rfl

/-- Delivery is conditional on supplying both remaining propagation events. -/
theorem supplied_delivery :
    observeWire (buffered ++ [(slot false,.bReply true),(slot false,.aReply true)]) =
      some ⟨none, .answered true, .idle, [.ask false,.reply false true]⟩ := rfl

/-- The complete pair of idle stages does not distinguish initial idle from
idle after delivery. History, retained by Detailed, does distinguish them. -/
theorem stages_do_not_determine_client : ¬ ∃ recover : Option (Stage × Stage) → Output,
    ∀ wire, InteractionPlay ff ff wire → recover ((inspect ff ff wire).map stagePair) = observeWire wire := by
  rintro ⟨recover,h⟩
  have initialLegal : InteractionPlay ff ff [] := fun _ => ⟨.idle,.nil⟩
  have a := h [] initialLegal
  have b := h delivered ((accepted_iff ff ff delivered).mp delivered_accepted)
  have bad : (some (⟨none,.idle,.idle,[]⟩ : Observation) : Output) =
      some ⟨none,.answered true,.idle,[.ask false,.reply false true]⟩ := a.symm.trans b
  cases bad

def reused : Wire := delivered ++
  [(slot false,.aAsk),(slot false,.bAsk),(slot false,.cAsk),
   (slot false,.cReply false),(slot false,.bReply false),(slot false,.aReply false)]

example : ∃ d, inspect ff ff reused = some d := ⟨_,rfl⟩
example : observeWire reused = some ⟨none,.answered false,.idle,
    [.ask false,.reply false true,.ask false,.reply false false]⟩ := rfl

example : inspect ff ff [(slot false,.aReply true)] = none := rfl
example : inspect ff ff [(slot false,.aAsk),(slot false,.aAsk)] = none := rfl
example : inspect ff ff (buffered ++ [(slot false,.bReply false)]) = none := rfl

/-- The interpreted B reply changes, while endpoints and external meaning agree. -/
def negationPrefix : Wire :=
  [(slot false,.aAsk),(slot false,.bAsk),(slot false,.cAsk),
   (slot false,.cReply true),(slot false,.bReply false)]

theorem negation_accepted : ∃ d, inspect negate negate negationPrefix = some d := ⟨_,rfl⟩

example : BehavioralTransport.mapWire keep flip keep negationPrefix ≠ negationPrefix := by decide

example (h : inspect negate negate wire = some d) :
    inspect ff ff (BehavioralTransport.mapWire keep flip keep wire) = some (d.interpret keep flip keep) ∧
    (d.interpret keep flip keep).stages = d.stages ∧
    (d.interpret keep flip keep).external = d.external := simplify_observer h

example (h : inspect negate negate wire = some d) :
    inspect negate negate (BehavioralTransport.mapWire keep flip keep
      (BehavioralTransport.mapWire keep flip keep wire)) = some d := twice_inspect h

example (q : List (Bool × Bool)) : runClient negate negate (network negate negate q) = native q :=
  runClient_caller q

example : runClient ff ff buffered = some ⟨none,.pending,.idle,[.ask false]⟩ := rfl
example : runClient ff ff [(slot false,.aReply true)] = none := rfl

/-- Ordered client history is retained even where final answers and statuses agree. -/
theorem answer_order_distinguished :
    (observeWire (network negate negate [(true,true),(false,false)])).map Observation.result =
      (observeWire (network negate negate [(false,false),(true,true)])).map Observation.result ∧
    observeWire (network negate negate [(true,true),(false,false)]) ≠
      observeWire (network negate negate [(false,false),(true,true)]) := by
  simp only [implementation_observation]
  exact ⟨equal_results, different_interactions⟩

end Examples.InteractionPrefixes
