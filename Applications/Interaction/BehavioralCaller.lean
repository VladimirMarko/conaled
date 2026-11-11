import Applications.Interaction.BehavioralTransport
import SquareKit.InteractionContracts
import SquareKit.CommaVertical

/-! Three behavioral levels at one fixed environment schedule. -/
namespace Interaction.BehavioralCaller
open OverlappingQueries FiniteStrategies OverlappingStrategies OverlappingCaller
open BehavioralTransport

abbrev Schedule := List (Bool × Bool)
abbrev Relay := List (Event arena RelayMove)
abbrev Wire := List (Event arena WireMove)
abbrev Output := Option Observation

/-- Actual client events are executed; the service boundary is not substituted. -/
def observeRelay (r : Relay) : Output :=
  let history := r.flatMap clientEvent
  (OverlappingQueries.execute initial history).map (fun s => observe s history)

def observeWire (w : Wire) : Output := observeRelay (hide w)

theorem double_negation : negate.comp negate = forwarding := by
  change (⟨_⟩ : Strategy arena) = ⟨_⟩
  congr 1
  funext i b
  cases b <;> rfl

theorem forwarding_observation (q : Schedule) :
    observeRelay (caller forwarding q) = native q := by
  have ht : transform forwarding = id := by funext m; cases m <;> rfl
  simp only [observeRelay, caller, client_recovery, ht, List.map_id, native]

theorem implementation_hides (q : Schedule) :
    hide (network negate negate q) = caller forwarding q := by
  rw [network_hides, double_negation]

theorem implementation_observation (q : Schedule) :
    observeWire (network negate negate q) = native q := by
  rw [observeWire, implementation_hides, forwarding_observation]

/-- Evaluator-output sets include rejection. Legality is proved separately for
accepted schedules, so an invalid raw trace is not called a legal strategy play. -/
def nativeOutputs (q : Schedule) : Set Output := {o | o = native q}
def relayOutputs (q : Schedule) : Set Relay := {r | r = caller forwarding q}
def wireOutputs (q : Schedule) : Set Wire := {w | w = network negate negate q}

def firstComparison (o : Output) (r : Relay) : Prop := observeRelay r = o
def secondComparison (r : Relay) (w : Wire) : Prop := hide w = r

theorem first_correct (q : Schedule) : Refines firstComparison (nativeOutputs q) (relayOutputs q) := by
  rintro r rfl
  exact ⟨native q, rfl, forwarding_observation q⟩

theorem second_correct (q : Schedule) : Refines secondComparison (relayOutputs q) (wireOutputs q) := by
  rintro w rfl
  exact ⟨caller forwarding q, rfl, implementation_hides q⟩

/-- Coverage composes through the very same relay value, at unchanged q. -/
theorem vertical_coverage (q : Schedule) :
    Refines (Relation.Comp firstComparison secondComparison) (nativeOutputs q) (wireOutputs q) :=
  (first_correct q).trans (second_correct q)

/-- Coverage alone does not establish this observation equation. -/
theorem vertical_observation (h : Relation.Comp firstComparison secondComparison o w) :
    observeWire w = o := by
  obtain ⟨r, first, second⟩ := h
  change observeRelay (hide w) = o
  rw [show hide w = r from second]
  exact first

theorem composed_correct (q : Schedule) :
    ∀ w ∈ wireOutputs q, observeWire w = native q := by
  intro w hw
  obtain ⟨o, ho, comparison⟩ := vertical_coverage q hw
  exact (vertical_observation comparison).trans ho

/-- These exact evaluator squares do fit Comma.vertical. Their middle horizontal
arrow is the same forwarding caller; they do not encode directed inclusion. -/
def wireSquare : Squares.Square (⟨Schedule, Schedule, id⟩ : Squares.Rep)
    ⟨Wire, Relay, hide⟩ where
  impl := network negate negate
  spec := caller forwarding
  commutes := implementation_hides

def relaySquare : Squares.Square (⟨Schedule, Schedule, id⟩ : Squares.Rep)
    ⟨Relay, Output, observeRelay⟩ where
  impl := caller forwarding
  spec := native
  commutes := forwarding_observation

def pastedSquare := Squares.vertical id observeRelay wireSquare relaySquare (fun _ => rfl)

theorem comma_pasting : SquareKit.Comma.Exact.ofSquare pastedSquare =
    SquareKit.Comma.vertical
      (SquareKit.equalityCongr SquareKit.FunctionCategory.ops)
      SquareKit.FunctionCategory.laws
      (SquareKit.Comma.Exact.ofSquare wireSquare)
      (SquareKit.Comma.Exact.ofSquare relaySquare) (funext (fun _ => rfl)) :=
  SquareKit.Comma.Exact.ofSquare_vertical _ _ _ _ _

theorem pasted_recovers (q : Schedule) : observeWire (network negate negate q) = native q :=
  pastedSquare.commutes q

/-- Explicit successful-environment coverage prevents safety from hiding empty
behavior. No scheduler fairness or future response assumption is needed. -/
theorem accepted_coverage (h : native q = some out) :
    ∃ r w, forwarding.Play r ∧ InteractionPlay negate negate w ∧
      firstComparison (some out) r ∧ secondComparison r w ∧
      observeWire w = some out := by
  refine ⟨caller forwarding q, network negate negate q,
    relay_legal _ (native_legal h), network_legal _ _ h, ?_, implementation_hides q, ?_⟩
  · exact (forwarding_observation q).trans h
  · exact (implementation_observation q).trans h

/-- All original forwarding pending prefixes remain available, even between
atomic caller blocks. This claim concerns the language, not native evaluation. -/
theorem original_prefixes (xs : Relay) :
    OverlappingStrategies.CompositePlay negate negate xs ↔ forwarding.Play xs := by
  rw [OverlappingStrategies.compose_exact, double_negation]

def CoversAccepted (behavior : Schedule → Set Wire) : Prop :=
  ∀ q out, native q = some out → ∃ w ∈ behavior q, observeWire w = some out

theorem implementation_covers : CoversAccepted wireOutputs := by
  intro q out h
  exact ⟨network negate negate q, rfl, (implementation_observation q).trans h⟩

/-- Safety coverage in the implementation-to-specification direction alone
admits an empty implementation. The separate coverage requirement rules it out. -/
theorem empty_safe (q : Schedule) :
    Refines (Relation.Comp firstComparison secondComparison) (nativeOutputs q) (∅ : Set Wire) := by
  intro w hw
  exact False.elim hw

theorem empty_fails_coverage : ¬ CoversAccepted (fun _ => ∅) := by
  intro h
  obtain ⟨w, hw, _⟩ := h [] _ both_pending
  exact hw

/-- Producing no further replies is safe as a prefix, but fails after an actual
supplied response. This says nothing about waiting when the environment is silent. -/
def silent (_ : Schedule) : Set Wire := {w | w = network negate negate []}

theorem silent_fails_coverage : ¬ CoversAccepted silent := by
  intro h
  obtain ⟨w, hw, ho⟩ := h [(true,true)] _ right_only
  change w = network negate negate [] at hw
  rw [hw, implementation_observation] at ho
  cases ho

theorem pending_recovery : observeWire (network negate negate []) =
    some ⟨none, .pending, .pending, requests⟩ := by
  rw [implementation_observation]; exact both_pending

theorem response_recovery : observeWire (network negate negate [(true,true)]) =
    some ⟨none, .pending, .answered true, requests ++ [.reply true true]⟩ := by
  rw [implementation_observation]; exact right_only

theorem rejection_recovery : observeWire (network negate negate [(true,true),(true,false)]) = none := by
  rw [implementation_observation]; exact duplicate_reply_rejected

/-- A legal policy in the same arena gives the wrong client response. -/
theorem legal_but_wrong :
    InteractionPlay negate forwarding (network negate forwarding [(true,true),(false,false)]) ∧
    observeWire (network negate forwarding [(true,true),(false,false)]) ≠
      native [(true,true),(false,false)] := by
  constructor
  · exact network_legal _ _ right_first
  · decide

theorem order_not_recoverable : ¬ ∃ recover : Option Bool × Status × Status → Output,
    ∀ q out, native q = some out → recover (out.result, out.left, out.right) = some out := by
  rintro ⟨recover, h⟩
  have a := h _ _ right_first
  have b := h _ _ left_first
  have bad := a.symm.trans b
  cases bad

end Interaction.BehavioralCaller
