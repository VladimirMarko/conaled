import Applications.Interaction.StrategyQueries

/-! Checked selected observations and policy changes for finite interaction. -/
namespace Examples.FiniteStrategies
open Interaction.FiniteQueries Interaction.FiniteStrategies

example (b : Bool) : observe (network (constant b) id id 1 false []) =
    (some b, [.ask, .reply b]) := by
  rw [forwarding_native]
  exact constant_once b

example (b : Bool) : observe (network (constant b) id id 2 false []) =
    (some b, [.ask, .reply b, .ask, .reply b]) := by
  rw [forwarding_native]
  exact constant_twice b

example : observe (network changing id id 2 false []) =
    (some true, [.ask, .reply false, .ask, .reply true]) := by
  rw [forwarding_native]
  rfl

example : observe (network silent id id 2 false []) = (none, [.ask]) := by
  rw [forwarding_native]
  exact silent_pending

/-- Failure after a completed interaction retains that round and the pending ask. -/
def thenSilent : Environment := fun h => if h.isEmpty then some false else none
example : observe (network thenSilent id id 2 false []) =
    (none, [.ask, .reply false, .ask]) := by
  rw [forwarding_native]
  rfl

example : CompositePlay id id
    ((network changing id id 2 false []).2.flatMap hideMiddle) :=
  (selected_contract changing 2 false []).2.2.1

/-- Even two complete forwarding rounds have actual matched middle-channel moves. -/
example : (network changing id id 2 false []).2 =
    [.aAsk, .bAsk, .cAsk, .cReply false, .bReply false, .aReply false,
     .aAsk, .bAsk, .cAsk, .cReply true, .bReply true, .aReply true] := rfl

/-- Changed policy: flipping one reply changes selection, but not service evidence. -/
example : observe (network (constant false) Bool.not id 1 true []) =
    (some true, [.ask, .reply false]) := by
  simpa [native, constant] using network_native (constant false) Bool.not id 1 false []

/-- Two policy flips cancel at the whole strategy boundary. -/
example (xs : List RelayMove) : CompositePlay Bool.not Bool.not xs ↔ RelayPlay id xs := by
  rw [compose_exact]
  have h : Bool.not ∘ Bool.not = id := by funext b; cases b <;> rfl
  rw [h]

def duplicate (b : Bool) : List RelayMove :=
  [.leftAsk, .rightAsk, .rightReply b, .rightAsk, .rightReply b, .leftReply b]
def cached (b : Bool) : List RelayMove :=
  [.leftAsk, .rightAsk, .rightReply b, .leftReply b, .leftAsk, .leftReply b]

theorem duplicate_not_play : ¬ RelayPlay id (duplicate false) :=
  rejected_not_play (by rfl)
theorem cached_not_play : ¬ RelayPlay id (cached false) :=
  rejected_not_play (by rfl)

/-- Faulty forwarding still returns the constant reply but violates exact history. -/
def faultyObservation (b : Bool) (xs : List RelayMove) : Outcome :=
  (some b, xs.flatMap relayServiceMoves)

theorem duplicate_wrong_history :
    (faultyObservation false (duplicate false)).1 = (once (constant false)).1 ∧
    (faultyObservation false (duplicate false)).2 ≠ (once (constant false)).2 := by decide

theorem cache_wrong_history :
    (faultyObservation false (cached false)).1 = (twice (constant false)).1 ∧
    (faultyObservation false (cached false)).2 ≠ (twice (constant false)).2 := by decide

/-- A deliberately restricted observational equality on finite clients. -/
def constantReturns : Setoid Nat where
  r n m := ∀ b, (native (constant b) n false []).1 = (native (constant b) m false []).1
  iseqv := ⟨fun _ _ => rfl, fun h b => (h b).symm, fun h k b => (h b).trans (k b)⟩

theorem constant_returns_equal : constantReturns.r 1 2 := fun _ => rfl

def constantObservation (b : Bool) : Quotient constantReturns → Option Bool :=
  Quotient.lift (fun n => (native (constant b) n false []).1) (fun _ _ h => h b)

/-- An adaptive responder is not an admissible observation of this quotient. -/
theorem adaptive_does_not_descend : ¬ ∃ obs : Quotient constantReturns → Option Bool,
    ∀ n, obs (Quotient.mk constantReturns n) = (native changing n false []).1 := by
  rintro ⟨obs, h⟩
  have eqv : Quotient.mk constantReturns 1 = Quotient.mk constantReturns 2 :=
    Quotient.sound constant_returns_equal
  have bad := (h 1).symm.trans ((congrArg obs eqv).trans (h 2))
  contradiction

theorem history_does_not_descend : ¬ ∃ obs : Quotient constantReturns → List Move,
    ∀ n, obs (Quotient.mk constantReturns n) = (native (constant false) n false []).2 := by
  rintro ⟨obs, h⟩
  have eqv : Quotient.mk constantReturns 1 = Quotient.mk constantReturns 2 :=
    Quotient.sound constant_returns_equal
  have bad := (h 1).symm.trans ((congrArg obs eqv).trans (h 2))
  contradiction
end Examples.FiniteStrategies
