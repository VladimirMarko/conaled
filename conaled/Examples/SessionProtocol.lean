import SquareKit.Session.Protocol

namespace Examples.SessionProtocol
open Session

/-- Two successive binary selections, with early termination on another branch. -/
def request : Protocol := .choose (.choose .finish .finish) .finish
def chooseRequest : Selection request := .left (.right .finish)
def acknowledge : Protocol := .choose .finish .finish
def chooseAck : Selection acknowledge := .left .finish

/-- The environment still owns the peer of endpoint 2. -/
def done : Proof [(2,.one)] := .close 2

def ackReceiver : Receiver [(2,.one)] acknowledge :=
  .choose (.finish done) (.finish done)
def ack : Proof [(2,.one)] := connect 1 (by decide) chooseAck ackReceiver

/-- Only the selected right subbranch continues into the second typed session. -/
def requestReceiver : Receiver [(2,.one)] request :=
  .choose (.choose (.finish done) (.finish ack)) (.finish done)
def network : Proof [(2,.one)] := connect 0 (by decide) chooseRequest requestReceiver

def observed : List Event := [.label 0 false, .label 0 true, .closed 0, .label 1 false, .closed 1]

example : Typed network.erase [(2,.one)] := network.typed
example : request.formula.dual.dual = request.formula := Formula.dual_dual _
example : Accepts 0 request [.label 0 false,.label 0 true,.closed 0] := chooseRequest.accepts 0
example : Accepts 1 acknowledge [.label 1 false,.closed 1] := chooseAck.accepts 1

/-- This is reduction of the composed process, not equality of a function result. -/
theorem communicates : Steps network.erase observed (.close 2) :=
  completes_then 0 (by decide) chooseRequest requestReceiver
    (completes 1 (by decide) chooseAck ackReceiver)

example : ∃ e q, Step network.erase e q := progress 0 (by decide) chooseRequest requestReceiver
example : Steps ack.erase [.label 1 false,.closed 1] (.close 2) :=
  completes 1 (by decide) chooseAck ackReceiver

/-- Ordinary process clients can state raw communicating endpoints directly. -/
def ordinary : Process := .cut 3 (.select 3 false (.close 3))
  (.offer 3 (.wait 3 (.close 4)) (.wait 3 (.close 4)))
example : Typed ordinary [(4,.one)] := by
  exact Typed.cut (Γ := []) (a := .plus .one .one) (by decide)
    (Typed.left Typed.close) (.offer (.wait (by decide) .close) (.wait (by decide) .close))
example : Steps ordinary [.label 3 false,.closed 3] (.close 4) :=
  .cons .left (.cons .close .nil)

/-- The optional proof interface exposes the actual principal-cut simulation. -/
def leafReceiver : Proof [(3,.bottom),(4,.one)] := .wait 3 (by decide) (.close 4)
example : Step
    (Proof.cut 3 (.plus .one .one) (Γ := []) (by decide)
      (.left (.close 3)) (.offer leafReceiver leafReceiver)).erase
    (.label 3 false)
    (Proof.cut 3 .one (Γ := []) (by decide) (.close 3) leafReceiver).erase :=
  (CutStep.left (b := .one) (by decide) (.close 3) leafReceiver leafReceiver).simulates

/-- Repeated endpoint names cannot be typed, even with exchange. -/
theorem no_duplicate (x : Nat) (a b : Formula) (p : Process) :
    ¬ Typed p [(x,a),(x,b)] := by
  intro h
  simpa [Valid] using h.valid

/-- Two components cannot each spend the same residual endpoint at a cut. -/
example : ¬ Valid ([(2,.one)] ++ [(2,.one)]) := by decide

/-- The early-termination branch cannot send another selection before close. -/
example : ¬ Accepts 0 request [.label 0 true,.label 0 false,.closed 0] := by
  intro h
  cases h with
  | right h => cases h

/-- A fixed finite protocol cannot provide arbitrarily many communications. -/
theorem no_unbounded_server (a : Protocol) (x : Nat) :
    ¬ (∀ n, ∃ p : Selection a, n < (p.events x).length) := by
  intro h
  obtain ⟨p,hp⟩ := h a.bound
  exact Nat.not_lt_of_ge (p.length_le x) hp

/-- Every execution to the selected phase boundary refines the type's language. -/
example : Interaction.Refines Eq {es | Accepts 0 request es}
    {es | ∃ q, Steps network.erase es q ∧ es.length = 3} :=
  trace_refines 0 (by decide) chooseRequest requestReceiver

/-- Existing relational property transport carries a protocol safety property
onto actual process observations, without another process induction. -/
example (es : List Event)
    (run : ∃ q, Steps network.erase es q ∧ es.length = 3) :
    ∀ e ∈ es, e.channel = 0 := by
  exact (trace_refines 0 (by decide) chooseRequest requestReceiver).property
    (P := fun es => ∀ e ∈ es, e.channel = 0)
    (Q := fun es => ∀ e ∈ es, e.channel = 0)
    (fun _ h => h.channels) (fun _ _ eq h => eq ▸ h) es run

/-- The chosen residual is externally blocked, not claimed to terminate closed. -/
example : ¬ ∃ e q, Step (.close 2) e q := by rintro ⟨e,q,h⟩; cases h

end Examples.SessionProtocol
