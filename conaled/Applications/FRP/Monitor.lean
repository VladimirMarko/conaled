import SquareKit.Temporal.Monitor
import Applications.FRP.TemporalCausality

/-! Decidable monitor atoms inspect reference frames, never unobserved source truth. -/
namespace FRPSpec.Frontier.Demand.Monitor
open FRPSpec.Frontier.Trace
open _root_.Temporal.Monitor
variable {T α : Type} [LinearOrder T]

abbrev Observation (T α : Type) := Temporal.Frame (T := T) (α := α)

def pending (t : T) : Formula (Observation T α) := .atom (fun f => decide (f.stored = .pending t))
def ready : Formula (Observation T α) := .atom (fun f => f.observed.isSome)
def emitted : Formula (Observation T α) := .atom (fun f => f.emitted.isSome)
def answer [DecidableEq α] (t : T) (xs : List α) : Formula (Observation T α) :=
  .atom (fun f => decide (f.emitted = some (t,xs)))

def frames (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T) (t : T) : Nat → Observation T α :=
  Temporal.frame s ms a t

/-- Additional source processing preserves certified knowledge of a fixed timestamp.
It need not preserve next, bounded-until, or the one-step emission atom. -/
theorem observed_persists (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T)
    (t : T) {n m : Nat} {out : List α} (le : n ≤ m)
    (h : (frames s ms a t n).observed = some out) :
    (frames s ms a t m).observed = some out :=
  run_persists s ms (sourceSchedule a) le h

end FRPSpec.Frontier.Demand.Monitor
