import Applications.FRP.Temporal
import SquareKit.Temporal.BatchRelations

/-! Payload mapping consumes a supplied arrival certificate; it does not transform
an arbitrary trace into a causal online processor. -/
namespace FRPSpec.Frontier.Demand.Temporal
open _root_.Temporal FRPSpec.Frontier.Trace
variable {T α β : Type} [LinearOrder T]
variable (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T) (t : T)

/-- Honesty followed by a payload map, with the response square inside `correct`. -/
def mapPayload (truth : Source → T → List α) (honest : (traceRep ms).Rel s truth)
    (g : α → β) {n : Nat} (w : Arrival s ms a t n) :
    Until (Pending s ms a t)
      (fun _ => {out : List β // out = (truth .left t ++ truth .right t).map g}) n :=
  (correct s ms a t truth honest w).map (fun _ => id)
    (fun _ b => ⟨b.1.map g, congrArg (List.map g) b.2.down.2⟩)

@[simp] theorem mapPayload_horizon (truth : Source → T → List α)
    (honest : (traceRep ms).Rel s truth) (g : α → β) {n : Nat} (w : Arrival s ms a t n) :
    (mapPayload s ms a t truth honest g w).horizon = w.horizon := by
  simp [mapPayload, correct]

/-- Observe the mapped certificate's terminal list, including order and duplicates. -/
theorem mapPayload_value (truth : Source → T → List α)
    (honest : (traceRep ms).Rel s truth) (g : α → β) {n : Nat} (w : Arrival s ms a t n) :
    (Until.terminal (mapPayload s ms a t truth honest g w)).val =
      (truth .left t ++ truth .right t).map g :=
  (Until.terminal (mapPayload s ms a t truth honest g w)).property

/-- Erase only the equality annotation to compare with an ordinary batch map. -/
theorem mapPayload_output (truth : Source → T → List α)
    (honest : (traceRep ms).Rel s truth) (g : α → β) {n : Nat} (w : Arrival s ms a t n) :
    (Until.terminal (mapPayload s ms a t truth honest g w)).val =
      (output s ms a t w).map g := by
  induction w with
  | now b => rfl
  | wait _ _ ih => exact ih

end FRPSpec.Frontier.Demand.Temporal
