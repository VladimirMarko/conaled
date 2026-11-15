import SquareKit.SemanticBoundary
import SquareKit.GroupoidTransportRoutes

/-! A bounded semantic boundary for selected arrows and their dependent action.
Only redundant representation flags are identified. The arrow remains data;
this is not a quotient identifying parallel paths or higher cells. -/
namespace SquareKit.GroupoidTransport.SelectedBoundary
open CategoryTheory Squares
universe u v

/-- Direct and flagged realizations retain exactly the chosen semantic data. -/
def direct (S : Type u) : Rep.{u} := ⟨S, S, id⟩
def flagged (S : Type u) : Rep.{u} := ⟨S × Bool, S, Prod.fst⟩
def removeFlag (S : Type u) : Square (flagged S) (direct S) := ⟨Prod.fst, id, fun _ => rfl⟩
def addFlag (S : Type u) : Square (direct S) (flagged S) := ⟨fun s => (s, true), id, fun _ => rfl⟩

/-- Lift a semantic operation while changing irrelevant representation data. -/
def operation {S T : Type u} (f : S → T) : Square (flagged S) (flagged T) :=
  ⟨fun p => (f p.1, !p.2), f, fun _ => rfl⟩

theorem replacement {S : Type u} (x : SemanticBoundary.Handle (flagged S)) :
    SemanticBoundary.lift (addFlag S) (SemanticBoundary.lift (removeFlag S) x) = x := by
  induction x using Quotient.inductionOn with
  | h x => exact Quotient.sound rfl

variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  (B : C ⥤ Type u) {A : D ⥤ Type u} {K : E ⥤ Type u}

/-- An input includes both its chosen path and its dependent source value. -/
abbrev Input (x y : C) := (x ⟶ y) × B.obj x
abbrev Output (x y : C) := (x ⟶ y) × B.obj y

/-- The path is retained even when its action on this family is ineffective. -/
def transport (x y : C) : Square (flagged (Input B x y)) (flagged (Output B x y)) :=
  operation (fun (p, b) => (p, B.map p b))

def routeInput (r : Route B A) (x y : C) :
    Square (flagged (Input B x y)) (flagged (Input A (r.base.obj x) (r.base.obj y))) :=
  operation (fun (p, b) => (r.base.map p, r.fiber.app x b))

def routeOutput (r : Route B A) (x y : C) :
    Square (flagged (Output B x y)) (flagged (Output A (r.base.obj x) (r.base.obj y))) :=
  operation (fun (p, b) => (r.base.map p, r.fiber.app y b))

/-- Local naturality derives the commuting comparison for the entire selected input. -/
theorem route_transport (r : Route B A) (x y : C)
    (h : SemanticBoundary.Handle (flagged (Input B x y))) :
    SemanticBoundary.lift (routeOutput B r x y) (SemanticBoundary.lift (transport B x y) h) =
      SemanticBoundary.lift (transport A (r.base.obj x) (r.base.obj y))
        (SemanticBoundary.lift (routeInput B r x y) h) := by
  induction h using Quotient.inductionOn with
  | h h =>
    apply Quotient.sound
    exact Prod.ext rfl (r.transport h.1.1 h.1.2)

/-- Every certified composite transports by the original route composition law. -/
theorem route_compose (r : Route B A) (s : Route A K) (x y : C)
    (h : SemanticBoundary.Handle (flagged (Input B x y))) :
    SemanticBoundary.lift (routeInput B (r.comp s) x y) h =
      SemanticBoundary.lift (routeInput A s (r.base.obj x) (r.base.obj y))
        (SemanticBoundary.lift (routeInput B r x y) h) := by
  induction h using Quotient.inductionOn with
  | h h => exact Quotient.sound rfl

/-- Source substitution changes both the arrow and the fiber before routing. -/
theorem substituted_transport {H : Type u} [Category.{u} H] (r : Route B A)
    (σ : H ⥤ C) {x y : H} (p : x ⟶ y) (b : B.obj (σ.obj x)) :
    (r.reindex σ).fiber.app y ((σ ⋙ B).map p b) =
      A.map (r.base.map (σ.map p)) (r.fiber.app (σ.obj x) b) :=
  r.substitution_transport σ p b

end SquareKit.GroupoidTransport.SelectedBoundary
