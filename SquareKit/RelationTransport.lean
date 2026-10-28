import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice.Image

/-! Predicate transport through arbitrary relations. `image` describes possible
outputs; `requirement` describes inputs whose every related output satisfies a
predicate. The latter is partial correctness, with no existence or progress
claim. Function specializations reuse Mathlib's image, preimage and kernImage. -/
namespace SquareKit.RelationTransport
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

def image (r : X → Y → Prop) (P : Set X) : Set Y :=
  {y | ∃ x ∈ P, r x y}

def requirement (r : X → Y → Prop) (Q : Set Y) : Set X :=
  {x | ∀ y, r x y → y ∈ Q}

theorem image_requirement (r : X → Y → Prop) :
    GaloisConnection (image r) (requirement r) := by
  intro P Q
  constructor
  · intro h x hx y hxy
    exact h ⟨x, hx, hxy⟩
  · rintro h y ⟨x, hx, hxy⟩
    exact h hx y hxy

theorem image_comp (r : X → Y → Prop) (q : Y → Z → Prop) (P : Set X) :
    image (Relation.Comp r q) P = image q (image r P) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hx, hxy⟩, hyz⟩
  · rintro ⟨y, ⟨x, hx, hxy⟩, hyz⟩
    exact ⟨x, hx, y, hxy, hyz⟩

theorem requirement_comp (r : X → Y → Prop) (q : Y → Z → Prop) (Q : Set Z) :
    requirement (Relation.Comp r q) Q = requirement r (requirement q Q) := by
  ext x
  constructor
  · intro h y hxy z hyz
    exact h z ⟨y, hxy, hyz⟩
  · rintro h z ⟨y, hxy, hyz⟩
    exact h y hxy z hyz

theorem image_graph (f : X → Y) (P : Set X) :
    image (fun x y => f x = y) P = f '' P := rfl

theorem requirement_graph (f : X → Y) (Q : Set Y) :
    requirement (fun x y => f x = y) Q = f ⁻¹' Q := by
  ext x
  exact ⟨fun h => h (f x) rfl, fun h y heq => heq ▸ h⟩

/-- Reversing the graph gives universal quantification over an observation's
fiber, rather than predicate substitution along the function. -/
theorem requirement_converse_graph (f : X → Y) (P : Set X) :
    requirement (fun y x => f x = y) P = Set.kernImage f P := rfl

/-- Restrict possible worlds before universally observing their property.
The left relation goes from observations in `Y` to admissible worlds in `X`.
Neither side asserts that an admissible world with this observation exists. -/
theorem requirement_restricted_converse (f : X → Y) (A P : Set X) :
    requirement (fun y x => x ∈ A ∧ f x = y) P =
      Set.kernImage (fun x : A => f x.val) {x | x.val ∈ P} := by
  ext y
  constructor
  · intro h x heq
    exact h x.val ⟨x.property, heq⟩
  · intro h x hx
    exact h (x := ⟨x, hx.1⟩) hx.2

end SquareKit.RelationTransport
