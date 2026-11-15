import SquareKit.Internal.PathTransport.CechMatching
import Mathlib.CategoryTheory.Equivalence

/-! Contractible local and source groupoids give empty-context effectivity
without reducing the implementation of the restriction functor. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
universe u v w
variable {D : Diagram.{u,v}}

/-- Thin local arrows make matching arrows thin, without forgetting their data. -/
theorem matching_hom_subsingleton
    (thin : ∀ x y : D.localCategory, Subsingleton (x ⟶ y)) (d e : Datum D) :
    Subsingleton (d ⟶ e) := by
  constructor
  intro f g
  exact Datum.Hom.ext _ _ ((thin _ _).elim _ _)

/-- In a contractible local groupoid with thin overlaps, the actual square is automatic. -/
def matchingArrowOfThin
    (arrow : ∀ x y : D.localCategory, x ⟶ y)
    (overlapThin : ∀ x y : D.doubleCategory, Subsingleton (x ⟶ y))
    (d e : Datum D) : d ⟶ e where
  localArrow := arrow d.localObject e.localObject
  commutes := (overlapThin _ _).elim _ _

/-- No matching equivalence or inspection of R is assumed. This applies to
empty-context restriction after its endpoint categories are identified. -/
theorem restriction_equivalence_of_contractible
    {C : Type w} [Groupoid.{u} C] (R : C ⥤ Datum D)
    (point : C) (sourceArrow : ∀ x y : C, x ⟶ y)
    (sourceThin : ∀ x y : C, Subsingleton (x ⟶ y))
    (localArrow : ∀ x y : D.localCategory, x ⟶ y)
    (localThin : ∀ x y : D.localCategory, Subsingleton (x ⟶ y))
    (overlapThin : ∀ x y : D.doubleCategory, Subsingleton (x ⟶ y)) :
    R.IsEquivalence := by
  let : R.Full := ⟨fun {x y} f =>
    ⟨sourceArrow x y, (matching_hom_subsingleton localThin _ _).elim _ _⟩⟩
  let : R.Faithful := ⟨fun {_ _} {_ _} _ => (sourceThin _ _).elim _ _⟩
  let : R.EssSurj := ⟨fun d =>
    ⟨point, ⟨asIso (matchingArrowOfThin localArrow overlapThin (R.obj point) d)⟩⟩⟩
  exact {}

end SquareKit.Internal.PathTransport.CechMatching
