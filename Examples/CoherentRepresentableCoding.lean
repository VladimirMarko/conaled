import SquareKit.Internal.CoherentRepresentableCoding
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver

/-! Sheaves over contexts provide category-valued data with coherent pullback.
The code construction retains functors and natural isomorphisms. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CoherentRepresentableCoding
open CategoryTheory SquareKit.RepresentableClassification
universe u v w a b
variable {C : Type v} [Category.{w} C]
variable (J : GrothendieckTopology (Context.{u} C)) (A : Type a) [Category.{b} A]

def codes := coherentCodes (J.pseudofunctorOver A)

example (I : C) : (codes J A).obj ⟨Opposite.op I⟩ =
    Cat.of (Sheaf (J.over (representable.{u} I)) A) := rfl

/-- Restriction is the actual sheaf pullback functor, including its action on morphisms. -/
example {I K : C} (f : K ⟶ I) :
    ((codes J A).map f.op.toLoc).toFunctor = J.overMapPullback A (representableMap f) := rfl

example {Γ : Context.{u} C} {x y : Γ.Elements} (f : x ⟶ y) :
    (J.pseudofunctorOver A).map (represented y).op.toLoc ≅
      (J.pseudofunctorOver A).map (represented x).op.toLoc ≫
        (J.pseudofunctorOver A).map (representableMap f.hom.unop).op.toLoc :=
  coherentCodeRestriction (J.pseudofunctorOver A) f

end Examples.CoherentRepresentableCoding
