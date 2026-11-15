import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory
universe u
/-- The whole normalized value represents this selected arrow. -/
def IdentityValueAction {V X : Type u} (v : V) (k : X) : Prop :=
 HEq v (LocallyDiscrete.mk (Discrete.mk k))
end SquareKit.Internal.PathTransport.HigherInterpretation
