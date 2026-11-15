import SquareKit.Internal.PathTransport.TwoFamilyModelData
import SquareKit.Internal.PathTransport.TwoFamilySectionNormalization
/-! A common value-comparison predicate for source actions and their native interpretations. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory TwoFamily
universe u
def RightEndpointValueFormula {Γ : Type u} [Bicategory.{u,u} Γ] [Strict Γ] {Θ : Context.{u}}
 (σ : StrictPseudofunctor Θ Γ) (G : Family Θ) (p : TwoFamily.Section G.data)
 (V : Γ → Type u) (v : ∀ z, V z) : Prop :=
 ∀ γ, HEq (p.normalObj G.data γ).fiber (LocallyDiscrete.mk (v (σ.obj γ)))
end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
