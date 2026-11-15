import SquareKit.Internal.PathTransport.TwoFamilyBranchObjects
import SquareKit.Internal.PathTransport.TwoFamilyReindexedObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory
universe u
variable {Γ Δ Θ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
def ReindexedBranchFormula (c : SourceContraction i) (E : Family Γ) (F : Family Δ)
    (e : F = E.reindex i) (σ : StrictPseudofunctor Θ Γ) (G : Family Θ)
    (j : TwoFamily.Section F.data → TwoFamily.Section G.data) : Prop :=
  ∀ d, c.ReindexedValueFormula E (TwoFamily.Section.cast (congrArg Family.data e) d) σ G (j d)
theorem BranchFormula.reindex_cast (c : SourceContraction i) (E : Family Γ) (F : Family Δ)
    (e : F = E.reindex i) (j : TwoFamily.Section F.data → TwoFamily.Section E.data)
    (h : c.BranchFormula E F e j) (σ : StrictPseudofunctor Θ Γ)
    (G : Family Θ) (e' : E.reindex σ = G) :
    c.ReindexedBranchFormula E F e σ G
      (fun d => TwoFamily.Section.cast (congrArg Family.data e') ((j d).reindex E.data σ)) :=
  fun d => ValueFormula.reindex_cast c E _ (j d) (h d) σ G e'
end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
