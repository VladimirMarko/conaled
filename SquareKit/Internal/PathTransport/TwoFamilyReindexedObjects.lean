import SquareKit.Internal.PathTransport.TwoFamilyContractionObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory
universe u
variable {Γ Δ Θ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
def ReindexedValueFormula (c : SourceContraction i) (E : Family Γ)
    (d : TwoFamily.Section (TwoFamily.reindex i E.data)) (σ : StrictPseudofunctor Θ Γ)
    (F : Family Θ) (s : TwoFamily.Section F.data) : Prop :=
  ∀ z : Θ,
    HEq (s.normalObj F.data z).fiber
      ((E.data.map (c.homotopy.app (σ.obj z))).obj
        ((d.normalObj (TwoFamily.reindex i E.data) (c.retraction.obj (σ.obj z))).fiber))

theorem ValueFormula.reindex_cast (c : SourceContraction i) (E : Family Γ)
    (d : TwoFamily.Section (TwoFamily.reindex i E.data)) (s : TwoFamily.Section E.data)
    (h : c.ValueFormula E d s) (σ : StrictPseudofunctor Θ Γ)
    (F : Family Θ) (e : E.reindex σ = F) :
    c.ReindexedValueFormula E d σ F
      (TwoFamily.Section.cast (congrArg Family.data e) (s.reindex E.data σ)) := by
  intro z
  exact (TwoFamily.Section.cast_normalObj (congrArg Family.data e) _ z).trans
    (heq_of_eq ((s.reindex_normalObj E.data σ z).trans (h (σ.obj z))))
end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
