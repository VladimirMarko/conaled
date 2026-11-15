import SquareKit.Internal.PathTransport.TwoFamilyContractionObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory
universe u
variable {Γ Δ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
def BranchFormula (c : SourceContraction i) (E : Family Γ) (F : Family Δ)
    (e : F = E.reindex i) (j : TwoFamily.Section F.data → TwoFamily.Section E.data) : Prop :=
  ∀ d, c.ValueFormula E (TwoFamily.Section.cast (congrArg Family.data e) d) (j d)
theorem SectionFormula.cast_input (c : SourceContraction i) (E : Family Γ)
    (j : TwoFamily.Section (TwoFamily.reindex i E.data) → TwoFamily.Section E.data)
    (h : c.SectionFormula E j) (F : Family Δ) (e : F = E.reindex i) :
    c.BranchFormula E F e (fun d => j (TwoFamily.Section.cast (congrArg Family.data e) d)) :=
  fun d => h (TwoFamily.Section.cast (congrArg Family.data e) d)
end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
