import SquareKit.Internal.PathTransport.TwoFamilySourceContraction
import SquareKit.Internal.PathTransport.TwoFamilyTransportObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory
universe u
variable {Γ Δ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
variable (c : SourceContraction i) (E : Family Γ)
variable (d : TwoFamily.Section (TwoFamily.reindex i E.data))
theorem objects (z : Γ) :
    ((TwoFamily.retractionJ i c.retraction c.homotopy E.data d).normalObj E.data z).fiber =
      (E.data.map (c.homotopy.app z)).obj
        ((d.normalObj (TwoFamily.reindex i E.data) (c.retraction.obj z)).fiber) :=
  TwoFamily.retractionJ_normalObj E.data i c.retraction c.homotopy d z
def ValueFormula (c : SourceContraction i) (E : Family Γ)
    (d : TwoFamily.Section (TwoFamily.reindex i E.data)) (s : TwoFamily.Section E.data) : Prop :=
  ∀ z : Γ,
    (s.normalObj E.data z).fiber =
      (E.data.map (c.homotopy.app z)).obj
        ((d.normalObj (TwoFamily.reindex i E.data) (c.retraction.obj z)).fiber)

def SectionFormula (c : SourceContraction i) (E : Family Γ)
    (j : TwoFamily.Section (TwoFamily.reindex i E.data) → TwoFamily.Section E.data) : Prop :=
  ∀ d, c.ValueFormula E d (j d)

theorem sectionFormula (c : SourceContraction i) (E : Family Γ) :
    c.SectionFormula E (TwoFamily.retractionJ i c.retraction c.homotopy E.data) :=
  c.objects E
end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
