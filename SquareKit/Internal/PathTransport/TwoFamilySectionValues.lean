import SquareKit.Internal.PathTransport.TwoFamilyTransportObjects
import SquareKit.Internal.PathTransport.TwoFamilyStructuralModel
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
universe u
variable {Γ Δ : Context.{u}}
def sectionValue (A : Family Γ) (s : ULift.{u+1} (TwoFamily.Section A.data)) (γ : Γ) : A.data.obj γ :=
  (s.down.normalObj A.data γ).fiber

theorem sectionValue_cast {A B : Family Γ} (e : A = B)
    (s : ULift.{u+1} (TwoFamily.Section A.data)) (γ : Γ) :
    HEq (sectionValue B (cast (congrArg (fun F => ULift.{u+1} (TwoFamily.Section F.data)) e) s) γ)
      (sectionValue A s γ) := by
  cases e
  rfl

theorem sectionValue_reindex (A : Family Γ) (s : ULift.{u+1} (TwoFamily.Section A.data))
    (σ : StrictPseudofunctor Δ Γ) (δ : Δ) :
    sectionValue (A.reindex σ) ⟨s.down.reindex A.data σ⟩ δ = sectionValue A s (σ.obj δ) :=
  TwoFamily.Section.reindex_normalObj A.data s.down σ δ
end SquareKit.Internal.PathTransport.HigherInterpretation
