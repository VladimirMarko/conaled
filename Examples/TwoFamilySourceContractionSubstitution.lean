import SquareKit.Internal.PathTransport.TwoFamilySourceContractionSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionReindex
import Examples.TwoFamilySourceContraction
/-! The selected source branch survives substitution of the underlying higher
family, across both dependent telescope entries. -/
noncomputable section
namespace Examples.TwoFamilySourceContractionSubstitution
open CategoryTheory Bicategory SquareKit SquareKit.Internal.PathTransport
open HigherInterpretation Examples.TwoFamilyModelData Examples.TwoFamilySourceContraction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def pathsFor (A : Family integerContext) : Context where
  toStrictTwoCategory := ⟨TwoFamily.PathContext A.data⟩
  groupoid := inferInstance
  locallyGroupoid := inferInstance

def initialFor (A : Family integerContext) :
    {c : SourceContraction (Γ := pathsFor A) (Δ := A.total)
      (TwoFamily.pathReflexivity A.data) // c.Normalized} :=
  ⟨⟨TwoFamily.pathFirst A.data, TwoFamily.pathContraction A.data⟩,
    TwoFamily.pathReflexivity_first A.data, TwoFamily.pathContraction_reflexive A.data⟩

variable (σ : StrictPseudofunctor integerContext integerContext)
def nextInclusion : model.Substitution (integers.reindex σ).total (pathsFor (integers.reindex σ)) :=
  ⟨TwoFamily.pathReflexivity (integers.reindex σ).data⟩
def pathMap : model.Substitution (pathsFor (integers.reindex σ)) paths :=
  ⟨TwoFamily.pathReindex integers.data σ⟩
def branchMap : model.Substitution (integers.reindex σ).total integers.total :=
  ⟨TwoFamily.reindexHigher integers.data σ⟩
theorem inclusion_square : model.compSub (pathMap σ) (nextInclusion σ) =
    model.compSub inclusion (branchMap σ) :=
  ULift.ext (TwoFamily.pathReindex_reflexivity integers.data σ)

theorem contraction_square : SourceContraction.Square initial.val
    (initialFor (integers.reindex σ)).val (pathMap σ).down (branchMap σ).down :=
  ⟨TwoFamily.pathReindex_reflexivity integers.data σ,
    (TwoFamily.pathReindex_first integers.data σ).symm,
    TwoFamily.pathContraction_reindex integers.data σ⟩

def selectedBranch := SourceContraction.branchReindex integerContext integerContext tail
  inclusion (nextInclusion σ) (pathMap σ) (branchMap σ) (inclusion_square σ) motive branch

example : model.subTm
    (SourceContraction.eliminate integerContext integerContext tail inclusion initial motive branch)
    (tail.liftSub model (pathMap σ)) =
    SourceContraction.eliminate integerContext integerContext (tail.pullback model (pathMap σ))
      (nextInclusion σ) (initialFor (integers.reindex σ))
      (model.subTy motive (tail.liftSub model (pathMap σ))) (selectedBranch σ) :=
  SourceContraction.eliminate_reindex integerContext integerContext tail inclusion (nextInclusion σ)
    (pathMap σ) (branchMap σ) (inclusion_square σ) initial (initialFor (integers.reindex σ))
    (contraction_square σ) motive branch
end Examples.TwoFamilySourceContractionSubstitution
