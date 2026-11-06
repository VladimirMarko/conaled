import Examples.FrozenMemoHigherObservation
import Examples.FrozenMemoStageEvaluation
import Examples.TwoFamilyModelData
import SquareKit.Internal.PathTransport.TwoFamilyFullModel
/-! Assign all eight frozen binders in the constructed higher model. The path
family starts at a fixed point and ends at the generic variable. The source
evaluation equations identify the generated context and selected homotopy. -/
noncomputable section
namespace Examples.TwoFamilyFrozenPoint
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoOpenIdentityHigher
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
abbrev emptyA := Family.constant Context.empty integerContext

def fixedLift : StrictPseudofunctor Context.empty emptyA.total :=
  StrictPseudofunctor.mk'' {
    obj := fun γ => ⟨γ, point⟩
    map := fun p => ⟨p, arrow⟩
    map₂ := fun α => ⟨α, Multiplicative.ofAdd (0:ℤ)⟩
  }
def fixed : TwoFamily.Section emptyA.data where
  lift := fixedLift
  over := strictFunctorData_ext rfl
end Examples.TwoFamilyFrozenPoint
namespace Examples.TwoFamilyFrozenPoint
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoOpenIdentityHigher
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
abbrev emptyB : Family emptyA.total := Family.identity
  (emptyA.reindex (TwoFamily.projectionHigher emptyA.data))
  (fixed.reindex emptyA.data (TwoFamily.projectionHigher emptyA.data))
  (TwoFamily.variableSection emptyA.data)
abbrev model := structuralModel integerContext integerContext
open Examples.FrozenMemoStages

abbrev assignedHomotopyContext : Context := homotopyContext model emptyA emptyB
def assignedHomotopyPoint (k : ℤ) : assignedHomotopyContext :=
  ⟨⟨⟨⟨⟨⟨⟨⟨PUnit.unit⟩⟩, point⟩, point⟩, point⟩, ⟨arrow⟩⟩, ⟨arrow⟩⟩,
    ⟨⟨Multiplicative.ofAdd k⟩⟩⟩

abbrev assignedContext : Context := inputContext model emptyA emptyB
/-- The selected second identity is the integer `k`; the other path data are identities. -/
def assignedPoint (k : ℤ) : assignedContext :=
  ⟨⟨assignedHomotopyPoint k, ⟨arrow⟩⟩, ⟨arrow⟩⟩


set_option maxRecDepth 2000
-- Infer these proof types once instead of expanding the full dependent context.
set_option linter.defProp false

def retained (k : ℤ) :=
  selectedHomotopy_payload integerContext integerContext emptyA emptyB (assignedPoint k)

def sourceContext := inputContext_eval (fullModel integerContext integerContext) emptyA emptyB
def sourceHomotopy := selectedHomotopy_eval (fullModel integerContext integerContext) emptyA emptyB
end Examples.TwoFamilyFrozenPoint
