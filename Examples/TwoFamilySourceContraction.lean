import SquareKit.Internal.PathTransport.TwoFamilySourceContraction
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionReflexive
import Examples.TwoFamilyStructuralModel
/-! Source telescopes recover a chosen higher section after two dependent
extensions of a genuine path contraction. -/
noncomputable section
namespace Examples.TwoFamilySourceContraction
open CategoryTheory Bicategory SquareKit SquareKit.Internal.PathTransport
open HigherInterpretation Examples.TwoFamilyModelData
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
abbrev model := structuralModel integerContext integerContext

def paths : Context where
  toStrictTwoCategory := ⟨TwoFamily.PathContext integers.data⟩
  groupoid := inferInstance
  locallyGroupoid := inferInstance

def initial : {c : SourceContraction (Γ := paths) (Δ := integers.total)
    (TwoFamily.pathReflexivity integers.data) // c.Normalized} :=
  ⟨⟨TwoFamily.pathFirst integers.data, TwoFamily.pathContraction integers.data⟩,
    TwoFamily.pathReflexivity_first integers.data, TwoFamily.pathContraction_reflexive integers.data⟩

def first : Family paths := Family.constant paths integerContext
def second : Family first.total :=
  Family.identity (first.reindex (TwoFamily.projectionHigher first.data))
    (TwoFamily.variableSection first.data) (TwoFamily.variableSection first.data)

def tail : Typed.StructuralModel.Telescope model paths 2 :=
  .cons first (.cons second .nil)
def inclusion : model.Substitution integers.total paths := ⟨TwoFamily.pathReflexivity integers.data⟩
def motive : model.Family (tail.total model) := model.subTy second (model.weaken first.total second)
def selected : model.Section (tail.total model) motive := model.genericVariable first.total second
def branch : model.Section _ (model.subTy motive (tail.liftSub model inclusion)) :=
  model.subTm selected (tail.liftSub model inclusion)

example : model.subTm
    (SourceContraction.eliminate integerContext integerContext tail inclusion initial motive branch)
    (tail.liftSub model inclusion) = branch :=
  SourceContraction.eliminate_beta integerContext integerContext tail inclusion initial motive branch
end Examples.TwoFamilySourceContraction
