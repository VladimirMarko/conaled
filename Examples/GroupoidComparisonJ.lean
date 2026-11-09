import Examples.GroupoidComparison
import SquareKit.Internal.PathTransport.ComparisonJSubstitution

/-! Contextual elimination with two changing dependent declarations. The second
is the identity family of the first variable, retaining selected arrows. -/
noncomputable section
namespace Examples.GroupoidComparisonJ
open CategoryTheory SquareKit.Internal.PathTransport
open GroupoidModel Comparison GroupoidComparison FamilyMapElimination
open Typed Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local notation "M" => Comparison.structuralModel signature

def constantBase (Γ : Comparison.Context.{0}) : Comparison.Section (signature.baseFamily Γ) where
  left := constantSection ((CategoryTheory.Functor.const Γ.left).obj (Discrete.mk false,p))
  right := constantSection ((CategoryTheory.Functor.const Γ.right).obj p)
  commutes := by
    apply GroupoidModel.Section.lift_injective
    fapply CategoryTheory.Functor.ext
    · intro γ; rfl
    · intro γ δ f
      fapply Grothendieck.ext
      · simp [GroupoidModel.Section.familyImage, GroupoidModel.Section.lift]
      · simp [GroupoidModel.Section.familyImage, GroupoidModel.Section.lift, constantSection,
          Comparison.Signature.baseFamily, signature, collapse, Grothendieck.map, Grpd.forgetToCat]
        rfl

def path := StructuralModel.pathContext M family chosenSection
def declaration : Comparison.Family path := signature.baseFamily path

def tail : StructuralModel.Telescope M path 2 :=
  .cons declaration (.cons ((declaration.reindex declaration.weaken).identity
    declaration.variable declaration.variable) .nil)

def motive : Comparison.Family (StructuralModel.Telescope.total M tail) := signature.baseFamily _

def branch : Comparison.Section (motive.reindex (StructuralModel.rootTail M family chosenSection tail)) :=
  cast (congrArg Comparison.Section (signature.base_sub _).symm) (constantBase _)

def result : Comparison.Section motive :=
  Comparison.contextualJ signature family chosenSection tail motive branch

/-- The actual constructed eliminator recovers its nonempty-tail branch. -/
example : result.reindex (StructuralModel.rootTail M family chosenSection tail) = branch :=
  Comparison.contextualJ_beta signature family chosenSection tail motive branch

/-- Both interpretations of this application commute with the changing family
comparison. This uses the result constructed by the common elimination law. -/
example : result.left.familyImage motive.map =
    result.right.reindex (StructuralModel.Telescope.total M tail).map := result.commutes

example : HEq ((leftProjection signature).mapTm result)
    (GroupoidModel.Instance.contextualJ signature.base.left signature.leftFiber
      family.left ⟨chosenSection.left⟩
      ((leftProjection signature).pathTelescope family chosenSection tail)
      ((leftProjection signature).jMotive family chosenSection tail motive)
      ((leftProjection signature).jBranch family chosenSection tail motive branch)) :=
  contextualJ_left signature family chosenSection tail motive branch

example : HEq ((rightProjection signature).mapTm result)
    (GroupoidModel.Instance.contextualJ signature.base.right signature.rightFiber
      family.right ⟨chosenSection.right⟩
      ((rightProjection signature).pathTelescope family chosenSection tail)
      ((rightProjection signature).jMotive family chosenSection tail motive)
      ((rightProjection signature).jBranch family chosenSection tail motive branch)) :=
  contextualJ_right signature family chosenSection tail motive branch

/-- An ordinary open substitution acts on the entire dependent J application. -/
example {Δ : Comparison.Context.{0}} (σ : Comparison.Substitution Δ context) :
    HEq (result.reindex (StructuralModel.pathTailMap M family chosenSection tail σ))
      (Comparison.contextualJ signature (family.reindex σ) (chosenSection.reindex σ)
        (StructuralModel.pathTail M family chosenSection tail σ)
        (motive.reindex (StructuralModel.pathTailMap M family chosenSection tail σ))
        (StructuralModel.reindexBranch M family chosenSection tail σ motive branch)) :=
  contextualJ_sub signature family chosenSection tail σ motive branch

example : Typed.ModelMap (Comparison.fullModel signature)
    (GroupoidModel.Instance.fullModel signature.base.left signature.leftFiber) :=
  leftModelMap signature

example : Typed.ModelMap (Comparison.fullModel signature)
    (GroupoidModel.Instance.fullModel signature.base.right signature.rightFiber) :=
  rightModelMap signature

end Examples.GroupoidComparisonJ
