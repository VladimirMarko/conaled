import SquareKit.Internal.Cubical.CocycleHigherNonzero
import SquareKit.Internal.DependentJudgments.PathFamilyConjugationSemantics

/-! The J-defined path-family transport and its explicit endpoint comparison in the cocycle model. -/
noncomputable section
namespace Examples.CubicalPathComparison
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics

abbrev M := cocycleModel
abbrev point : M.Section M.empty cocycleBase := ⟨zeroTerm terminal⟩
abbrev loops := cocycleBase.identity (zeroTerm terminal) (zeroTerm terminal)
abbrev loopContext := total loops.family

def loopBase : loopContext ⟶ total cocycleBase.family := pair (terminalSub _) (zeroTerm _)

theorem loopFamily_eq : reindex cocycleRootedFamily.family loopBase =
    reindex loops.family (projection loops.family) :=
  (normalizedIdentity_reindex (reindex cocycleBase.family (projection cocycleBase.family))
    ((zeroTerm terminal).reindex (projection cocycleBase.family)) (generic cocycleBase.family) loopBase).trans
  (normalizedIdentity_reindex cocycleBase.family (zeroTerm terminal) (zeroTerm terminal) (projection loops.family)).symm

def loopWitness : Term (reindex cocycleRootedFamily.family loopBase) :=
  (generic loops.family).convert loopFamily_eq.symm

def loopInclusion : loopContext ⟶ M.toStructuralModel.pathContext cocycleBase point := pair loopBase loopWitness

def transportedLoop : Term (reindex loops.family (projection loops.family)) :=
  ((pathTransportSection M cocycleBase point).down.reindex loopInclusion).convert loopFamily_eq

private theorem identity_congr {Γ : Context.{0}} {A B : Family Γ} (e : A = B)
    {a b : Term A} {c d : Term B} (ha : HEq a c) (hb : HEq b d) :
    normalizedIdentity A a b = normalizedIdentity B c d := by cases e; cases ha; cases hb; rfl

theorem comparisonFamily_eq :
    reindex (pathBetaMotive M cocycleBase point).family loopInclusion =
      normalizedIdentity (reindex loops.family (projection loops.family)) transportedLoop (generic loops.family) := by
  have e := normalizedIdentity_reindex (motive M cocycleBase cocycleRootedFamily point).family
    (pathTransportSection M cocycleBase point).down (pathWitnessSection M cocycleBase point).down loopInclusion
  exact e.trans (identity_congr loopFamily_eq
    (Term.convert_heq loopFamily_eq ((pathTransportSection M cocycleBase point).down.reindex loopInclusion)).symm
    (Term.convert_heq loopFamily_eq.symm (generic loops.family)))

def betaLoop : Term (normalizedIdentity (reindex loops.family (projection loops.family))
    transportedLoop (generic loops.family)) :=
  ((pathBetaSection M cocycleBase point).down.reindex loopInclusion).convert comparisonFamily_eq

end Examples.CubicalPathComparison
