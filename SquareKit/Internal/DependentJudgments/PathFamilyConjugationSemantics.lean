import SquareKit.Internal.DependentJudgments.DerivedPathSemantics
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable (M : PathTransport.Typed.Model.{u})
def pathTransportBranch {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :
    M.Section Γ (M.subTy (M.toStructuralModel.pathFamily A x) (M.toStructuralModel.sectionSub A x)) :=
  cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_root A x).symm) (M.reflexivity A x)
def pathTransportSection {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :=
  transportSection M A (M.toStructuralModel.pathFamily A x) x (pathTransportBranch M A x)
def pathWitnessSection {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :=
  M.genericVariable (M.extend Γ A) (M.toStructuralModel.pathFamily A x)
def pathBetaMotive {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :=
  M.identity (motive M A (M.toStructuralModel.pathFamily A x) x)
    (pathTransportSection M A x) (pathWitnessSection M A x)
theorem pathWitness_root {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :
    HEq (M.subTm (pathWitnessSection M A x) (M.toStructuralModel.rootSub A x)) (M.reflexivity A x) :=
  (M.variable_pair _ _ _).trans (cast_heq _ _)
theorem pathBetaMotive_root {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :
    M.subTy (pathBetaMotive M A x) (M.toStructuralModel.rootSub A x) =
      M.identity (M.identity A x x) (M.reflexivity A x) (M.reflexivity A x) := by
  unfold pathBetaMotive
  rw [M.identity_sub]
  exact M.toStructuralModel.identity_congr
    ((motive_root M A (M.toStructuralModel.pathFamily A x) x).trans (M.toStructuralModel.pathFamily_root A x))
    ((transportSection_root M A (M.toStructuralModel.pathFamily A x) x (pathTransportBranch M A x)).trans (cast_heq _ _))
    (pathWitness_root M A x)
def pathBetaSection {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :
    M.Section (M.toStructuralModel.pathContext A x) (pathBetaMotive M A x) :=
  M.j A x .nil (pathBetaMotive M A x)
    (cast (congrArg (M.Section Γ) (pathBetaMotive_root M A x).symm)
      (M.reflexivity (M.identity A x x) (M.reflexivity A x)))

theorem pathBetaSection_root {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A) :
    HEq (M.subTm (pathBetaSection M A x) (M.toStructuralModel.rootSub A x))
      (M.reflexivity (M.identity A x x) (M.reflexivity A x)) :=
  (M.j_beta A x .nil _ _).trans (cast_heq _ _)
def pathTransportValue {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) : M.Section Γ (M.identity A x y) :=
  cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_at A x y))
    (transportValue M A (M.toStructuralModel.pathFamily A x) x y p (pathTransportBranch M A x))
theorem pathTransportSection_endpoint {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    HEq (M.subTm (pathTransportSection M A x) (M.toStructuralModel.endpointSub A x y p))
      (pathTransportValue M A x y p) := by
  unfold pathTransportValue transportValue
  exact ((cast_heq _ _).trans (cast_heq _ _)).symm
theorem pathWitness_endpoint {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    HEq (M.subTm (pathWitnessSection M A x) (M.toStructuralModel.endpointSub A x y p)) p :=
  (M.variable_pair _ _ _).trans (cast_heq _ _)
theorem pathBetaMotive_endpoint {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    M.subTy (pathBetaMotive M A x) (M.toStructuralModel.endpointSub A x y p) =
      M.identity (M.identity A x y) (pathTransportValue M A x y p) p := by
  unfold pathBetaMotive
  rw [M.identity_sub]
  exact M.toStructuralModel.identity_congr
    ((motive_endpoint M A (M.toStructuralModel.pathFamily A x) x y p).trans (M.toStructuralModel.pathFamily_at A x y))
    (pathTransportSection_endpoint M A x y p) (pathWitness_endpoint M A x y p)
def pathBetaValue {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    M.Section Γ (M.identity (M.identity A x y) (pathTransportValue M A x y p) p) :=
  cast (congrArg (M.Section Γ) (pathBetaMotive_endpoint M A x y p))
    (M.subTm (pathBetaSection M A x) (M.toStructuralModel.endpointSub A x y p))
end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
