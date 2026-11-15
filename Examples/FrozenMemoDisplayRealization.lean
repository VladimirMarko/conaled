import Examples.FrozenMemoStageEvaluation
/-! Interpret the original frozen displayed tails and both substitution maps
in any constructed contextual model. -/
noncomputable section
namespace Examples.FrozenMemoStages
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
universe u
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
local notation "env" => Examples.FrozenMemoSignature.environment M A B
local notation "S" => M.toStructuralModel

def tailUData : DisplayRealization M env signature.tailU (qPoints S A B).context :=
 .cons signature.withQ.hU (.nil signature.withQ.hU.extend) _ (uFamily S A B)
  (uFamily_eval M A B) (.nil _ (inputContext S A B))
def tailQData : DisplayRealization M env signature.tailQ (homotopyPoints S A B).context :=
 .cons signature.withH.hQ signature.tailU _ (qFamily S A B)
  (qFamily_eval M A B) (tailUData M A B)
def tailHData : DisplayRealization M env signature.tailH (parallel S A B).context :=
 .cons signature.withParallel.hIdentity signature.tailQ _ (parallel S A B).identity
  (parallel_eval M A B).identity_eval (tailQData M A B)
def tailParallelData : DisplayRealization M env signature.tailParallel
    ((((Points.initial A B).addY).addZ).addP (M := S)).context :=
 .cons signature.withP.toPoints.hPath signature.tailH _ _
  ((((initial_eval M A B).addY).addZ).addP).toPointsEvaluation.path_eval (tailHData M A B)
def tailPData : DisplayRealization M env signature.tailP
    (((Points.initial (M := S) A B).addY).addZ).context :=
 .cons signature.xyz.hPath signature.tailParallel _ _
  (((initial_eval M A B).addY).addZ).path_eval (tailParallelData M A B)
def tailZData : DisplayRealization M env signature.tailZ
    ((Points.initial (M := S) A B).addY).context :=
 .cons signature.xy.hx.family signature.tailP _ _
  ((initial_eval M A B).addY).family_eval (tailPData M A B)
def duplicate := (S).sectionSub (Points.initial (M := S) A B).family (Points.initial (M := S) A B).x
theorem duplicate_eval : signature.duplicate.eval (Contextual.algebra M) env =
 .substitution (Points.initial (M := S) A B).context ((Points.initial (M := S) A B).addY).context (duplicate M A B) :=
 sectionSub_eval M env _ _ _ _ _ _ (initial_eval M A B).context_eval
  (initial_eval M A B).family_eval (initial_eval M A B).x_eval

def sigmaData := (tailZData M A B).pullback signature.point.hx.family.context signature.duplicate_typed
 (Points.initial (M := S) A B).context (duplicate M A B)
 (initial_eval M A B).context_eval (duplicate_eval M A B)

def afterZData := (tailPData M A B).pullback
 (signature.xy.hx.family.substitute signature.duplicate_typed).extend
 (signature.duplicate_typed.lift signature.xy.hx.family)
 (M.extend (Points.initial (M := S) A B).context
   (M.subTy ((Points.initial (M := S) A B).addY).family (duplicate M A B)))
 (M.lift ((Points.initial (M := S) A B).addY).family (duplicate M A B))
 (extend_eval M env _ _ _ _ (initial_eval M A B).context_eval
  (subTy_eval M env _ _ _ _ _ _ ((initial_eval M A B).addY).family_eval (duplicate_eval M A B)))
 (lift_eval M env _ _ _ _ _ _ _ (initial_eval M A B).context_eval
  ((initial_eval M A B).addY).family_eval (duplicate_eval M A B))
theorem deltaZ_eq :
 M.subTy ((Points.initial (M := S) A B).addY).family (duplicate M A B) =
  (Points.initial (M := S) A B).family :=
 (S).weaken_section_type (Points.initial (M := S) A B).family
  (Points.initial (M := S) A B).x (Points.initial (M := S) A B).family

def deltaX := cast (congrArg (M.Section (Points.initial (M := S) A B).context) (deltaZ_eq M A B).symm)
 (Points.initial (M := S) A B).x

theorem deltaZ_eval : signature.deltaZType.eval (Contextual.algebra M) env =
 .family (Points.initial (M := S) A B).context
  (M.subTy ((Points.initial (M := S) A B).addY).family (duplicate M A B)) :=
 subTy_eval M env _ _ _ _ _ _ ((initial_eval M A B).addY).family_eval (duplicate_eval M A B)

def tauData := (afterZData M A B).display.pullback signature.point.hx.family.context signature.deltaX_as_z.section
 (Points.initial (M := S) A B).context
 ((S).sectionSub (M.subTy ((Points.initial (M := S) A B).addY).family (duplicate M A B)) (deltaX M A B))
 (initial_eval M A B).context_eval
 (sectionSub_eval M env _ _ _ _ _ _ (initial_eval M A B).context_eval
  (deltaZ_eval M A B) ((initial_eval M A B).x_eval.trans (Value.term_eq (deltaZ_eq M A B).symm (cast_heq _ _).symm)))
end Examples.FrozenMemoStages
