import Examples.FrozenOrdinaryActionSemantics
import SquareKit.Internal.DependentJudgments.FixedPathBetaSemantics
import SquareKit.Internal.DependentJudgments.OrdinaryActionSubstitution
import SquareKit.Internal.DependentJudgments.OrdinaryActionCongruence

/-! Reindex the actual frozen transport and beta together, retaining ordinary action. -/
namespace Examples.FrozenOrdinaryAction
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
universe u
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
variable {Δ : M.Context} (σ : M.Substitution Δ (paths M A B).context)

def reindexedType := M.identity (M.subTy (paths M A B).family σ)
  (M.subTm (paths M A B).x σ) (M.subTm (paths M A B).y σ)

theorem reindexedType_eq : M.subTy (pathType M A B) σ = reindexedType M A B σ :=
  M.identity_sub (paths M A B).family (paths M A B).x (paths M A B).y σ

def reindexedTransport : M.Section (M.extend Δ (reindexedType M A B σ))
    (M.subTy (reindexedType M A B σ) (M.weaken Δ (reindexedType M A B σ))) :=
  cast (congrArg (fun F => M.Section (M.extend Δ F) (M.subTy F (M.weaken Δ F))) (reindexedType_eq M A B σ))
    (reindexEndomap M (pathType M A B) (transport M A B) σ)

def reindexedBeta : M.Section (M.extend Δ (reindexedType M A B σ))
    (EndomapBetaType M (reindexedType M A B σ) (reindexedTransport M A B σ)) :=
  castEndomapBeta M (reindexedType_eq M A B σ) _
    (reindexEndomapBeta M (pathType M A B) (transport M A B)
      (fixedPathBetaSection M (paths M A B).family (paths M A B).x (paths M A B).y) σ)

def reindexedP := cast (congrArg (M.Section Δ) (reindexedType_eq M A B σ)) (M.subTm (paths M A B).p σ)
def reindexedP' := cast (congrArg (M.Section Δ) (reindexedType_eq M A B σ)) (M.subTm (paths M A B).p' σ)

theorem reindexedHType_eq : M.subTy (M.identity (pathType M A B) (paths M A B).p (paths M A B).p') σ =
    M.identity (reindexedType M A B σ) (reindexedP M A B σ) (reindexedP' M A B σ) :=
  (M.identity_sub _ _ _ σ).trans (M.toStructuralModel.identity_congr (reindexedType_eq M A B σ)
    (cast_heq _ _).symm (cast_heq _ _).symm)

def reindexedH := cast (congrArg (M.Section Δ) (reindexedHType_eq M A B σ)) (M.subTm (paths M A B).h σ)

theorem action_reindex : HEq (M.subTm (action M A B) σ)
    (ordinaryApValue M (reindexedType M A B σ) (reindexedType M A B σ) (reindexedTransport M A B σ)
      (reindexedP M A B σ) (reindexedP' M A B σ) (reindexedH M A B σ)) :=
  (ordinaryApValue_sub M (pathType M A B) (pathType M A B) (transport M A B)
    (paths M A B).p (paths M A B).p' (paths M A B).h σ).trans
    (ordinaryApValue_congr M (reindexedType_eq M A B σ) (reindexedType_eq M A B σ)
      (cast_heq _ _).symm (cast_heq _ _).symm (cast_heq _ _).symm
      ((cast_heq _ _).trans (cast_heq _ _).symm))

end Examples.FrozenOrdinaryAction
