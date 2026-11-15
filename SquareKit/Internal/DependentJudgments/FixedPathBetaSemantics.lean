import SquareKit.Internal.DependentJudgments.FixedPathTransportSemantics
/-! Restrict the original J-derived beta section together with path transport. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Model.{u})
def EndomapBetaType {Γ : M.Context} (F : M.Family Γ)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F))) :=
 M.identity (M.subTy F (M.weaken Γ F)) s (M.genericVariable Γ F)
theorem reindexEndomapBeta_type {Γ Δ : M.Context} (F : M.Family Γ)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F)))
 (σ : M.Substitution Δ Γ) :
 M.subTy (EndomapBetaType M F s) (M.toStructuralModel.lift F σ) =
 EndomapBetaType M (M.subTy F σ) (reindexEndomap M F s σ) := by
 rw [EndomapBetaType, M.identity_sub]
 exact M.toStructuralModel.identity_congr (M.toStructuralModel.weaken_lift_type F σ)
  (cast_heq _ _).symm (M.toStructuralModel.variable_lift F σ)
def reindexEndomapBeta {Γ Δ : M.Context} (F : M.Family Γ)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F)))
 (p : M.Section (M.extend Γ F) (EndomapBetaType M F s))
 (σ : M.Substitution Δ Γ) :
 M.Section (M.extend Δ (M.subTy F σ)) (EndomapBetaType M (M.subTy F σ) (reindexEndomap M F s σ)) :=
 cast (congrArg (M.Section _) (reindexEndomapBeta_type M F s σ)) (M.subTm p (M.toStructuralModel.lift F σ))
def castEndomapBeta {Γ : M.Context} {F G : M.Family Γ} (e : F = G)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F)))
 (p : M.Section (M.extend Γ F) (EndomapBetaType M F s)) :
 M.Section (M.extend Γ G)
 (EndomapBetaType M G (cast (congrArg (fun H => M.Section (M.extend Γ H) (M.subTy H (M.weaken Γ H))) e) s)) := by
 cases e
 exact p
def fixedPathBetaSection {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A) :
 M.Section (M.extend Γ (M.identity A x y)) (EndomapBetaType M (M.identity A x y) (fixedPathTransportSection M A x y)) :=
 castEndomapBeta M (M.toStructuralModel.pathFamily_at A x y)
  (reindexEndomap M (M.toStructuralModel.pathFamily A x) (pathTransportSection M A x) (M.toStructuralModel.sectionSub A y))
  (reindexEndomapBeta M (M.toStructuralModel.pathFamily A x) (pathTransportSection M A x)
   (pathBetaSection M A x) (M.toStructuralModel.sectionSub A y))
end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
