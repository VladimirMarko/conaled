import SquareKit.Internal.DependentJudgments.PathFamilyConjugationSemantics
/-! Restrict the actual path-transport section to fixed endpoints.
Endpoint evaluation recovers the same J-derived transport value. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open PathTransport.Typed StructuralModel
universe u
variable (M : Model.{u})
def reindexEndomap {Γ Δ : M.Context} (F : M.Family Γ)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F)))
 (σ : M.Substitution Δ Γ) :
 M.Section (M.extend Δ (M.subTy F σ)) (M.subTy (M.subTy F σ) (M.weaken Δ (M.subTy F σ))) :=
 cast (congrArg (M.Section _) (M.toStructuralModel.weaken_lift_type F σ)) (M.subTm s (M.toStructuralModel.lift F σ))
def fixedPathTransportSection {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A) :
 M.Section (M.extend Γ (M.identity A x y))
 (M.subTy (M.identity A x y) (M.weaken Γ (M.identity A x y))) :=
 cast (congrArg (fun F => M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F)))
  (M.toStructuralModel.pathFamily_at A x y))
 (reindexEndomap M (M.toStructuralModel.pathFamily A x) (pathTransportSection M A x)
  (M.toStructuralModel.sectionSub A y))
theorem lift_section_any {Γ Δ : M.Context} (F : M.Family Γ)
 (σ : M.Substitution Δ Γ) (p : M.Section Δ (M.subTy F σ)) :
 M.compSub (M.toStructuralModel.lift F σ) (M.toStructuralModel.sectionSub (M.subTy F σ) p) =
 M.pairSub F σ p := by
 apply M.toStructuralModel.pair_ext F
 · rw [← M.comp_assoc, M.toStructuralModel.weaken_lift, M.comp_assoc,
     M.toStructuralModel.weaken_section, M.comp_id_right, M.weaken_pair]
 · apply (M.subTm_comp _ _ _).symm.trans
   apply (M.toStructuralModel.subTm_congr (M.toStructuralModel.weaken_lift_type F σ)
     (M.toStructuralModel.variable_lift F σ) _).trans
   exact (M.toStructuralModel.variable_section (M.subTy F σ) p).trans (M.variable_pair F σ p).symm
theorem reindexEndomap_endpoint {Γ Δ : M.Context} (F : M.Family Γ)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F)))
 (σ : M.Substitution Δ Γ) (p : M.Section Δ (M.subTy F σ)) :
 HEq (M.subTm (reindexEndomap M F s σ) (M.toStructuralModel.sectionSub (M.subTy F σ) p))
 (M.subTm s (M.pairSub F σ p)) := by
 apply (M.toStructuralModel.subTm_congr (M.toStructuralModel.weaken_lift_type F σ).symm
   (cast_heq _ _) _).trans
 apply (M.subTm_comp _ _ _).trans
 rw [lift_section_any]
theorem castEndomap_endpoint {Γ : M.Context} {F G : M.Family Γ} (e : F = G)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F))) (p : M.Section Γ G) :
 HEq (M.subTm (cast (congrArg (fun H => M.Section (M.extend Γ H) (M.subTy H (M.weaken Γ H))) e) s)
   (M.toStructuralModel.sectionSub G p))
 (M.subTm s (M.toStructuralModel.sectionSub F (cast (congrArg (M.Section Γ) e.symm) p))) := by
 cases e
 rfl
theorem fixedPathTransportSection_endpoint {Γ : M.Context} (A : M.Family Γ)
 (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y)) :
 HEq (M.subTm (fixedPathTransportSection M A x y)
   (M.toStructuralModel.sectionSub (M.identity A x y) p))
 (pathTransportValue M A x y p) :=
 (castEndomap_endpoint M (M.toStructuralModel.pathFamily_at A x y) _ p).trans
  ((reindexEndomap_endpoint M (M.toStructuralModel.pathFamily A x) (pathTransportSection M A x)
    (M.toStructuralModel.sectionSub A y) _).trans (pathTransportSection_endpoint M A x y p))
end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
