import Examples.GuardedGroupoidMemo
import SquareKit.Internal.DependentJudgments.FixedPathTransportSource
import SquareKit.Internal.DependentJudgments.FixedPathTransportSemantics
/-! The fixed-endpoint source transport denotes the original selected J section. -/
namespace Examples.FixedPathTransportEvaluation
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Model.{u}) {V : Type} (ρ : V → Value M.toStructuralModel)
private theorem endomap_value_cast {Γ : M.Context} {F G : M.Family Γ} (e : F = G)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F))) :
 Value.term (M := M.toStructuralModel) (M.extend Γ F) (M.subTy F (M.weaken Γ F)) s =
 Value.term (M.extend Γ G) (M.subTy G (M.weaken Γ G))
 (cast (congrArg (fun H => M.Section (M.extend Γ H) (M.subTy H (M.weaken Γ H))) e) s) := by
 cases e
 rfl
private theorem reindex_endomap_value {Γ Δ : M.Context} (F : M.Family Γ)
 (s : M.Section (M.extend Γ F) (M.subTy F (M.weaken Γ F))) (σ : M.Substitution Δ Γ) :
 Value.term (M := M.toStructuralModel) (M.extend Δ (M.subTy F σ))
  (M.subTy (M.subTy F (M.weaken Γ F)) (M.toStructuralModel.lift F σ))
  (M.subTm s (M.toStructuralModel.lift F σ)) =
 Value.term (M.extend Δ (M.subTy F σ))
  (M.subTy (M.subTy F σ) (M.weaken Δ (M.subTy F σ))) (reindexEndomap M F s σ) :=
 Value.term_eq (M.toStructuralModel.weaken_lift_type F σ) (cast_heq _ _).symm
theorem fixedPathTransport_eval (g a sx sy : Contextual.Expression V)
 (Γ : M.Context) (A : M.Family Γ) (x y : M.Section Γ A)
 (hg : g.eval (Contextual.algebra M) ρ = .context Γ)
 (ha : a.eval (Contextual.algebra M) ρ = .family Γ A)
 (hx : sx.eval (Contextual.algebra M) ρ = .term Γ A x)
 (hy : sy.eval (Contextual.algebra M) ρ = .term Γ A y) :
 (Contextual.fixedPathTransportTerm g a sx sy).eval (Contextual.algebra M) ρ =
 .term (M.extend Γ (M.identity A x y))
 (M.subTy (M.identity A x y) (M.weaken Γ (M.identity A x y)))
 (fixedPathTransportSection M A x y) := by
 have hP := pathFamily_eval M ρ g a sx Γ A x hg ha hx
 have hrefl := reflexivity_eval M ρ a sx Γ A x ha hx
 have hb := hrefl.trans (Value.term_eq (M.toStructuralModel.pathFamily_root A x).symm
  (cast_heq (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_root A x).symm) (M.reflexivity A x)).symm)
 have hT := transportGeneric_eval M ρ g a (Contextual.pathFamily g a sx) sx (Contextual.reflexivity a sx)
  Γ A (M.toStructuralModel.pathFamily A x) x (pathTransportBranch M A x) hg ha hP hx hb
 have hs := sectionSub_eval M ρ g a sy Γ A y hg ha hy
 have hl := lift_eval M ρ g (Contextual.pathFamily g a sx) (Contextual.sectionSub g a sy)
  (M.extend Γ A) Γ (M.toStructuralModel.pathFamily A x) _ hg hP hs
 have h := subTm_eval M ρ _ _ _ _ _ _ _ hT hl
 exact h.trans ((reindex_endomap_value M (M.toStructuralModel.pathFamily A x)
  (pathTransportSection M A x) (M.toStructuralModel.sectionSub A y)).trans
  (endomap_value_cast M (M.toStructuralModel.pathFamily_at A x y) _))
end Examples.FixedPathTransportEvaluation
