import SquareKit.Internal.PathTransport.TwoFamilySigmaSecondReindex
/-! Whole-section pairing commutes with substitution. The proof uses the two projection laws and the proved beta and eta equations. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
theorem Section.sigmaPair_congr {a a' : Section F} (e : a = a')
    (b : Section (TwoFamily.reindex a.lift B)) (b' : Section (TwoFamily.reindex a'.lift B))
    (hb : HEq b b') : a.sigmaPair F B b = a'.sigmaPair F B b' := by
  cases e
  cases eq_of_heq hb
  rfl

theorem Section.sigma_ext (s t : Section (sigmaFamily F B))
    (h1 : s.sigmaFirst F B = t.sigmaFirst F B)
    (h2 : HEq (s.sigmaSecond F B) (t.sigmaSecond F B)) : s = t :=
  (s.sigmaPair_eta F B).symm.trans
    ((Section.sigmaPair_congr F B h1 _ _ h2).trans (t.sigmaPair_eta F B))

variable (σ : StrictPseudofunctor Δ Γ)
theorem sigmaPair_reindex_family (a : Section F) :
    reindex (a.reindex F σ).lift (reindex (reindexHigher F σ) B) =
      reindex σ (reindex a.lift B) := by
  rw [reindex_comp, reindex_comp]
  exact congrArg (fun k => reindex k B) (a.reindex_lift F σ)

def Section.sigmaPairReindexSecond (a : Section F) (b : Section (TwoFamily.reindex a.lift B)) :
    Section (TwoFamily.reindex (a.reindex F σ).lift (TwoFamily.reindex (reindexHigher F σ) B)) :=
  Section.cast (sigmaPair_reindex_family F B σ a).symm (b.reindex _ σ)

theorem Section.sigmaPair_reindex (a : Section F) (b : Section (TwoFamily.reindex a.lift B)) :
    Section.cast (sigmaFamily_reindex F σ B)
      ((a.reindex F σ).sigmaPair (TwoFamily.reindex σ F) (TwoFamily.reindex (reindexHigher F σ) B)
        (a.sigmaPairReindexSecond F B σ b)) =
      (a.sigmaPair F B b).reindex _ σ := by
  let A := TwoFamily.reindex σ F
  let B' := TwoFamily.reindex (reindexHigher F σ) B
  let original := a.sigmaPair F B b
  let t := original.sigmaReindex F B σ
  let rebuilt := (a.reindex F σ).sigmaPair A B' (a.sigmaPairReindexSecond F B σ b)
  have ht1 : t.sigmaFirst A B' = a.reindex F σ := by
    rw [Section.sigmaFirst_reindex]
    exact congrArg (fun z : Section F => z.reindex F σ) (Section.sigmaPair_first F B a b)
  have h1 : rebuilt.sigmaFirst A B' = t.sigmaFirst A B' :=
    (Section.sigmaPair_first A B' _ _).trans ht1.symm
  have h2 : HEq (rebuilt.sigmaSecond A B') (t.sigmaSecond A B') := by
    apply HEq.trans (Section.sigmaPair_second_heq A B' _ _)
    apply HEq.trans (Section.cast_heq _ _)
    apply HEq.trans _ (Section.sigmaSecond_reindex_heq F B σ original).symm
    exact (Section.reindex_heq
      (congrArg (fun z : Section F => TwoFamily.reindex z.lift B) (Section.sigmaPair_first F B a b))
      (original.sigmaSecond F B) b (Section.sigmaPair_second_heq F B a b) σ).symm
  have h := Section.sigma_ext A B' rebuilt t h1 h2
  apply eq_of_heq
  apply HEq.trans (Section.cast_heq _ _)
  apply HEq.trans (heq_of_eq h)
  exact Section.cast_heq _ _
end SquareKit.Internal.PathTransport.TwoFamily
