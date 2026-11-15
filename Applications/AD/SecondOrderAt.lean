import Applications.AD.SecondOrder

/-! Tangent transport at admitted points, without global smoothness across singularities. -/
noncomputable section
open scoped ContDiff Topology
namespace Applications.AD.SecondOrderAt
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The semantic tangent operation. Its laws state their local admission premises. -/
def lift (f : E → F) (p : E × E) : F × F := (f p.1, fderiv ℝ f p.1 p.2)

theorem lift_global (f : E → F) (hf : ContDiff ℝ ∞ f) :
    lift f = SecondOrder.lift f hf := rfl

theorem lift_comp (f : E → F) (g : F → G) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    lift (g ∘ f) (x,v) = lift g (lift f (x,v)) := by
  simp [lift, fderiv_comp x hg hf]

theorem lift_contDiffAt (f : E → F) (x v : E) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (lift f) (x,v) := by
  exact (hf.comp (x,v) contDiffAt_fst).prodMk
    (((hf.fderiv_right (by simp)).comp (x,v) contDiffAt_fst).clm_apply contDiffAt_snd)

/-- Iterate the same semantic tangent operation. -/
def twice (f : E → F) := lift (lift f)

theorem twice_global (f : E → F) (hf : ContDiff ℝ ∞ f) :
    twice f = SecondOrder.twice f hf := rfl

theorem twice_formula (f : E → F) (x v u w : E) (hf : ContDiffAt ℝ ∞ f x) :
    twice f ((x,v),(u,w)) =
      ((f x, fderiv ℝ f x v),
       (fderiv ℝ f x u, SecondOrder.second f x u v + fderiv ℝ f x w)) := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hx := (hf.differentiableAt (by simp)).hasFDerivAt.comp (x,v)
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hh := ((hd.differentiableAt (by simp)).hasFDerivAt.comp (x,v)
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt).clm_apply
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have he := (hx.prodMk hh).fderiv
  change ((f x, fderiv ℝ f x v), fderiv ℝ (lift f) (x,v) (u,w)) = _
  rw [show fderiv ℝ (lift f) (x,v) = _ from he]
  simp [SecondOrder.second, add_comm]

theorem twice_comp (f : E → F) (g : F → G) (x v u w : E)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) :
    twice (g ∘ f) ((x,v),(u,w)) = twice g (twice f ((x,v),(u,w))) := by
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 g (f x) := hg.of_le (by simp)
  have hfe : ∀ᶠ p : E × E in 𝓝 (x,v), ContDiffAt ℝ 1 f p.1 :=
    (continuousAt_fst : ContinuousAt (fun p : E × E => p.1) (x,v)).eventually
      (hf1.eventually (by simp))
  have hge : ∀ᶠ p : E × E in 𝓝 (x,v), ContDiffAt ℝ 1 g (f p.1) :=
    (hf.continuousAt.comp (continuousAt_fst : ContinuousAt (fun p : E × E => p.1) (x,v))).eventually
      (hg1.eventually (by simp))
  have he : lift (g ∘ f) =ᶠ[𝓝 (x,v)] lift g ∘ lift f := by
    filter_upwards [hfe, hge] with p hp hq
    exact lift_comp f g p.1 p.2 hp.differentiableAt_one hq.differentiableAt_one
  change lift (lift (g ∘ f)) ((x,v),(u,w)) = _
  have hval := he.eq_of_nhds
  have hder := he.fderiv_eq (𝕜 := ℝ)
  rw [show lift (lift (g ∘ f)) ((x,v),(u,w)) =
      lift (lift g ∘ lift f) ((x,v),(u,w)) from Prod.ext hval (congrArg (fun L => L (u,w)) hder)]
  exact lift_comp (lift f) (lift g) (x,v) (u,w)
    ((lift_contDiffAt f x v hf).differentiableAt (by simp))
    ((lift_contDiffAt g (f x) (fderiv ℝ f x v) hg).differentiableAt (by simp))

theorem second_of_directional (f g : E → F) (x v u : E) (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ ∞ f x)
    (he : (fun z => fderiv ℝ f z v) =ᶠ[𝓝 x] g)
    (hg : HasFDerivAt g L x) : SecondOrder.second f x u v = L u := by
  have hs : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hd := (hs.differentiableAt (by simp)).hasFDerivAt
  have hh := hd.clm_apply (hasFDerivAt_const v x)
  have eq := hh.unique (hg.congr_of_eventuallyEq he)
  have ev := congrArg (fun K : E →L[ℝ] F => K u) eq
  simpa [SecondOrder.second] using ev

end Applications.AD.SecondOrderAt
