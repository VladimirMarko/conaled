import Applications.AD.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Experimental second-order tangent transport, using the existing certified AD tangent. -/
noncomputable section
open scoped ContDiff
namespace Applications.AD.SecondOrder
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def lift (f : E → F) (hf : ContDiff ℝ ∞ f) : E × E → F × F := tangent (DMap.ofSmooth f hf)

theorem lift_smooth (f : E → F) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (lift f hf) :=
  (hf.comp contDiff_fst).prodMk (hf.contDiff_fderiv_apply (by simp))

theorem lift_comp (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    lift (g ∘ f) (hg.comp hf) = lift g hg ∘ lift f hf := by
  have h : DMap.ofSmooth (g ∘ f) (hg.comp hf) =
      DMap.comp (DMap.ofSmooth g hg) (DMap.ofSmooth f hf) := DMap.ext (fun _ => rfl)
  funext p
  change tangent (DMap.ofSmooth (g ∘ f) _) p = _
  rw [h, tangent_comp]
  rfl

def twice (f : E → F) (hf : ContDiff ℝ ∞ f) := lift (lift f hf) (lift_smooth f hf)

theorem twice_comp (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    twice (g ∘ f) (hg.comp hf) = twice g hg ∘ twice f hf := by
  unfold twice
  have congr_lift {a b : E × E → G × G} (ha : ContDiff ℝ ∞ a)
      (hb : ContDiff ℝ ∞ b) (h : a = b) : lift a ha = lift b hb := by
    cases h
    rfl
  exact (congr_lift _ _ (lift_comp f g hf hg)).trans (lift_comp _ _ _ _)

/-- The actual derivative of the derivative, with both directions displayed. -/
def second (f : E → F) (x v u : E) : F := fderiv ℝ (fderiv ℝ f) x v u

theorem twice_formula (f : E → F) (hf : ContDiff ℝ ∞ f) (x v u w : E) :
    twice f hf ((x,v),(u,w)) =
      ((f x, fderiv ℝ f x v), (fderiv ℝ f x u, second f x u v + fderiv ℝ f x w)) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hx := (hf.differentiable (by simp) x).hasFDerivAt.comp (x,v) (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hh := ((hd.differentiable (by simp) x).hasFDerivAt.comp (x,v)
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt).clm_apply (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have he := (hx.prodMk hh).fderiv
  change ((f x, fderiv ℝ f x v), fderiv ℝ (lift f hf) (x,v) (u,w)) = _
  rw [show fderiv ℝ (lift f hf) (x,v) = _ from he]
  simp [second, add_comm]

/-- Stored quadratic coefficient is half the second derivative. -/
def jet (f : E → F) (x v w : E) : F × F × F :=
  (f x, fderiv ℝ f x v, fderiv ℝ f x w + (1/2 : ℝ) • second f x v v)

def encode (p : E × E × E) : (E × E) × (E × E) := ((p.1,p.2.1),(p.2.1,(2 : ℝ) • p.2.2))

theorem encode_injective : Function.Injective (encode : (E × E × E) → _) := by
  intro a b h
  have h1 : a.1 = b.1 := congrArg (fun p => p.1.1) h
  have h2 : a.2.1 = b.2.1 := congrArg (fun p => p.1.2) h
  have h3 : (2 : ℝ) • a.2.2 = (2 : ℝ) • b.2.2 := congrArg (fun p => p.2.2) h
  apply Prod.ext h1
  apply Prod.ext h2
  exact (smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)) h3

theorem twice_encode (f : E → F) (hf : ContDiff ℝ ∞ f) (p : E × E × E) :
    twice f hf (encode p) = encode (jet f p.1 p.2.1 p.2.2) := by
  rw [encode, twice_formula]
  dsimp [encode, jet]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  simp only [map_smul, smul_add, smul_smul]
  norm_num
  exact add_comm _ _

theorem jet_comp (f : E → F) (g : F → G) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x v w : E) :
    jet (g ∘ f) x v w =
      jet g (jet f x v w).1 (jet f x v w).2.1 (jet f x v w).2.2 := by
  apply encode_injective
  rw [← twice_encode _ (hg.comp hf) (x,v,w), twice_comp]
  change twice g hg (twice f hf (encode (x,v,w))) = _
  rw [twice_encode, twice_encode]

theorem jet_linear (L : E →L[ℝ] F) (x v w : E) : jet L x v w = (L x,L v,L w) := by
  have h : fderiv ℝ (⇑L : E → F) = fun _ => L := funext (fun x => L.fderiv)
  simp [jet, second, h]

theorem jet_constant (a : F) (x v w : E) : jet (fun _ : E => a) x v w = (a,0,0) := by
  simp [jet, second]

theorem jet_tuple {n : ℕ} (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x v w : E) :
    jet (fun y i => f i y) x v w =
      (fun i => (jet (f i) x v w).1, fun i => (jet (f i) x v w).2.1,
        fun i => (jet (f i) x v w).2.2) := by
  have h (i : Fin n) := jet_comp (fun y j => f j y)
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) (contDiff_pi.mpr hf) (contDiff_apply ℝ (fun _ => ℝ) i) x v w
  simp only [jet_linear] at h
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext i
    exact (congrArg (fun p => p.2.1) (h i)).symm
  · funext i
    exact (congrArg (fun p => p.2.2) (h i)).symm

end Applications.AD.SecondOrder
