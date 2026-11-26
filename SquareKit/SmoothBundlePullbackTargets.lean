import SquareKit.SmoothBundlePullbackRealization
import SquareKit.SmoothBundleTargetMaps

/-! Target maps commute with the actual ordinary bundle pullback. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m d : ℕ} {G B E B' E' M : Type} [Group G]
  [MulAction G E] [MulAction G E'] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace E'] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space m) B'] [ChartedSpace (Space m) E'] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
  [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners m) ∞ E'] [IsManifold (modelWithCorners d) ∞ M]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (Q : Bundle (n := m) (G := G) (B := B') (E := E'))
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (k : E' → E) (hk : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ k)
  (hp : ∀ e, P.projection (k e) = f (Q.projection e))
  (ha : ∀ (g : G) e, k (g • e) = g • k e)
  (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
  (F : E → M) (hF : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ F)
  (hG : ∀ (g : G) e, F (g • e) = g • F e)

/-- A smooth equivariant map over a base map preserves the composite target. -/
def quotientArrowAlong : SheafActionQuotient.Arrow
    (Q.realizedQuotient smoothAction (F ∘ k) (hF.comp hk)
      (fun g e => by dsimp; rw [ha, hG]))
    (SheafActionQuotient.reindex (P.realizedQuotient smoothAction F hF hG)
      (ManifoldRealization.map f hf)) := by
  refine ⟨P.arrowAlong Q f hf k hk hp ha, ?_⟩
  apply (SheafActionQuotient.preserves_iff_totalMap _).mpr
  rw [SheafActionQuotient.reindex_totalMap, realizedQuotient_totalMap, realizedQuotient_totalMap]
  change SplitSheaf.totalMap (P.arrowAlong Q f hf k hk hp ha).iso.hom ≫
    SplitSheaf.lift P.realizedTorsor.family (ManifoldRealization.map f hf) ≫
      P.realizedTotalIso.hom ≫ ManifoldRealization.map F hF =
    Q.realizedTotalIso.hom ≫ ManifoldRealization.map (F ∘ k) (hF.comp hk)
  rw [← Category.assoc (SplitSheaf.lift _ _), ← Category.assoc,
    arrowAlong_total, Category.assoc, ← ManifoldRealization.map_comp]

end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m d : ℕ} {G B E B' M : Type} [Group G] [MulAction G E] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space m) B']
  [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners m) ∞ B']
  [IsManifold (modelWithCorners d) ∞ M]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
  (F : E → M) (hF : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ F)
  (hG : ∀ (g : G) e, F (g • e) = g • F e)

/-- The actual pullback with target `F ∘ snd` realizes to quotient reindexing. -/
def quotientComparison :
    letI := chartedSpace (m := m) P f hf.continuous
    letI := isManifold (m := m) P f hf.continuous
    SheafActionQuotient.Arrow
      ((bundle (m := m) P f hf.continuous).realizedQuotient smoothAction
        (F ∘ snd P f) (hF.comp (smooth_snd P f hf.continuous hf)) (fun g z => hG g (snd P f z)))
      (SheafActionQuotient.reindex (P.realizedQuotient smoothAction F hF hG)
        (ManifoldRealization.map f hf)) := by
  letI := chartedSpace (m := m) P f hf.continuous
  letI := isManifold (m := m) P f hf.continuous
  exact P.quotientArrowAlong (bundle (m := m) P f hf.continuous) f hf
    (snd P f) (smooth_snd P f hf.continuous hf)
    (fun z => (equation P f z).symm) (fun _ _ => rfl) smoothAction F hF hG


end SquareKit.SmoothPrincipalBundle.Pullback

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m d : ℕ} {G B E B' E' M : Type} [Group G]
  [MulAction G E] [MulAction G E'] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace E'] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [ChartedSpace (Space m) B'] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners n) ∞ E']
  [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners d) ∞ M]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  {F : E → M} {F' : E' → M}

/-- Ordinary pullback acts on target-preserving maps by the actual fiber-product map. -/
def targetMap (a : TargetMap P Q F F') :
    letI := chartedSpace (m := m) P f hf.continuous
    letI := chartedSpace (m := m) Q f hf.continuous
    TargetMap (bundle (m := m) P f hf.continuous) (bundle (m := m) Q f hf.continuous)
      (F ∘ snd P f) (F' ∘ snd Q f) := by
  letI := chartedSpace (m := m) P f hf.continuous
  letI := chartedSpace (m := m) Q f hf.continuous
  exact { map P f hf.continuous a.toMap with target := fun z => a.target (snd P f z) }

variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
  (hF : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ F) (hF' : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ F')
  (hG : ∀ (g : G) e, F (g • e) = g • F e) (hG' : ∀ (g : G) e, F' (g • e) = g • F' e)

/-- Naturality preserves the full quotient arrow and its target, not just its torsor. -/
theorem quotientComparison_natural (a : TargetMap P Q F F') :
    letI := chartedSpace (m := m) P f hf.continuous
    letI := isManifold (m := m) P f hf.continuous
    letI := chartedSpace (m := m) Q f hf.continuous
    letI := isManifold (m := m) Q f hf.continuous
    ((targetMap P f hf a).realizedArrow smoothAction
      (hF.comp (smooth_snd P f hf.continuous hf)) (hF'.comp (smooth_snd Q f hf.continuous hf))
      (fun g z => hG g (snd P f z)) (fun g z => hG' g (snd Q f z))).comp
        (quotientComparison Q f hf smoothAction F' hF' hG') =
      (quotientComparison P f hf smoothAction F hF hG).comp
        ((a.realizedArrow smoothAction hF hF' hG hG').reindex (ManifoldRealization.map f hf)) := by
  let := chartedSpace (m := m) P f hf.continuous
  let := isManifold (m := m) P f hf.continuous
  let := chartedSpace (m := m) Q f hf.continuous
  let := isManifold (m := m) Q f hf.continuous
  apply SheafActionQuotient.Arrow.ext
  exact realizationComparison_natural P f hf a.toMap

end SquareKit.SmoothPrincipalBundle.Pullback

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m k : ℕ} {G B E B' B'' M : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace B'']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space m) B'] [ChartedSpace (Space k) B'']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners k) ∞ B'']
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (f : B' → B) (hf : Continuous f) (g : B'' → B') (hg : Continuous g) (F : E → M)

/-- The ordinary identity comparison also preserves an arbitrary supplied target map. -/
def identityTargetMap :
    letI := chartedSpace (m := n) P (id : B → B) continuous_id
    TargetMap (bundle (m := n) P id continuous_id) P (F ∘ snd P id) F := by
  letI := chartedSpace (m := n) P (id : B → B) continuous_id
  exact { identityMap P with target := fun _ => rfl }

/-- Flattening successive actual pullbacks preserves the composite target. -/
def compositionTargetMap :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
    TargetMap (bundle (m := k) (bundle (m := m) P f hf) g hg)
      (bundle (m := k) P (f ∘ g) (hf.comp hg))
      ((F ∘ snd P f) ∘ snd (bundle (m := m) P f hf) g) (F ∘ snd P (f ∘ g)) := by
  letI := chartedSpace (m := m) P f hf
  letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
  letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
  exact { compositionMap P f hf g hg with target := fun _ => rfl }

end SquareKit.SmoothPrincipalBundle.Pullback

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n d : ℕ} {G B E M : Type} [Group G] [MulAction G E] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners d) ∞ M]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
  (F : E → M) (hF : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ F)
  (hG : ∀ (g : G) e, F (g • e) = g • F e)

theorem quotientComparison_id :
    let := chartedSpace (m := n) P (id : B → B) continuous_id
    let := isManifold (m := n) P (id : B → B) continuous_id
    (quotientComparison P id contMDiff_id smoothAction F hF hG).comp
      (SheafActionQuotient.reindexCongr (P.realizedQuotient smoothAction F hF hG)
        ManifoldRealization.map_id) =
      (identityTargetMap P F).realizedArrow smoothAction
        (hF.comp (smooth_snd P id continuous_id contMDiff_id)) hF
        (fun g z => hG g (snd P id z)) hG := by
  let := chartedSpace (m := n) P (id : B → B) continuous_id
  let := isManifold (m := n) P (id : B → B) continuous_id
  apply SheafActionQuotient.Arrow.ext
  change (realizationComparison P id contMDiff_id).comp
    (SheafActionQuotient.reindexCongr (P.realizedQuotient smoothAction F hF hG)
      ManifoldRealization.map_id).torsorArrow = (identityMap P).realizedArrow
  rw [SheafActionQuotient.reindexCongr_torsorArrow]
  exact realizationComparison_id P

end SquareKit.SmoothPrincipalBundle.Pullback

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m k d : ℕ} {G B E B' B'' M : Type} [Group G] [MulAction G E] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace B'']
  [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space m) B'] [ChartedSpace (Space k) B''] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
  [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners k) ∞ B''] [IsManifold (modelWithCorners d) ∞ M]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (g : B'' → B') (hg : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ g)
  (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
  (F : E → M) (hF : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ F)
  (hG : ∀ (g : G) e, F (g • e) = g • F e)

/-- Successive ordinary pullbacks agree with quotient reindexing, including their targets. -/
theorem quotientComparison_comp :
    let := chartedSpace (m := m) P f hf.continuous
    let := isManifold (m := m) P f hf.continuous
    let := chartedSpace (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
    let := isManifold (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
    let := chartedSpace (m := k) P (f ∘ g) (hf.comp hg).continuous
    let := isManifold (m := k) P (f ∘ g) (hf.comp hg).continuous
    ((quotientComparison (bundle (m := m) P f hf.continuous) g hg smoothAction
      (F ∘ snd P f) (hF.comp (smooth_snd P f hf.continuous hf))
      (fun a z => hG a (snd P f z))).comp
      ((quotientComparison P f hf smoothAction F hF hG).reindex (ManifoldRealization.map g hg))).comp
      (SheafActionQuotient.reindexCompositeCongr (P.realizedQuotient smoothAction F hF hG)
        (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)
        (ManifoldRealization.map (f ∘ g) (hf.comp hg))
        (ManifoldRealization.map_comp g f hg hf).symm) =
      ((compositionTargetMap (m := m) (k := k) P f hf.continuous g hg.continuous F).realizedArrow
        smoothAction
        ((hF.comp (smooth_snd P f hf.continuous hf)).comp
          (smooth_snd (bundle (m := m) P f hf.continuous) g hg.continuous hg))
        (hF.comp (smooth_snd P (f ∘ g) (hf.comp hg).continuous (hf.comp hg)))
        (fun a z => hG a (snd P f (snd (bundle (m := m) P f hf.continuous) g z)))
        (fun a z => hG a (snd P (f ∘ g) z))).comp
        (quotientComparison P (f ∘ g) (hf.comp hg) smoothAction F hF hG) := by
  let := chartedSpace (m := m) P f hf.continuous
  let := isManifold (m := m) P f hf.continuous
  let := chartedSpace (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
  let := isManifold (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
  let := chartedSpace (m := k) P (f ∘ g) (hf.comp hg).continuous
  let := isManifold (m := k) P (f ∘ g) (hf.comp hg).continuous
  apply SheafActionQuotient.Arrow.ext
  change ((realizationComparison (bundle (m := m) P f hf.continuous) g hg).comp
    ((realizationComparison P f hf).reindex (ManifoldRealization.map g hg))).comp
      (SheafActionQuotient.reindexCompositeCongr (P.realizedQuotient smoothAction F hF hG)
        (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)
        (ManifoldRealization.map (f ∘ g) (hf.comp hg))
        (ManifoldRealization.map_comp g f hg hf).symm).torsorArrow =
    (compositionMap (m := m) (k := k) P f hf.continuous g hg.continuous).realizedArrow.comp
      (realizationComparison P (f ∘ g) (hf.comp hg))
  rw [SheafActionQuotient.reindexCompositeCongr_torsorArrow]
  exact realizationComparison_comp P f hf g hg

end SquareKit.SmoothPrincipalBundle.Pullback
