import SquareKit.SmoothBundleTargetMaps
import SquareKit.SmoothBundlePullback
import SquareKit.SheafTorsorReindexMaps
/-! Ordinary bundle maps over changing bases induce cartesian sheaf maps.
The actual pullback manifold realizes to this reindexing, with all projections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m : ℕ} {G B E B' E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space m) B'] [ChartedSpace (Space m) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
  [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners m) ∞ E']
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (Q : Bundle (n := m) (G := G) (B := B') (E := E'))
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (k : E' → E) (hk : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ k)
  (hp : ∀ e, P.projection (k e) = f (Q.projection e))
  (ha : ∀ (g : G) e, k (g • e) = g • k e)

def totalAlong : SplitSheaf.extension Q.realizedTorsor.family ⟶ SplitSheaf.extension P.realizedTorsor.family :=
  Q.realizedTotalIso.hom ≫ ManifoldRealization.map k hk ≫ P.realizedTotalIso.inv

include hp in
theorem totalAlong_projection :
    P.totalAlong Q k hk ≫ SplitSheaf.p P.realizedTorsor.family =
      SplitSheaf.p Q.realizedTorsor.family ≫ ManifoldRealization.map f hf := by
  rw [← P.realizedTotalIso_projection, ← Q.realizedTotalIso_projection]
  simp only [totalAlong, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← ManifoldRealization.map_comp k P.projection hk P.smooth_projection,
    ← ManifoldRealization.map_comp Q.projection f Q.smooth_projection hf]
  have he : P.projection ∘ k = f ∘ Q.projection := funext hp
  simp only [he]

def fiberAlong : Q.realizedTorsor.family.family ⟶
    (SplitSheaf.tySub P.realizedTorsor.family (ManifoldRealization.map f hf)).family := SplitSheaf.mapAlong (ManifoldRealization.map f hf) (P.totalAlong Q k hk)
  (P.totalAlong_projection Q f hf k hk hp)

theorem fiberAlong_value (x : (object m B').obj.Elements) (p : Q.realizedTorsor.family.family.obj x) :
    P.realizedTotalIso.hom.hom.app x.obj
      ⟨(ManifoldRealization.map f hf).hom.app x.obj x.val,
        (P.fiberAlong Q f hf k hk hp).app x p⟩ =
      (ManifoldRealization.map k hk).hom.app x.obj
        (Q.realizedTotalIso.hom.hom.app x.obj ⟨x.val,p⟩) := by
  apply SplitSheaf.mapAlong_value_of_comp
  simp [totalAlong]

include ha in
theorem fiberAlong_equivariant (x : (object m B').obj.Elements)
    (g : (locallyConstantGroup G).obj.obj x.obj) (p : Q.realizedTorsor.family.family.obj x) :
    (P.fiberAlong Q f hf k hk hp).app x (Q.realizedTorsor.act x g p) =
      (SheafTorsor.reindex P.realizedTorsor (ManifoldRealization.map f hf)).act x g
        ((P.fiberAlong Q f hf k hk hp).app x p) := by
  have hinj := ((CategoryTheory.isIso_iff_bijective
    (P.realizedTotalIso.hom.hom.app x.obj)).mp inferInstance).injective
  let y := (ManifoldRealization.map f hf).hom.mapElements.obj x
  have he : P.realizedTotalIso.hom.hom.app x.obj
      ⟨y.val, (P.fiberAlong Q f hf k hk hp).app x (Q.realizedTorsor.act x g p)⟩ =
      P.realizedTotalIso.hom.hom.app x.obj
      ⟨y.val, P.realizedTorsor.act y g ((P.fiberAlong Q f hf k hk hp).app x p)⟩ := by
    apply (P.fiberAlong_value Q f hf k hk hp x (Q.realizedTorsor.act x g p)).trans
    apply Eq.trans _ (P.realizedTotalIso_equivariant y g
      ((P.fiberAlong Q f hf k hk hp).app x p)).symm
    rw [Q.realizedTotalIso_equivariant]
    have hv := P.fiberAlong_value Q f hf k hk hp x p
    apply Eq.trans _ (congrArg ((representation P.smooth_action).act x.obj g) hv).symm
    apply SmoothConstantAction.Representation.intertwines
    exact fun a => Q.target_intertwines P.smooth_action k hk ha a
  exact eq_of_heq (Sigma.mk.inj_iff.mp (hinj he)).2

/-- Any equivariant smooth bundle map over a smooth base map gives the full
reindexing isomorphism; its inverse follows from principality. -/
def arrowAlong : SheafTorsor.Arrow Q.realizedTorsor
    (SheafTorsor.reindex P.realizedTorsor (ManifoldRealization.map f hf)) :=
  SheafTorsor.EquivariantMap.toArrow {
    hom := P.fiberAlong Q f hf k hk hp
    equivariant := P.fiberAlong_equivariant Q f hf k hk hp ha }

end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m : ℕ} {G B E B' E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space m) B'] [ChartedSpace (Space m) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
  [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners m) ∞ E']
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (Q : Bundle (n := m) (G := G) (B := B') (E := E'))
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (k : E' → E) (hk : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ k)
  (hp : ∀ e, P.projection (k e) = f (Q.projection e))
  (ha : ∀ (g : G) e, k (g • e) = g • k e)

theorem arrowAlong_total :
    SplitSheaf.totalMap (P.arrowAlong Q f hf k hk hp ha).iso.hom ≫
      SplitSheaf.lift P.realizedTorsor.family (ManifoldRealization.map f hf) ≫
      P.realizedTotalIso.hom = Q.realizedTotalIso.hom ≫ ManifoldRealization.map k hk := by
  change SplitSheaf.totalMap (P.fiberAlong Q f hf k hk hp) ≫ _ ≫ _ = _
  rw [← Category.assoc, fiberAlong, SplitSheaf.mapAlong_total]
  simp [totalAlong]

include hp ha in
/-- An equivariant map between principal bundles is cartesian after realization,
including when the two bases have different dimensions. -/
theorem arrowAlong_isPullback :
    IsPullback (ManifoldRealization.map k hk) (ManifoldRealization.map Q.projection Q.smooth_projection)
      (ManifoldRealization.map P.projection P.smooth_projection) (ManifoldRealization.map f hf) := by
  let a := P.arrowAlong Q f hf k hk hp ha
  let e := SplitSheaf.totalIso a.iso
  apply (SplitSheaf.extension_pullback P.realizedTorsor.family (ManifoldRealization.map f hf)).of_iso
    (e.symm ≪≫ Q.realizedTotalIso) P.realizedTotalIso (Iso.refl _) (Iso.refl _)
  · apply (cancel_epi e.hom).mp
    change e.hom ≫ SplitSheaf.lift P.realizedTorsor.family (ManifoldRealization.map f hf) ≫
      P.realizedTotalIso.hom = e.hom ≫ (e.inv ≫ Q.realizedTotalIso.hom) ≫ ManifoldRealization.map k hk
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact P.arrowAlong_total Q f hf k hk hp ha
  · apply (cancel_epi e.hom).mp
    change e.hom ≫ SplitSheaf.p (SplitSheaf.tySub P.realizedTorsor.family (ManifoldRealization.map f hf)) ≫ 𝟙 _ =
      e.hom ≫ (e.inv ≫ Q.realizedTotalIso.hom) ≫ ManifoldRealization.map Q.projection Q.smooth_projection
    rw [Category.comp_id, ← Category.assoc, Iso.hom_inv_id_assoc,
      Q.realizedTotalIso_projection]
    exact SplitSheaf.totalMap_projection a.iso.hom
  · simpa using P.realizedTotalIso_projection.symm
  · simp

end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m : ℕ} {G B E B' : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space m) B']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners m) ∞ B']
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)

/-- The actual sheet-constructed ordinary pullback realizes to torsor reindexing. -/
def realizationComparison :
    let := chartedSpace (m := m) P f hf.continuous
    let := isManifold (m := m) P f hf.continuous
    SheafTorsor.Arrow (bundle (m := m) P f hf.continuous).realizedTorsor
      (SheafTorsor.reindex P.realizedTorsor (ManifoldRealization.map f hf)) := by
  let := chartedSpace (m := m) P f hf.continuous
  let := isManifold (m := m) P f hf.continuous
  exact P.arrowAlong (bundle (m := m) P f hf.continuous) f hf (snd P f)
    (smooth_snd P f hf.continuous hf) (fun z => (equation P f z).symm) (fun _ _ => rfl)

/-- Realization preserves this actual pullback square, with its specified projections.
This is the discrete principal-bundle case, with no transversality assumption. -/
theorem realization_isPullback :
    let := chartedSpace (m := m) P f hf.continuous
    let := isManifold (m := m) P f hf.continuous
    IsPullback (ManifoldRealization.map (snd P f) (smooth_snd P f hf.continuous hf))
      (ManifoldRealization.map (fst P f) (smooth_fst P f hf.continuous))
      (ManifoldRealization.map P.projection P.smooth_projection) (ManifoldRealization.map f hf) := by
  let := chartedSpace (m := m) P f hf.continuous
  let := isManifold (m := m) P f hf.continuous
  exact P.arrowAlong_isPullback (bundle (m := m) P f hf.continuous) f hf (snd P f)
    (smooth_snd P f hf.continuous hf) (fun z => (equation P f z).symm) (fun _ _ => rfl)

end SquareKit.SmoothPrincipalBundle.Pullback

namespace SquareKit.SmoothPrincipalBundle.Map
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners n) ∞ E']
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')} (a : Map P Q)

theorem realizedArrow_display :
    SplitSheaf.totalMap a.realizedArrow.iso.hom ≫ Q.realizedTotalIso.hom =
      P.realizedTotalIso.hom ≫ ManifoldRealization.map a.toFun a.smooth := by
  change SplitSheaf.totalMap a.realizedFiberMap ≫ _ = _
  rw [a.realizedFiberMap_total]
  simp [realizedTotalMap]

end SquareKit.SmoothPrincipalBundle.Map

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m : ℕ} {G B E B' E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [ChartedSpace (Space m) B']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners n) ∞ E']
  [IsManifold (modelWithCorners m) ∞ B']
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)

theorem realizationComparison_total :
    let := chartedSpace (m := m) P f hf.continuous
    let := isManifold (m := m) P f hf.continuous
    SplitSheaf.totalMap (realizationComparison P f hf).iso.hom ≫
      SplitSheaf.lift P.realizedTorsor.family (ManifoldRealization.map f hf) ≫ P.realizedTotalIso.hom =
      (bundle (m := m) P f hf.continuous).realizedTotalIso.hom ≫
        ManifoldRealization.map (snd P f) (smooth_snd P f hf.continuous hf) := by
  let := chartedSpace (m := m) P f hf.continuous
  let := isManifold (m := m) P f hf.continuous
  exact P.arrowAlong_total (bundle (m := m) P f hf.continuous) f hf (snd P f)
    (smooth_snd P f hf.continuous hf) (fun z => (equation P f z).symm) (fun _ _ => rfl)

variable {Q : Bundle (n := n) (G := G) (B := B) (E := E')}

/-- Realization of ordinary pullback commutes with every equivariant bundle map. -/
theorem realizationComparison_natural (a : Map P Q) :
    let := chartedSpace (m := m) P f hf.continuous
    let := isManifold (m := m) P f hf.continuous
    let := chartedSpace (m := m) Q f hf.continuous
    let := isManifold (m := m) Q f hf.continuous
    ((map P f hf.continuous a).realizedArrow).comp (realizationComparison Q f hf) =
      (realizationComparison P f hf).comp (a.realizedArrow.reindex (ManifoldRealization.map f hf)) := by
  let := chartedSpace (m := m) P f hf.continuous
  let := isManifold (m := m) P f hf.continuous
  let := chartedSpace (m := m) Q f hf.continuous
  let := isManifold (m := m) Q f hf.continuous
  apply SheafTorsor.Arrow.ext
  apply SplitSheaf.reindex_map_ext
  apply (cancel_mono Q.realizedTotalIso.hom).mp
  change (SplitSheaf.totalMap ((map P f hf.continuous a).realizedArrow.iso.hom ≫
      (realizationComparison Q f hf).iso.hom) ≫ _) ≫ _ =
    (SplitSheaf.totalMap ((realizationComparison P f hf).iso.hom ≫
      (a.realizedArrow.reindex (ManifoldRealization.map f hf)).iso.hom) ≫ _) ≫ _
  rw [SplitSheaf.totalMap_comp, SplitSheaf.totalMap_comp]
  simp only [Category.assoc]
  rw [realizationComparison_total, ← Category.assoc, Map.realizedArrow_display]
  have hr : SplitSheaf.totalMap (a.realizedArrow.reindex (ManifoldRealization.map f hf)).iso.hom ≫
      SplitSheaf.lift Q.realizedTorsor.family (ManifoldRealization.map f hf) =
      SplitSheaf.lift P.realizedTorsor.family (ManifoldRealization.map f hf) ≫
        SplitSheaf.totalMap a.realizedArrow.iso.hom :=
    SplitSheaf.totalMap_reindex_lift a.realizedArrow.iso.hom (ManifoldRealization.map f hf)
  rw [← Category.assoc (SplitSheaf.totalMap (a.realizedArrow.reindex (ManifoldRealization.map f hf)).iso.hom), hr]
  simp only [Category.assoc]
  rw [Map.realizedArrow_display]
  have htot := congrArg (fun t => t ≫ ManifoldRealization.map a.toFun a.smooth)
    (realizationComparison_total P f hf)
  simp only [Category.assoc] at htot
  rw [htot]
  rw [← ManifoldRealization.map_comp (map P f hf.continuous a).toFun (snd Q f)
      (map P f hf.continuous a).smooth (smooth_snd Q f hf.continuous hf),
    ← ManifoldRealization.map_comp (snd P f) a.toFun (smooth_snd P f hf.continuous hf) a.smooth]
  rfl

end SquareKit.SmoothPrincipalBundle.Pullback

namespace SquareKit.SmoothPrincipalBundle.Pullback
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
theorem realizationComparison_id :
    let := chartedSpace (m := n) P (id : B → B) continuous_id
    let := isManifold (m := n) P (id : B → B) continuous_id
    (realizationComparison P id contMDiff_id).comp
      (SheafTorsor.reindexCongr P.realizedTorsor ManifoldRealization.map_id) =
      (identityMap P).realizedArrow := by
  let := chartedSpace (m := n) P (id : B → B) continuous_id
  let := isManifold (m := n) P (id : B → B) continuous_id
  apply SheafTorsor.Arrow.ext
  apply SplitSheaf.totalMap_injective
  apply (cancel_mono P.realizedTotalIso.hom).mp
  change SplitSheaf.totalMap ((realizationComparison P id contMDiff_id).iso.hom ≫
    (SheafTorsor.reindexCongr P.realizedTorsor ManifoldRealization.map_id).iso.hom) ≫ _ = _
  rw [SplitSheaf.totalMap_comp]
  have ht := SheafTorsor.reindexCongr_lift P.realizedTorsor ManifoldRealization.map_id
  change SplitSheaf.totalMap (SheafTorsor.reindexCongr P.realizedTorsor ManifoldRealization.map_id).iso.hom = _ at ht
  rw [Category.assoc, ht, realizationComparison_total, Map.realizedArrow_display]
  rfl
variable {m k : ℕ} {B' B'' : Type} [TopologicalSpace B'] [TopologicalSpace B'']
  [ChartedSpace (Space m) B'] [ChartedSpace (Space k) B'']
  [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners k) ∞ B'']
  (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (g : B'' → B') (hg : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ g)
theorem realizationComparison_comp :
    let := chartedSpace (m := m) P f hf.continuous
    let := isManifold (m := m) P f hf.continuous
    let := chartedSpace (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
    let := isManifold (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
    let := chartedSpace (m := k) P (f ∘ g) (hf.comp hg).continuous
    let := isManifold (m := k) P (f ∘ g) (hf.comp hg).continuous
    ((realizationComparison (bundle (m := m) P f hf.continuous) g hg).comp
      ((realizationComparison P f hf).reindex (ManifoldRealization.map g hg))).comp
      (SheafTorsor.reindexCompositeCongr P.realizedTorsor
        (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)
        (ManifoldRealization.map (f ∘ g) (hf.comp hg))
        (ManifoldRealization.map_comp g f hg hf).symm) =
    (compositionMap (m := m) (k := k) P f hf.continuous g hg.continuous).realizedArrow.comp
      (realizationComparison P (f ∘ g) (hf.comp hg)) := by
  let := chartedSpace (m := m) P f hf.continuous
  let := isManifold (m := m) P f hf.continuous
  let := chartedSpace (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
  let := isManifold (m := k) (bundle (m := m) P f hf.continuous) g hg.continuous
  let := chartedSpace (m := k) P (f ∘ g) (hf.comp hg).continuous
  let := isManifold (m := k) P (f ∘ g) (hf.comp hg).continuous
  apply SheafTorsor.Arrow.ext
  apply SplitSheaf.reindex_map_ext
  apply (cancel_mono P.realizedTotalIso.hom).mp
  rw [SheafTorsor.reindexCompositeCongr_comp_total]
  change _ = (SplitSheaf.totalMap
    ((compositionMap (m := m) (k := k) P f hf.continuous g hg.continuous).realizedArrow.iso.hom ≫
      (realizationComparison P (f ∘ g) (hf.comp hg)).iso.hom) ≫ _) ≫ _
  rw [SplitSheaf.totalMap_comp]
  simp only [Category.assoc]
  rw [realizationComparison_total]
  have ht := congrArg (fun t => t ≫
    ManifoldRealization.map (snd P f) (smooth_snd P f hf.continuous hf))
    (realizationComparison_total (bundle (m := m) P f hf.continuous) g hg)
  simp only [Category.assoc] at ht
  rw [ht, realizationComparison_total,
    ← Category.assoc (SplitSheaf.totalMap
      (compositionMap (m := m) (k := k) P f hf.continuous g hg.continuous).realizedArrow.iso.hom),
    Map.realizedArrow_display]
  simp only [Category.assoc]
  rw [← ManifoldRealization.map_comp, ← ManifoldRealization.map_comp]
  rfl
end SquareKit.SmoothPrincipalBundle.Pullback
