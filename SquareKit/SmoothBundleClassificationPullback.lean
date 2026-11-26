import SquareKit.SmoothBundleClassification
import SquareKit.SmoothBundlePullbackRealization

/-! Ordinary base change and its natural comparison with sheaf restriction. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothPrincipalBundle.Ordinary
open CategoryTheory ManifoldRealization SmoothOpenSite
open scoped Manifold ContDiff
variable {n m k : ℕ} {G B B' B'' : Type} [Group G]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
  [TopologicalSpace B'] [ChartedSpace (Space m) B'] [IsManifold (modelWithCorners m) ∞ B']
  [TopologicalSpace B''] [ChartedSpace (Space k) B''] [IsManifold (modelWithCorners k) ∞ B'']

/-- The total space is the actual equality subtype, with the sheet-derived atlas. -/
def pulledBack (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (P : Ordinary n G B) : Ordinary m G B' := by
  letI := Pullback.chartedSpace (m := m) P.bundle f hf.continuous
  letI := Pullback.isManifold (m := m) P.bundle f hf.continuous
  exact ofBundle (Pullback.bundle (m := m) P.bundle f hf.continuous)

set_option backward.isDefEq.respectTransparency false in
def pullbackFunctor (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f) :
    Ordinary n G B ⥤ Ordinary m G B' where
  obj := pulledBack f hf
  map {P _Q} a := Pullback.map P.bundle f hf.continuous a
  map_id P := Pullback.map_ident P.bundle f hf.continuous
  map_comp a b := Pullback.map_comp _ f hf.continuous a b

set_option backward.isDefEq.respectTransparency false in
def pullbackRealization (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f) :
    pullbackFunctor (G := G) f hf ⋙ realization ≅
      realization ⋙ SheafTorsor.restriction (ManifoldRealization.map f hf) :=
  NatIso.ofComponents (fun P => (Pullback.realizationComparison P.bundle f hf).toIso)
    (by intro P Q a; exact Pullback.realizationComparison_natural P.bundle f hf a)

set_option backward.isDefEq.respectTransparency false in
def pullbackIdentityComponent (P : Ordinary n G B) :
    pulledBack (id : B → B) contMDiff_id P ≅ P where
  hom := Pullback.identityMap P.bundle
  inv := Pullback.identityInverseMap P.bundle
  hom_inv_id := Pullback.identityMap_inverse P.bundle
  inv_hom_id := Pullback.identityInverseMap_inverse P.bundle

set_option backward.isDefEq.respectTransparency false in
def pullbackIdentity : pullbackFunctor (n := n) (m := n) (G := G) (id : B → B) contMDiff_id ≅ 𝟭 _ :=
  NatIso.ofComponents pullbackIdentityComponent (by
    intro P Q a
    exact (Pullback.identityMap_natural P.bundle a).symm)

set_option backward.isDefEq.respectTransparency false in
def pullbackCompositionComponent (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (g : B'' → B') (hg : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ g) (P : Ordinary n G B) :
    pulledBack g hg (pulledBack f hf P) ≅ pulledBack (f ∘ g) (hf.comp hg) P where
  hom := Pullback.compositionMap P.bundle f hf.continuous g hg.continuous
  inv := Pullback.compositionInverseMap P.bundle f hf.continuous g hg.continuous
  hom_inv_id := Pullback.compositionMap_inverse P.bundle f hf.continuous g hg.continuous
  inv_hom_id := Pullback.compositionInverseMap_inverse P.bundle f hf.continuous g hg.continuous

set_option backward.isDefEq.respectTransparency false in
def pullbackComposition (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (g : B'' → B') (hg : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ g) :
    pullbackFunctor (G := G) f hf ⋙ pullbackFunctor (n := m) (m := k) g hg ≅
      pullbackFunctor (n := n) (m := k) (f ∘ g) (hf.comp hg) :=
  NatIso.ofComponents (pullbackCompositionComponent f hf g hg) (by
    intro P Q a
    exact (Pullback.compositionMap_natural P.bundle f hf.continuous g hg.continuous a).symm)

set_option backward.isDefEq.respectTransparency false in
theorem pullbackRealization_id (P : Ordinary n G B) :
    (pullbackRealization (id : B → B) contMDiff_id).hom.app P ≫
      SheafTorsor.reindexCongr (realization.obj P) ManifoldRealization.map_id =
      realization.map (pullbackIdentityComponent P).hom :=
  Pullback.realizationComparison_id P.bundle

set_option backward.isDefEq.respectTransparency false in
theorem pullbackRealization_comp (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (g : B'' → B') (hg : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ g) (P : Ordinary n G B) :
    (pullbackRealization g hg).hom.app (pulledBack f hf P) ≫
      (SheafTorsor.restriction (ManifoldRealization.map g hg)).map
        ((pullbackRealization f hf).hom.app P) ≫
      SheafTorsor.reindexCompositeCongr (realization.obj P)
        (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)
        (ManifoldRealization.map (f ∘ g) (hf.comp hg))
        (ManifoldRealization.map_comp g f hg hf).symm =
      realization.map (pullbackCompositionComponent f hf g hg P).hom ≫
        (pullbackRealization (f ∘ g) (hf.comp hg)).hom.app P := by
  rw [← Category.assoc]
  exact Pullback.realizationComparison_comp P.bundle f hf g hg

/-- The pulled back chosen total manifold realizes the restricted original torsor. -/
def pulledBackRecovery (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (P : Torsors (n := n) (G := G) (B := B)) :
    realization.obj (pulledBack f hf (reconstructed P)) ≅
      (SheafTorsor.restriction (ManifoldRealization.map f hf)).obj P :=
  (pullbackRealization f hf).app (reconstructed P) ≪≫
    (SheafTorsor.restriction (ManifoldRealization.map f hf)).mapIso (recovery P)

/-- Reconstruction after restriction agrees by an ordinary smooth bundle isomorphism
with the actual pullback of the chosen reconstruction. -/
def reconstructionPullbackComponent (f : B' → B)
    (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (P : Torsors (n := n) (G := G) (B := B)) :
    reconstructed ((SheafTorsor.restriction (ManifoldRealization.map f hf)).obj P) ≅
      pulledBack f hf (reconstructed P) :=
  recoveryComparison _ _ (pulledBackRecovery f hf P)

@[simp] theorem realization_reconstructionPullbackComponent (f : B' → B)
    (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (P : Torsors (n := n) (G := G) (B := B)) :
    realization.map (reconstructionPullbackComponent f hf P).hom =
      (recovery ((SheafTorsor.restriction (ManifoldRealization.map f hf)).obj P)).hom ≫
        (pulledBackRecovery f hf P).inv :=
  realization_recoveryComparison _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem pulledBackRecovery_natural (f : B' → B)
    (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    {P Q : Torsors (n := n) (G := G) (B := B)} (a : P ⟶ Q) :
    realization.map ((pullbackFunctor f hf).map (reconstruction.map a)) ≫
      (pulledBackRecovery f hf Q).hom =
    (pulledBackRecovery f hf P).hom ≫
      (SheafTorsor.restriction (ManifoldRealization.map f hf)).map a := by
  let H := SheafTorsor.restriction (G := locallyConstantGroup G) (ManifoldRealization.map f hf)
  change realization.map ((pullbackFunctor f hf).map (reconstruction.map a)) ≫
    (pullbackRealization f hf).hom.app (reconstructed Q) ≫ H.map (recovery Q).hom =
    ((pullbackRealization f hf).hom.app (reconstructed P) ≫ H.map (recovery P).hom) ≫ H.map a
  rw [← Category.assoc]
  have hn := (pullbackRealization f hf).hom.naturality (reconstruction.map a)
  change realization.map ((pullbackFunctor f hf).map (reconstruction.map a)) ≫
    (pullbackRealization f hf).hom.app (reconstructed Q) =
    (pullbackRealization f hf).hom.app (reconstructed P) ≫
      H.map (realization.map (reconstruction.map a)) at hn
  rw [hn]
  rw [Category.assoc, ← H.map_comp, realization_reconstruction_map]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
def reconstructionPullback (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f) :
    SheafTorsor.restriction (G := locallyConstantGroup G) (ManifoldRealization.map f hf) ⋙
      reconstruction ≅ reconstruction ⋙ pullbackFunctor f hf :=
  NatIso.ofComponents (reconstructionPullbackComponent f hf) (by
    intro P Q a
    apply realization.map_injective
    simp only [Functor.map_comp, Functor.comp_map, realization_reconstructionPullbackComponent,
      realization_reconstruction_map]
    apply (cancel_mono (pulledBackRecovery f hf Q).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pulledBackRecovery_natural f hf a]
    simp)

end SquareKit.SmoothPrincipalBundle.Ordinary
