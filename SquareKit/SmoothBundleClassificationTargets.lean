import SquareKit.SmoothBundleClassificationPullback
import SquareKit.SmoothTorsorReconstructionTargets
import SquareKit.SmoothBundlePullbackTargets

/-! Classification with an independent manifold-valued equivariant target. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothPrincipalBundle.Ordinary
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n d : ℕ} {G B M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace B] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners d) ∞ M]

/-- A smooth equivariant target on an independently supplied ordinary bundle. -/
structure WithTarget (n d : ℕ) (G B M : Type) [Group G] [MulAction G M]
    [TopologicalSpace B] [TopologicalSpace M]
    [ChartedSpace (Space n) B] [ChartedSpace (Space d) M] where
  ordinary : Ordinary n G B
  target : ordinary.Total → M
  smooth : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ target
  equivariant : ∀ (g : G) x, target (g • x) = g • target x

namespace WithTarget
instance : Category.{0} (WithTarget n d G B M) where
  Hom P Q := TargetMap P.ordinary.bundle Q.ordinary.bundle P.target Q.target
  id P := TargetMap.ident P.ordinary.bundle P.target
  comp f g := f.comp g
  id_comp f := TargetMap.ext _ _ (Map.ident_comp f.toMap)
  comp_id f := TargetMap.ext _ _ (Map.comp_ident f.toMap)
  assoc _ _ _ := rfl

instance : Groupoid (WithTarget n d G B M) where
  inv f := f.inverse
  inv_comp f := f.inverse_comp
  comp_inv f := f.comp_inverse

def forget : WithTarget n d G B M ⥤ Ordinary n G B where
  obj P := P.ordinary
  map f := f.toMap

variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
abbrev Quotients := SheafActionQuotient.Object (representation smoothAction).action (object n B)

def realization : WithTarget n d G B M ⥤ Quotients (n := n) (B := B) smoothAction where
  obj P := P.ordinary.bundle.realizedQuotient smoothAction P.target P.smooth P.equivariant
  map {P Q} f := f.realizedArrow smoothAction P.smooth Q.smooth P.equivariant Q.equivariant
  map_id P := TargetMap.realizedArrow_ident smoothAction P.smooth P.equivariant
  map_comp {P Q R} f g :=
    TargetMap.realizedArrow_comp smoothAction P.smooth Q.smooth P.equivariant Q.equivariant
      f R.smooth R.equivariant g

def realizationFullyFaithful : (realization (n := n) (B := B) smoothAction).FullyFaithful where
  preimage {P Q} h := (targetMapEquiv smoothAction P.smooth Q.smooth P.equivariant Q.equivariant).symm h
  map_preimage {P Q} h :=
    (targetMapEquiv smoothAction P.smooth Q.smooth P.equivariant Q.equivariant).apply_symm_apply h
  preimage_map {P Q} f :=
    (targetMapEquiv smoothAction P.smooth Q.smooth P.equivariant Q.equivariant).symm_apply_apply f

instance : (realization (n := n) (B := B) smoothAction).Full :=
  (realizationFullyFaithful smoothAction).full
instance : (realization (n := n) (B := B) smoothAction).Faithful :=
  (realizationFullyFaithful smoothAction).faithful

def reconstructed (R : Quotients (n := n) (B := B) smoothAction) : WithTarget n d G B M where
  ordinary := Ordinary.reconstructed R.torsor
  target := SmoothTorsorReconstruction.reconstructedTarget smoothAction R
  smooth := SmoothTorsorReconstruction.reconstructedTarget_smooth smoothAction R
  equivariant := SmoothTorsorReconstruction.reconstructedTarget_equivariant smoothAction R

def recovery (R : Quotients (n := n) (B := B) smoothAction) :
    (realization smoothAction).obj (reconstructed smoothAction R) ≅ R :=
  (SmoothTorsorReconstruction.reconstructedQuotientArrow smoothAction R).toIso

def reconstruction : Quotients (n := n) (B := B) smoothAction ⥤ WithTarget n d G B M where
  obj := reconstructed smoothAction
  map {P Q} h := (realization smoothAction).preimage
    ((recovery smoothAction P).hom ≫ h ≫ (recovery smoothAction Q).inv)
  map_id P := by apply (realization smoothAction).map_injective; simp
  map_comp h k := by apply (realization smoothAction).map_injective; simp [Category.assoc]

@[simp] theorem realization_reconstruction_map
    {P Q : Quotients (n := n) (B := B) smoothAction} (h : P ⟶ Q) :
    (realization smoothAction).map ((reconstruction smoothAction).map h) =
      (recovery smoothAction P).hom ≫ h ≫ (recovery smoothAction Q).inv :=
  Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
def counit : reconstruction (n := n) (B := B) smoothAction ⋙ realization smoothAction ≅ 𝟭 _ :=
  NatIso.ofComponents (recovery smoothAction) (by intro P Q h; simp [Category.assoc])

def unitComponent (P : WithTarget n d G B M) :
    P ≅ (reconstruction smoothAction).obj ((realization smoothAction).obj P) :=
  (realization smoothAction).preimageIso (recovery smoothAction ((realization smoothAction).obj P)).symm

@[simp] theorem realization_unitComponent (P : WithTarget n d G B M) :
    (realization smoothAction).map (unitComponent smoothAction P).hom =
      (recovery smoothAction ((realization smoothAction).obj P)).inv :=
  Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
def unit : 𝟭 (WithTarget n d G B M) ≅ realization smoothAction ⋙ reconstruction smoothAction :=
  NatIso.ofComponents (unitComponent smoothAction) (by
    intro P Q h
    apply (realization smoothAction).map_injective
    simp)

set_option backward.isDefEq.respectTransparency false in
/-- All target-preserving maps are retained, with an explicitly recovered target. -/
def classification : WithTarget n d G B M ≌ Quotients (n := n) (B := B) smoothAction where
  functor := realization smoothAction
  inverse := reconstruction smoothAction
  unitIso := unit smoothAction
  counitIso := counit smoothAction
  functor_unitIso_comp P := by
    change (realization smoothAction).map (unitComponent smoothAction P).hom ≫
      (recovery smoothAction ((realization smoothAction).obj P)).hom = _
    simp

theorem reconstructed_target_map (R : Quotients (n := n) (B := B) smoothAction) :
    ManifoldRealization.map (reconstructed smoothAction R).target (reconstructed smoothAction R).smooth =
      (Ordinary.totalRecovery R.torsor).hom ≫ R.totalMap :=
  SmoothTorsorReconstruction.reconstructedTarget_map smoothAction R

/-- Forgetting the target commutes with realization on objects and every arrow. -/
theorem realization_forget :
    realization (n := n) (B := B) smoothAction ⋙ SheafActionQuotient.forget =
      forget ⋙ Ordinary.realization := rfl

theorem reconstruction_forget_map {P Q : Quotients (n := n) (B := B) smoothAction}
    (h : P ⟶ Q) :
    ((reconstruction smoothAction).map h).toMap =
      Ordinary.reconstruction.map h.torsorArrow := by
  apply Ordinary.realization.map_injective
  have he := congrArg SheafActionQuotient.Arrow.torsorArrow
    (realization_reconstruction_map smoothAction h)
  exact he.trans (Ordinary.realization_reconstruction_map h.torsorArrow).symm

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the target preserves the specified reconstruction functor. -/
def reconstructionForget :
    reconstruction (n := n) (B := B) smoothAction ⋙ forget ≅
      SheafActionQuotient.forget ⋙ Ordinary.reconstruction :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro P Q h
    change ((reconstruction smoothAction).map h).toMap ≫ 𝟙 _ =
      𝟙 _ ≫ Ordinary.reconstruction.map h.torsorArrow
    rw [Category.comp_id, Category.id_comp]
    exact reconstruction_forget_map smoothAction h)

@[simp] theorem recovery_forget (R : Quotients (n := n) (B := B) smoothAction) :
    SheafActionQuotient.forget.map (recovery smoothAction R).hom =
      (Ordinary.recovery R.torsor).hom := rfl

/-- Underlying total-space function of the target-preserving unit. -/
def unitTotal (P : WithTarget n d G B M) :
    P.ordinary.Total → (reconstructed smoothAction ((realization smoothAction).obj P)).ordinary.Total :=
  (unitComponent smoothAction P).hom.toFun

/-- The target on the recovered total manifold intertwines the ordinary unit. -/
theorem unit_target (P : WithTarget n d G B M) (x : P.ordinary.Total) :
    (reconstructed smoothAction ((realization smoothAction).obj P)).target
        (unitTotal smoothAction P x) = P.target x :=
  (unitComponent smoothAction P).hom.target x

variable {m k : ℕ} {B' B'' : Type}
  [TopologicalSpace B'] [ChartedSpace (Space m) B'] [IsManifold (modelWithCorners m) ∞ B']
  [TopologicalSpace B''] [ChartedSpace (Space k) B''] [IsManifold (modelWithCorners k) ∞ B'']

/-- The target on the actual fiber product is composition with its second projection. -/
def pulledBack (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (P : WithTarget n d G B M) : WithTarget m d G B' M where
  ordinary := Ordinary.pulledBack f hf P.ordinary
  target := P.target ∘ Pullback.snd P.ordinary.bundle f
  smooth := P.smooth.comp (Pullback.smooth_snd P.ordinary.bundle f hf.continuous hf)
  equivariant g z := P.equivariant g (Pullback.snd P.ordinary.bundle f z)

set_option backward.isDefEq.respectTransparency false in
def pullbackFunctor (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f) :
    WithTarget n d G B M ⥤ WithTarget m d G B' M where
  obj := pulledBack f hf
  map {P _Q} a := Pullback.targetMap P.ordinary.bundle f hf a
  map_id P := by
    let := Pullback.chartedSpace (m := m) P.ordinary.bundle f hf.continuous
    exact TargetMap.ext _ _ (Pullback.map_ident P.ordinary.bundle f hf.continuous)
  map_comp {P Q R} a b := by
    let := Pullback.chartedSpace (m := m) P.ordinary.bundle f hf.continuous
    let := Pullback.chartedSpace (m := m) Q.ordinary.bundle f hf.continuous
    let := Pullback.chartedSpace (m := m) R.ordinary.bundle f hf.continuous
    exact TargetMap.ext _ _ (Pullback.map_comp _ f hf.continuous a.toMap b.toMap)

set_option backward.isDefEq.respectTransparency false in
def pullbackRealization (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f) :
    pullbackFunctor (G := G) (M := M) f hf ⋙ realization smoothAction ≅
      realization smoothAction ⋙ SheafActionQuotient.restriction (ManifoldRealization.map f hf) :=
  NatIso.ofComponents (fun P =>
    (Pullback.quotientComparison P.ordinary.bundle f hf smoothAction P.target P.smooth P.equivariant).toIso)
    (by intro P Q a
        exact Pullback.quotientComparison_natural P.ordinary.bundle f hf smoothAction
          P.smooth Q.smooth P.equivariant Q.equivariant a)

set_option backward.isDefEq.respectTransparency false in
def pullbackIdentityComponent (P : WithTarget n d G B M) :
    pulledBack (id : B → B) contMDiff_id P ≅ P where
  hom := Pullback.identityTargetMap P.ordinary.bundle P.target
  inv := { (Ordinary.pullbackIdentityComponent P.ordinary).inv with target := fun _ => rfl }
  hom_inv_id := by
    let := (Ordinary.pulledBack (id : B → B) contMDiff_id P.ordinary).charts
    exact TargetMap.ext _ _ (Ordinary.pullbackIdentityComponent P.ordinary).hom_inv_id
  inv_hom_id := TargetMap.ext _ _ (Ordinary.pullbackIdentityComponent P.ordinary).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
def pullbackCompositionComponent (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (g : B'' → B') (hg : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ g) (P : WithTarget n d G B M) :
    pulledBack g hg (pulledBack f hf P) ≅ pulledBack (f ∘ g) (hf.comp hg) P where
  hom := Pullback.compositionTargetMap P.ordinary.bundle f hf.continuous g hg.continuous P.target
  inv := { (Ordinary.pullbackCompositionComponent f hf g hg P.ordinary).inv with target := fun _ => rfl }
  hom_inv_id := by
    let := (Ordinary.pulledBack g hg (Ordinary.pulledBack f hf P.ordinary)).charts
    exact TargetMap.ext _ _ (Ordinary.pullbackCompositionComponent f hf g hg P.ordinary).hom_inv_id
  inv_hom_id := by
    let := (Ordinary.pulledBack (f ∘ g) (hf.comp hg) P.ordinary).charts
    exact TargetMap.ext _ _ (Ordinary.pullbackCompositionComponent f hf g hg P.ordinary).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
theorem pullbackRealization_id (P : WithTarget n d G B M) :
    (pullbackRealization smoothAction (id : B → B) contMDiff_id).hom.app P ≫
      SheafActionQuotient.reindexCongr ((realization smoothAction).obj P) ManifoldRealization.map_id =
      (realization smoothAction).map (pullbackIdentityComponent P).hom :=
  Pullback.quotientComparison_id P.ordinary.bundle smoothAction P.target P.smooth P.equivariant

set_option backward.isDefEq.respectTransparency false in
theorem pullbackRealization_comp (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (g : B'' → B') (hg : ContMDiff (modelWithCorners k) (modelWithCorners m) ∞ g) (P : WithTarget n d G B M) :
    (pullbackRealization smoothAction g hg).hom.app (pulledBack f hf P) ≫
      (SheafActionQuotient.restriction (ManifoldRealization.map g hg)).map
        ((pullbackRealization smoothAction f hf).hom.app P) ≫
      SheafActionQuotient.reindexCompositeCongr ((realization smoothAction).obj P)
        (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)
        (ManifoldRealization.map (f ∘ g) (hf.comp hg))
        (ManifoldRealization.map_comp g f hg hf).symm =
      (realization smoothAction).map (pullbackCompositionComponent f hf g hg P).hom ≫
        (pullbackRealization smoothAction (f ∘ g) (hf.comp hg)).hom.app P := by
  rw [← Category.assoc]
  exact Pullback.quotientComparison_comp P.ordinary.bundle f hf g hg smoothAction
    P.target P.smooth P.equivariant

def pulledBackRecovery (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (R : Quotients (n := n) (B := B) smoothAction) :
    (realization smoothAction).obj (pulledBack f hf (reconstructed smoothAction R)) ≅
      (SheafActionQuotient.restriction (ManifoldRealization.map f hf)).obj R :=
  (pullbackRealization smoothAction f hf).app (reconstructed smoothAction R) ≪≫
    (SheafActionQuotient.restriction (ManifoldRealization.map f hf)).mapIso (recovery smoothAction R)

/-- Target reconstruction and actual base change agree by an ordinary target-preserving isomorphism. -/
def reconstructionPullbackComponent (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (R : Quotients (n := n) (B := B) smoothAction) :
    reconstructed smoothAction ((SheafActionQuotient.restriction (ManifoldRealization.map f hf)).obj R) ≅
      pulledBack f hf (reconstructed smoothAction R) :=
  (realization smoothAction).preimageIso
    (recovery smoothAction _ ≪≫ (pulledBackRecovery smoothAction f hf R).symm)

@[simp] theorem realization_reconstructionPullbackComponent (f : B' → B)
    (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    (R : Quotients (n := n) (B := B) smoothAction) :
    (realization smoothAction).map (reconstructionPullbackComponent smoothAction f hf R).hom =
      (recovery smoothAction ((SheafActionQuotient.restriction (ManifoldRealization.map f hf)).obj R)).hom ≫
        (pulledBackRecovery smoothAction f hf R).inv := Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
theorem pulledBackRecovery_natural (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
    {P Q : Quotients (n := n) (B := B) smoothAction} (a : P ⟶ Q) :
    (realization smoothAction).map ((pullbackFunctor f hf).map ((reconstruction smoothAction).map a)) ≫
      (pulledBackRecovery smoothAction f hf Q).hom =
    (pulledBackRecovery smoothAction f hf P).hom ≫
      (SheafActionQuotient.restriction (ManifoldRealization.map f hf)).map a := by
  let H := SheafActionQuotient.restriction
    (a := (representation smoothAction).action) (ManifoldRealization.map f hf)
  change (realization smoothAction).map ((pullbackFunctor f hf).map ((reconstruction smoothAction).map a)) ≫
    (pullbackRealization smoothAction f hf).hom.app (reconstructed smoothAction Q) ≫
      H.map (recovery smoothAction Q).hom =
    ((pullbackRealization smoothAction f hf).hom.app (reconstructed smoothAction P) ≫
      H.map (recovery smoothAction P).hom) ≫ H.map a
  rw [← Category.assoc]
  have hn := (pullbackRealization smoothAction f hf).hom.naturality ((reconstruction smoothAction).map a)
  change (realization smoothAction).map ((pullbackFunctor f hf).map ((reconstruction smoothAction).map a)) ≫
    (pullbackRealization smoothAction f hf).hom.app (reconstructed smoothAction Q) =
    (pullbackRealization smoothAction f hf).hom.app (reconstructed smoothAction P) ≫
      H.map ((realization smoothAction).map ((reconstruction smoothAction).map a)) at hn
  rw [hn, Category.assoc, ← H.map_comp, realization_reconstruction_map]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
def reconstructionPullback (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f) :
    SheafActionQuotient.restriction (a := (representation smoothAction).action)
      (ManifoldRealization.map f hf) ⋙ reconstruction smoothAction ≅
        reconstruction smoothAction ⋙ pullbackFunctor f hf :=
  NatIso.ofComponents (reconstructionPullbackComponent smoothAction f hf) (by
    intro P Q a
    apply (realization smoothAction).map_injective
    simp only [Functor.map_comp, Functor.comp_map, realization_reconstructionPullbackComponent,
      realization_reconstruction_map]
    apply (cancel_mono (pulledBackRecovery smoothAction f hf Q).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pulledBackRecovery_natural smoothAction f hf a]
    simp)

end WithTarget
end SquareKit.SmoothPrincipalBundle.Ordinary
