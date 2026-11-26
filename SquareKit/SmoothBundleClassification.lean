import SquareKit.SmoothTorsorEquivalence
import SquareKit.SmoothBundleCategory
import SquareKit.SmoothTorsorReconstructionRecovery
import SquareKit.SmoothTorsorReconstructionSeparation

/-! Classification by the constructed ordinary total manifold, with a specified
reconstruction functor and natural unit/counit. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothPrincipalBundle.Ordinary
open CategoryTheory ManifoldRealization SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]

abbrev Torsors := SheafTorsor.Torsor (locallyConstantGroup G) (object n B)

/-- The total manifold and its action/projection are those constructed from P. -/
def reconstructed (P : Torsors (n := n) (G := G) (B := B)) : Ordinary n G B := by
  letI := SmoothTorsorReconstruction.chartedSpace P
  letI := SmoothTorsorReconstruction.isManifold P
  exact ofBundle (SmoothTorsorReconstruction.bundle P)

def recovery (P : Torsors (n := n) (G := G) (B := B)) :
    realization.obj (reconstructed P) ≅ P := by
  letI := SmoothTorsorReconstruction.chartedSpace P
  letI := SmoothTorsorReconstruction.isManifold P
  exact (SmoothTorsorReconstruction.reconstructedArrow P).toIso

def reconstruction : Torsors (n := n) (G := G) (B := B) ⥤ Ordinary n G B where
  obj := reconstructed
  map {P Q} h := realization.preimage ((recovery P).hom ≫ h ≫ (recovery Q).inv)
  map_id P := by
    apply realization.map_injective
    simp
  map_comp h k := by
    apply realization.map_injective
    simp [Category.assoc]

@[simp] theorem realization_reconstruction_map
    {P Q : Torsors (n := n) (G := G) (B := B)} (h : P ⟶ Q) :
    realization.map (reconstruction.map h) = (recovery P).hom ≫ h ≫ (recovery Q).inv :=
  Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
def counit : reconstruction (n := n) (G := G) (B := B) ⋙ realization ≅ 𝟭 _ :=
  NatIso.ofComponents recovery (by intro P Q h; simp [Category.assoc])

def unitComponent (P : Ordinary n G B) : P ≅ reconstruction.obj (realization.obj P) :=
  realization.preimageIso (recovery (realization.obj P)).symm

@[simp] theorem realization_unitComponent (P : Ordinary n G B) :
    realization.map (unitComponent P).hom = (recovery (realization.obj P)).inv :=
  Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
def unit : 𝟭 (Ordinary n G B) ≅ realization ⋙ reconstruction :=
  NatIso.ofComponents unitComponent (by
    intro P Q h
    apply realization.map_injective
    simp)

set_option backward.isDefEq.respectTransparency false in
/-- Every sheaf torsor is represented by the chosen ordinary bundle, with all maps retained. -/
def classification : Ordinary n G B ≌ Torsors (n := n) (G := G) (B := B) where
  functor := realization
  inverse := reconstruction
  unitIso := unit
  counitIso := counit
  functor_unitIso_comp P := by
    change realization.map (unitComponent P).hom ≫ (recovery (realization.obj P)).hom = _
    simp

/-- Any other ordinary realization is compared by a uniquely specified bundle isomorphism. -/
def recoveryComparison (P : Torsors (n := n) (G := G) (B := B))
    (Q : Ordinary n G B) (e : realization.obj Q ≅ P) : reconstructed P ≅ Q :=
  realization.preimageIso (recovery P ≪≫ e.symm)

@[simp] theorem realization_recoveryComparison
    (P : Torsors (n := n) (G := G) (B := B))
    (Q : Ordinary n G B) (e : realization.obj Q ≅ P) :
    realization.map (recoveryComparison P Q e).hom = (recovery P).hom ≫ e.inv :=
  Functor.map_preimage _ _

theorem recoveryComparison_unique (P : Torsors (n := n) (G := G) (B := B))
    (Q : Ordinary n G B) (e : realization.obj Q ≅ P)
    (a : reconstructed P ⟶ Q) (ha : realization.map a ≫ e.hom = (recovery P).hom) :
    a = (recoveryComparison P Q e).hom := by
  apply realization.map_injective
  rw [realization_recoveryComparison]
  exact (Iso.eq_comp_inv e).mpr ha

/-- Recovery of the full total sheaf, rather than just its real points. -/
def totalRecovery (P : Torsors (n := n) (G := G) (B := B)) :
    object n (reconstructed P).Total ≅ SplitSheaf.extension P.family :=
  SmoothTorsorReconstruction.reconstructedTotalIso P

theorem totalRecovery_projection (P : Torsors (n := n) (G := G) (B := B)) :
    (totalRecovery P).hom ≫ SplitSheaf.p P.family =
      ManifoldRealization.map (reconstructed P).bundle.projection
        (reconstructed P).bundle.smooth_projection :=
  SmoothTorsorReconstruction.reconstructedTotalIso_projection P

theorem totalRecovery_equivariant (P : Torsors (n := n) (G := G) (B := B))
    (U : SmoothPresentationSite.Siteᵒᵖ) (g : (locallyConstantGroup G).obj.obj U)
    (z : (object n (reconstructed P).Total).obj.obj U) :
    (totalRecovery P).hom.hom.app U
        ((SmoothManifoldAction.representation (reconstructed P).bundle.smooth_action).act U g z) =
      P.toAction.totalAct U g ((totalRecovery P).hom.hom.app U z) :=
  SmoothTorsorReconstruction.reconstructedTotalIso_equivariant P U g z

/-- Arbitrary independently chosen ordinary realizations have a specified comparison. -/
def choiceComparison {P : Torsors (n := n) (G := G) (B := B)}
    {Q R : Ordinary n G B} (e : realization.obj Q ≅ P) (f : realization.obj R ≅ P) : Q ≅ R :=
  realization.preimageIso (e ≪≫ f.symm)

@[simp] theorem realization_choiceComparison {P : Torsors (n := n) (G := G) (B := B)}
    {Q R : Ordinary n G B} (e : realization.obj Q ≅ P) (f : realization.obj R ≅ P) :
    realization.map (choiceComparison e f).hom = e.hom ≫ f.inv :=
  Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem choiceComparison_refl {P : Torsors (n := n) (G := G) (B := B)}
    {Q : Ordinary n G B} (e : realization.obj Q ≅ P) : choiceComparison e e = Iso.refl Q := by
  apply Iso.ext
  apply realization.map_injective
  simp

set_option backward.isDefEq.respectTransparency false in
theorem choiceComparison_trans {P : Torsors (n := n) (G := G) (B := B)}
    {Q R S : Ordinary n G B} (e : realization.obj Q ≅ P) (f : realization.obj R ≅ P)
    (g : realization.obj S ≅ P) :
    choiceComparison e f ≪≫ choiceComparison f g = choiceComparison e g := by
  apply Iso.ext
  apply realization.map_injective
  simp [Category.assoc]

theorem choiceComparison_unique {P : Torsors (n := n) (G := G) (B := B)}
    {Q R : Ordinary n G B} (e : realization.obj Q ≅ P) (f : realization.obj R ≅ P)
    (a : Q ⟶ R) (ha : realization.map a ≫ f.hom = e.hom) :
    a = (choiceComparison e f).hom := by
  apply realization.map_injective
  rw [realization_choiceComparison]
  exact (Iso.eq_comp_inv f).mpr ha

/-- The categorical unit is an actual equivariant diffeomorphism over the base. -/
def unitDiffeomorph (P : Ordinary n G B) :
    P.Total ≃ₘ⟮modelWithCorners n, modelWithCorners n⟯ (reconstructed (realization.obj P)).Total :=
  (unitComponent P).hom.diffeomorph

theorem unit_projection (P : Ordinary n G B) (x : P.Total) :
    (reconstructed (realization.obj P)).bundle.projection (unitDiffeomorph P x) =
      P.bundle.projection x := (unitComponent P).hom.projection x

theorem unit_equivariant (P : Ordinary n G B) (g : G) (x : P.Total) :
    unitDiffeomorph P (g • x) = g • unitDiffeomorph P x :=
  (unitComponent P).hom.equivariant g x

/-- Classification may be observed on any independently supplied covering atlas. -/
def chartRealization (A : ChartFamily n B) :
    Ordinary n G B ⥤ SheafTorsor.Torsor (locallyConstantGroup G) A.realization :=
  realization ⋙ (torsorBaseEquivalence (H := G) (atlasIso A)).functor

instance (A : ChartFamily n B) : (chartRealization (G := G) A).Full :=
  inferInstanceAs (realization ⋙ (torsorBaseEquivalence (H := G) (atlasIso A)).functor).Full
instance (A : ChartFamily n B) : (chartRealization (G := G) A).Faithful :=
  inferInstanceAs (realization ⋙ (torsorBaseEquivalence (H := G) (atlasIso A)).functor).Faithful

theorem chartRealization_obj (A : ChartFamily n B) (Q : Ordinary n G B) :
    (chartRealization A).obj Q = SheafTorsor.reindex Q.bundle.descendedObject.torsor
      (A.comparison Q.bundle.baseCharts).hom := Q.bundle.realizedTorsor_chart A

/-- Normalizing an arbitrary chart presentation uses its actual atlas isomorphism. -/
def chartChoiceComparison (A : ChartFamily n B)
    {P : SheafTorsor.Torsor (locallyConstantGroup G) A.realization}
    {Q R : Ordinary n G B} (e : (chartRealization A).obj Q ≅ P)
    (f : (chartRealization A).obj R ≅ P) : Q ≅ R :=
  (chartRealization A).preimageIso (e ≪≫ f.symm)

@[simp] theorem chartRealization_choiceComparison (A : ChartFamily n B)
    {P : SheafTorsor.Torsor (locallyConstantGroup G) A.realization}
    {Q R : Ordinary n G B} (e : (chartRealization A).obj Q ≅ P)
    (f : (chartRealization A).obj R ≅ P) :
    (chartRealization A).map (chartChoiceComparison A e f).hom = e.hom ≫ f.inv :=
  Functor.map_preimage _ _

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem chartChoiceComparison_refl (A : ChartFamily n B)
    {P : SheafTorsor.Torsor (locallyConstantGroup G) A.realization}
    {Q : Ordinary n G B} (e : (chartRealization A).obj Q ≅ P) :
    chartChoiceComparison A e e = Iso.refl Q := by
  apply Iso.ext
  apply (chartRealization A).map_injective
  simp

set_option backward.isDefEq.respectTransparency false in
theorem chartChoiceComparison_trans (A : ChartFamily n B)
    {P : SheafTorsor.Torsor (locallyConstantGroup G) A.realization}
    {Q R S : Ordinary n G B} (e : (chartRealization A).obj Q ≅ P)
    (f : (chartRealization A).obj R ≅ P) (g : (chartRealization A).obj S ≅ P) :
    chartChoiceComparison A e f ≪≫ chartChoiceComparison A f g =
      chartChoiceComparison A e g := by
  apply Iso.ext
  apply (chartRealization A).map_injective
  simp [Category.assoc]

theorem chartChoiceComparison_unique (A : ChartFamily n B)
    {P : SheafTorsor.Torsor (locallyConstantGroup G) A.realization}
    {Q R : Ordinary n G B} (e : (chartRealization A).obj Q ≅ P)
    (f : (chartRealization A).obj R ≅ P) (a : Q ⟶ R)
    (ha : (chartRealization A).map a ≫ f.hom = e.hom) :
    a = (chartChoiceComparison A e f).hom := by
  apply (chartRealization A).map_injective
  rw [chartRealization_choiceComparison]
  exact (Iso.eq_comp_inv f).mpr ha

set_option backward.isDefEq.respectTransparency false in
theorem chartChoiceComparison_of_global (A : ChartFamily n B)
    {P : Torsors (n := n) (G := G) (B := B)} {Q R : Ordinary n G B}
    (e : realization.obj Q ≅ P) (f : realization.obj R ≅ P) :
    chartChoiceComparison A
      ((torsorBaseEquivalence (H := G) (atlasIso A)).functor.mapIso e)
      ((torsorBaseEquivalence (H := G) (atlasIso A)).functor.mapIso f) =
      choiceComparison e f := by
  apply Iso.ext
  apply (chartRealization A).map_injective
  rw [chartRealization_choiceComparison]
  change (torsorBaseEquivalence (H := G) (atlasIso A)).functor.map e.hom ≫
    (torsorBaseEquivalence (H := G) (atlasIso A)).functor.map f.inv =
    (torsorBaseEquivalence (H := G) (atlasIso A)).functor.map
      (realization.map (choiceComparison e f).hom)
  rw [realization_choiceComparison, Functor.map_comp]

/-- The same chart observation can be computed through the actual common refinement. -/
theorem chartRealization_common (A : ChartFamily n B) :
    chartRealization (G := G) A = realization ⋙ SheafTorsor.restriction
      (EuclideanOpen.Charts.commonRefinementIso
        ((ChartFamily.preferred (n := n) (M := B)).commonLeft A)
        ((ChartFamily.preferred (n := n) (M := B)).commonRight A)).inv := by
  change realization ⋙ SheafTorsor.restriction (atlasIso A).inv = _
  rw [atlas_common A]

/-- Separation and countability are consequences with additional hypotheses. -/
theorem reconstructed_t2Space (P : Torsors (n := n) (G := G) (B := B))
    [T2Space B] : T2Space (reconstructed P).Total :=
  SmoothTorsorReconstruction.total_t2Space P

theorem reconstructed_secondCountableTopology (P : Torsors (n := n) (G := G) (B := B))
    [SecondCountableTopology B] [Countable G] :
    SecondCountableTopology (reconstructed P).Total :=
  SmoothTorsorReconstruction.total_secondCountableTopology P

end SquareKit.SmoothPrincipalBundle.Ordinary
