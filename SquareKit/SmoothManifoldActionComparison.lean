import SquareKit.SmoothManifoldActionPresentation
import SquareKit.SmoothQuotientCoverSectionNaturality
import SquareKit.SheafActionQuotientDescentBaseChange

/-! Restriction and descent comparisons retain complete arrows and endpoint transport. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace SquareKit.SmoothManifoldAction
open ManifoldRealization EuclideanOpen SmoothOpenSite SmoothOrdinaryQuotient SheafActionQuotient
open SmoothDiskPresentation
namespace Intertwining
variable {G : Type} [Group G] {X Y : Sheaf topology Type}
    (r : SmoothConstantAction.Representation G X) (s : SmoothConstantAction.Representation G Y)
    (e : X ≅ Y) (he : ∀ g, r.map g ≫ e.hom = e.hom ≫ s.map g)

include he

/-- A fixed-label intertwiner extends to all locally constant sheaf labels. -/
theorem act (U : SmoothPresentationSite.Siteᵒᵖ) (g : (locallyConstantGroup G).obj.obj U)
    (x : X.obj.obj U) :
    e.hom.hom.app U (r.act U g x) = s.act U g (e.hom.hom.app U x) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp Y.property)
    (Presheaf.imageSieve (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) g)).isSeparatedFor.ext
  intro V f hf
  obtain ⟨k, hk⟩ := hf
  rw [← NatTrans.naturality_apply e.hom.hom, r.act_natural, s.act_natural,
    ← NatTrans.naturality_apply e.hom.hom, ← hk, r.act_constant, s.act_constant]
  exact congrArg (fun q : X ⟶ Y => q.hom.app (Opposite.op V) (X.obj.map f.op x)) (he k)

theorem onMap {B : Sheaf topology Type} (k : B ⟶ locallyConstantGroupSheaf G) (m : B ⟶ X) :
    r.action.onMap k m ≫ e.hom = s.action.onMap k (m ≫ e.hom) := by
  ext U x
  exact act r s e he U _ _

def chartEquiv {B : Sheaf topology Type} (m n : B ⟶ X) :
    Arrow (chart r.action m) (chart r.action n) ≃
      Arrow (chart s.action (m ≫ e.hom)) (chart s.action (n ≫ e.hom)) :=
  (chartArrowEquiv m n).trans ((Equiv.subtypeEquivRight (fun k => by
    constructor
    · intro h
      rw [← onMap r s e he, h]
    · intro h
      apply (cancel_mono e.hom).mp
      rw [onMap r s e he, h])).trans (chartArrowEquiv _ _).symm)

theorem chartEquiv_label {B : Sheaf topology Type} {m n : B ⟶ X}
    (f : Arrow (chart r.action m) (chart r.action n)) :
    arrowLabel (chartEquiv r s e he m n f) = arrowLabel f := by
  exact congrArg Subtype.val ((chartArrowEquiv (m ≫ e.hom) (n ≫ e.hom)).apply_symm_apply _)

end Intertwining

variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]
namespace Atlas
variable (A : ChartFamily d M)
    (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))

def representation : SmoothConstantAction.Representation G A.realization where
  map g := A.interpret A (fun x => g • x) (smoothAction g)
  one := by
    have h : (fun x : M => (1 : G) • x) = id := funext (one_smul G)
    simp only [h]
    exact A.interpret_id
  mul g h := by
    simpa only [Function.comp_def, mul_smul] using
      (A.interpret_comp A A (fun x : M => h • x) (fun x : M => g • x) (smoothAction h) (smoothAction g))

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem equivariant (g : G) :
    (SmoothManifoldAction.representation smoothAction).map g ≫ (atlasIso A).hom =
      (atlasIso A).hom ≫ (representation A smoothAction).map g :=
  (atlas_naturality A A (fun x : M => g • x) (smoothAction g)).symm

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem action_equivariant (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (x : (object d M).obj.obj U) :
    (atlasIso A).hom.hom.app U ((SmoothManifoldAction.representation smoothAction).act U g x) =
      (representation A smoothAction).act U g ((atlasIso A).hom.hom.app U x) :=
  Intertwining.act _ _ (atlasIso A) (equivariant A smoothAction) U g x

def chartEquiv {U : Domain} (m n : External.SmoothMap U d M) :=
  Intertwining.chartEquiv (SmoothManifoldAction.representation smoothAction)
    (representation A smoothAction) (atlasIso A) (equivariant A smoothAction)
    (hat m.val m.property) (hat n.val n.property)

/-- The same external smooth families are obtained after changing atlas. -/
def smoothEquiv {U : Domain} (m n : External.SmoothMap U d M) :=
  (chartEquiv A smoothAction m n).symm.trans (External.smoothChartEquiv smoothAction m n)

theorem smoothEquiv_comparison {U : Domain} (m n : External.SmoothMap U d M)
    (f : External.ChartArrow smoothAction m n) :
    smoothEquiv A smoothAction m n (chartEquiv A smoothAction m n f) =
      External.smoothChartEquiv smoothAction m n f := by
  exact congrArg (External.smoothChartEquiv smoothAction m n)
    ((chartEquiv A smoothAction m n).symm_apply_apply f)

theorem common_refinement : atlasIso A =
    EuclideanOpen.Charts.commonRefinementIso
      ((ChartFamily.preferred (n := d) (M := M)).commonLeft A)
      ((ChartFamily.preferred (n := d) (M := M)).commonRight A) := atlas_common A

end Atlas

namespace External
variable {U V W : Domain}

def SmoothMap.restrict (m : SmoothMap U d M) (r : V ⟶ U) : SmoothMap V d M :=
  ⟨fun x => m.val ((show EuclideanOpen.Map V U from r) x),
    m.property.comp (openMap_contMDiff r)⟩

theorem hat_restrict (m : SmoothMap U d M) (r : V ⟶ U) :
    embedding.map r ≫ hat m.val m.property = hat (m.restrict r).val (m.restrict r).property := by
  apply (cancel_epi (principalIso V).hom).mp
  simp only [hat, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← principalIso_naturality r]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (map_comp _ _ (openMap_contMDiff r) m.property).symm

def Family.restrict {m n : SmoothMap U d M} (a : Family (G := G) U m n) (r : V ⟶ U) :
    Family (G := G) V (m.restrict r) (n.restrict r) :=
  ⟨fun x => a.val ((show EuclideanOpen.Map V U from r) x),
    a.property.1.comp (openMap_contMDiff r),
    fun _ => a.property.2.1 _, fun _ => a.property.2.2 _⟩

omit [IsManifold (Model d) ∞ M] in
theorem Family.restrict_id {m n : SmoothMap U d M} (a : Family (G := G) U m n) :
    a.restrict (𝟙 U) = a := rfl

omit [IsManifold (Model d) ∞ M] in
theorem Family.restrict_comp {m n : SmoothMap U d M} (a : Family (G := G) U m n)
    (r : V ⟶ U) (s : W ⟶ V) : (a.restrict r).restrict s = a.restrict (s ≫ r) := rfl

/-- Change endpoint expressions by the proved functor equations. -/
def transport {X Y : Sheaf topology Type} {a : Action (locallyConstantGroup G) Y}
    {m n m' n' : X ⟶ Y} (hm : m = m') (hn : n = n')
    (f : Arrow (chart a m) (chart a n)) : Arrow (chart a m') (chart a n') := by
  cases hm
  cases hn
  exact f

def transportEquiv {X Y : Sheaf topology Type} {a : Action (locallyConstantGroup G) Y}
    {m n m' n' : X ⟶ Y} (hm : m = m') (hn : n = n') :
    Arrow (chart a m) (chart a n) ≃ Arrow (chart a m') (chart a n') where
  toFun := transport hm hn
  invFun := transport hm.symm hn.symm
  left_inv f := by cases hm; cases hn; rfl
  right_inv f := by cases hm; cases hn; rfl

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem transport_label {Y : Sheaf topology Type} {a : Action (locallyConstantGroup G) Y}
    {m n m' n' : embedding.obj U ⟶ Y} (hm : m = m') (hn : n = n')
    (f : Arrow (chart a m) (chart a n)) :
    ForwardLabel.label (transport hm hn f) = ForwardLabel.label f := by
  cases hm
  cases hn
  rfl

variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))
variable {m n : SmoothMap U d M}

def restrictArrow (f : ChartArrow smoothAction m n) (r : V ⟶ U) :
    ChartArrow smoothAction (m.restrict r) (n.restrict r) :=
  transport (hat_restrict m r) (hat_restrict n r) (f.reindex (embedding.map r))

theorem smoothChartEquiv_restrict (f : ChartArrow smoothAction m n) (r : V ⟶ U) :
    smoothChartEquiv smoothAction _ _ (restrictArrow smoothAction f r) =
      (smoothChartEquiv smoothAction m n f).restrict r := by
  apply Family.ext
  intro x
  change ForwardLabel.label (transport _ _ _) x = _
  exact (congrArg (fun l : LocallyConstant (Points V) G => l x)
    (transport_label (hat_restrict m r) (hat_restrict n r) (f.reindex (embedding.map r)))).trans
      (ForwardLabel.restriction f r x)

theorem restrictArrow_id (f : ChartArrow smoothAction m n) :
    restrictArrow smoothAction f (𝟙 U) = f := by
  apply (smoothChartEquiv smoothAction m n).injective
  exact smoothChartEquiv_restrict smoothAction f (𝟙 U)

theorem restrictArrow_comp (f : ChartArrow smoothAction m n) (r : V ⟶ U) (s : W ⟶ V) :
    restrictArrow smoothAction (restrictArrow smoothAction f r) s =
      restrictArrow smoothAction f (s ≫ r) := by
  apply (smoothChartEquiv smoothAction _ _).injective
  exact (smoothChartEquiv_restrict smoothAction (restrictArrow smoothAction f r) s).trans
    ((congrArg (fun a => a.restrict s) (smoothChartEquiv_restrict smoothAction f r)).trans
      (smoothChartEquiv_restrict smoothAction f (s ≫ r)).symm)

/-- Canonical global-chart descent only; arbitrary nontrivial torsors need no
chosen global trivialization and are outside this comparison's scope. -/
theorem canonicalRecovery_comparison
    (A B : SplitSheaf.Ty (embedding.obj U))
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]
    (f : Descent.Map
      (Descent.canonicalDatum A (chart (representation smoothAction).action (hat m.val m.property)))
      (Descent.canonicalDatum A (chart (representation smoothAction).action (hat n.val n.property)))) :
    smoothChartEquiv smoothAction m n (Descent.canonicalArrowEquiv B _ _
      (Descent.recoveryArrowComparison A B _ _ f)) =
    smoothChartEquiv smoothAction m n (Descent.canonicalArrowEquiv A _ _ f) := by
  rw [Descent.recoveryArrowComparison_commutes]

end External
namespace SelectedBaseChange
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))
variable {X Y : Sheaf topology Type} (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
variable {q r : Descent.Datum (a := (representation smoothAction).action) A}

/-- The selected comparison is the existing descent comparison on this actual action. -/
def comparison (q : Descent.Datum (a := (representation smoothAction).action) A) (f : Y ⟶ X) :=
  q.baseChangeComparison f

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem naturality (h : Descent.Map q r) (f : Y ⟶ X) :
    (h.arrow.reindex f).comp (r.baseChangeComparison f) =
      (q.baseChangeComparison f).comp (h.baseChange f).arrow :=
  Descent.Map.baseChangeComparison_naturality h f

end SelectedBaseChange

namespace Cover
open SmoothQuotientCoverMatching
open Internal.PathTransport
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))
variable {X Y X' Y' : Sheaf topology Type}
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (f : Y ⟶ X) [Presheaf.IsLocallySurjective topology f.hom]
variable (k : Y' ⟶ X') [Presheaf.IsLocallySurjective topology k.hom]
variable (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u)

omit [TopologicalSpace G] [DiscreteTopology G]
  [Presheaf.IsLocallySurjective topology f.hom] [Presheaf.IsLocallySurjective topology k.hom] in
/-- Matching naturality for the constructed action retains whole functors. -/
theorem matchingNaturality :
    (matchingEquivalence (representation smoothAction).action hΓ f).functor ⋙
        (splitSquareMap (representation smoothAction).action hΓ u v square).functor =
      squareFunctor (representation smoothAction).action hΓ u v square ⋙
        (matchingEquivalence (representation smoothAction).action hΓ k).functor :=
  matchingEquivalence_natural (representation smoothAction).action hΓ u v square

omit [TopologicalSpace G] [DiscreteTopology G]
  [Presheaf.IsLocallySurjective topology f.hom] [Presheaf.IsLocallySurjective topology k.hom] in
/-- Family naturality retains selected base transports and matching arrows. -/
theorem familyNaturality :
    (relativeMatchingEquivalence (representation smoothAction).action hΓ hB f).functor ⋙
        squareFunctor (representation smoothAction).action (.ext hΓ hB) u v square =
      relativeSquareFunctor (representation smoothAction).action hΓ hB u v square ⋙
        (relativeMatchingEquivalence (representation smoothAction).action hΓ hB k).functor :=
  relativeMatchingEquivalence_square (representation smoothAction).action hΓ hB u v square

def familyRecovery (q : Datum (representation smoothAction).action hΓ f) :=
  familySquare_recovery (representation smoothAction).action hΓ hB u v square q

/-- Complete matching-section gluing, with the supplied local comparison. -/
def sectionNaturality
    (s : GroupoidModel.Section (relativeMatchingFamily (representation smoothAction).action hΓ hB f))
    (t : GroupoidModel.Section (relativeMatchingFamily (representation smoothAction).action hΓ hB k))
    (localComparison :
      s.lift ⋙ (dependentComprehensionEquivalence (representation smoothAction).action hΓ hB f).functor ⋙
          squareFunctor (representation smoothAction).action (.ext hΓ hB) u v square ≅
        squareFunctor (representation smoothAction).action hΓ u v square ⋙ t.lift ⋙
          (dependentComprehensionEquivalence (representation smoothAction).action hΓ hB k).functor) :=
  gluedSectionLift_natural (representation smoothAction).action hΓ hB f k u v square s t localComparison

end Cover

namespace Disk
set_option maxHeartbeats 800000
open SmoothQuarterTurnArcs SmoothQuarterTurnQuotient Orbifolds.QuarterTurn

local instance coordinateAction : MulAction C4 (ordinaryOpen diskDomain) where
  smul g x := (show EuclideanOpen.Map _ _ from diskMap g) x
  one_smul x := by
    change (show EuclideanOpen.Map _ _ from diskMap 1) x = x
    rw [diskMap_one]
    rfl
  mul_smul g h x := by
    change (show EuclideanOpen.Map _ _ from diskMap (g * h)) x = _
    rw [diskMap_mul]
    rfl

local instance : MulAction C4 (Points diskDomain) := coordinateAction

theorem smooth (g : C4) : ContMDiff (Model diskDomain.dimension) (Model diskDomain.dimension) ∞
    (fun x : ordinaryOpen diskDomain => g • x) := openMap_contMDiff (diskMap g)

abbrev endpoint {U : Domain} (m : U ⟶ diskDomain) : External.SmoothMap U diskDomain.dimension (ordinaryOpen diskDomain) :=
  ⟨(show EuclideanOpen.Map _ _ from m).toFun, openMap_contMDiff m⟩

theorem equivariant (g : C4) :
    (representation smooth).map g ≫ (principalIso diskDomain).hom =
      (principalIso diskDomain).hom ≫ diskRepresentation.map g :=
  principalIso_naturality (diskMap g)

theorem endpoint_comparison {U : Domain} (m : U ⟶ diskDomain) :
    hat (endpoint m).val (endpoint m).property ≫ (principalIso diskDomain).hom = embedding.map m := by
  change ((principalIso U).inv ≫ ManifoldRealization.map _ _) ≫ _ = _
  rw [Category.assoc, principalIso_naturality]
  simp

def quotientEquiv {U : Domain} (m n : U ⟶ diskDomain) :
    External.ChartArrow smooth (endpoint m) (endpoint n) ≃
      Arrow (chart diskRepresentation.action (embedding.map m))
        (chart diskRepresentation.action (embedding.map n)) :=
  (Intertwining.chartEquiv (representation smooth) diskRepresentation (principalIso diskDomain)
    equivariant _ _).trans
    (External.transportEquiv (endpoint_comparison m) (endpoint_comparison n))

/-- Coordinate conversion uses the explicit real-linear complexCoordinates map. -/
theorem diskPoints_smooth : ContMDiff (Model diskDomain.dimension) 𝓘(ℝ, ℂ) ∞
    (show ordinaryOpen diskDomain → Disk from diskPoints) := by
  apply (ContMDiff.subtypeVal_comp_iff disk _).mp
  exact complexCoordinates.contDiff.contMDiff.comp contMDiff_subtype_val

def labelComparison {U : Domain} (m n : U ⟶ diskDomain) :
    External.Labels (G := C4) U (endpoint m) (endpoint n) ≃ SmoothDiskPresentation.Family U m n where
  toFun g := ⟨g.val, fun x => by
    have h := congrArg diskPoints (g.property x)
    change diskPoints (diskPoints.symm (g.val x • diskValue m x)) = _ at h
    simpa only [Equiv.apply_symm_apply, endpoint, diskValue] using h⟩
  invFun g := ⟨g.val, fun x => by
    apply diskPoints.injective
    change diskPoints (diskPoints.symm (g.val x • diskValue m x)) = _
    simpa only [Equiv.apply_symm_apply, endpoint, diskValue] using g.property x⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def familyEquiv {U : Domain} (m n : U ⟶ diskDomain) :
    External.Family (G := C4) U (endpoint m) (endpoint n) ≃ SmoothDiskPresentation.SmoothFamily U m n :=
  (External.labelsEquiv _ _).symm.trans ((labelComparison m n).trans (familySmoothEquiv U m n))

theorem familyEquiv_apply {U : Domain} (m n : U ⟶ diskDomain)
    (a : External.Family (G := C4) U (endpoint m) (endpoint n)) (x : Points U) :
    (familyEquiv m n a).val x = ((a.val x).1, diskPoints (a.val x).2) := by
  exact Prod.ext rfl (congrArg diskPoints (a.property.2.1 x).symm)

theorem forward_agreement {U : Domain} (m n : U ⟶ diskDomain)
    (f : External.ChartArrow smooth (endpoint m) (endpoint n)) :
    familyEquiv m n (External.smoothChartEquiv smooth _ _ f) =
      SmoothDiskPresentation.smoothChartEquiv U m n (quotientEquiv m n f) := by
  apply Subtype.ext
  funext x
  apply Prod.ext
  · change ForwardLabel.label f x = ForwardLabel.label (quotientEquiv m n f) x
    have ht := External.transport_label (endpoint_comparison m) (endpoint_comparison n)
      (Intertwining.chartEquiv (representation smooth) diskRepresentation (principalIso diskDomain)
        equivariant _ _ f)
    have he := Intertwining.chartEquiv_label (representation smooth) diskRepresentation
      (principalIso diskDomain) equivariant f
    change ForwardLabel.label f x = ForwardLabel.label (External.transport _ _ _) x
    rw [ht]
    exact congrArg (fun k => (ordinaryHomLabelEquiv C4 U k x)⁻¹) he.symm
  · rfl

theorem inverse_agreement {U : Domain} (m n : U ⟶ diskDomain)
    (a : SmoothDiskPresentation.SmoothFamily U m n) :
    quotientEquiv m n ((External.smoothChartEquiv smooth _ _).symm ((familyEquiv m n).symm a)) =
      (SmoothDiskPresentation.smoothChartEquiv U m n).symm a := by
  apply (SmoothDiskPresentation.smoothChartEquiv U m n).injective
  rw [← forward_agreement, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem diskPoints_symm_smooth : ContMDiff 𝓘(ℝ, ℂ) (Model diskDomain.dimension) ∞
    (show Disk → ordinaryOpen diskDomain from diskPoints.symm) := by
  apply (ContMDiff.subtypeVal_comp_iff (ordinaryOpen diskDomain) _).mp
  exact complexCoordinates.symm.contDiff.contMDiff.comp contMDiff_subtype_val

theorem familyEquiv_symm_apply {U : Domain} (m n : U ⟶ diskDomain)
    (a : SmoothDiskPresentation.SmoothFamily U m n) (x : Points U) :
    ((familyEquiv m n).symm a).val x = ((a.val x).1, diskPoints.symm (a.val x).2) := by
  have he := congrArg (fun a => a.val x) ((familyEquiv m n).apply_symm_apply a)
  rw [familyEquiv_apply] at he
  have hfst := congrArg (fun z : C4 × Disk => z.1) he
  have hsnd := congrArg (fun z : C4 × Disk => z.2) he
  refine Prod.ext ?_ ?_
  · exact hfst
  apply diskPoints.injective
  rw [Equiv.apply_symm_apply]
  exact hsnd

end Disk
end SquareKit.SmoothManifoldAction
