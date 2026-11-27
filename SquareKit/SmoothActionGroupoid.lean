import SquareKit.SmoothBranchActionComparison
import SquareKit.SmoothTransverseRealization
import SquareKit.SheafGroupoidAction

/-! Actual smooth action groupoids, their composable-arrow manifolds, and the all-stage
arrow comparison. Independent branch consumers use the geometric arrow sheaf;
the action coordinates prove recovery and transport the groupoid laws. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace SquareKit.SmoothActionGroupoid
open ManifoldRealization SmoothOpenSite

section ConstantProduct
variable (G : Type) [Group G] (M : Sheaf topology Type)

def constantInjection (g : G) : M ⟶ SheafRelation.product (locallyConstantGroupSheaf G) M :=
  SheafRelation.lift (constantSection M g) (𝟙 M)

def constantCoproductMap : SheafCoproductLocal.total (fun _ : G => M) ⟶
    SheafRelation.product (locallyConstantGroupSheaf G) M :=
  SheafCoproductLocal.desc _ (constantInjection G M)

def rawInclusion : SmoothConstantAction.labelParameters (G := G) M ⟶
    (SheafCoproductLocal.total (fun _ : G => M)).obj where
  app U := ↾fun x => (SheafCoproductLocal.inclusion (fun _ : G => M) x.1).hom.app U x.2
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact NatTrans.naturality_apply (SheafCoproductLocal.inclusion (fun _ : G => M) x.1).hom f x.2

def constantCoproductInv : SheafRelation.product (locallyConstantGroupSheaf G) M ⟶
    SheafCoproductLocal.total (fun _ : G => M) :=
  ⟨((topology.W_of_isLocallyBijective (SmoothConstantAction.labelMap M)).homEquiv _
    (SheafCoproductLocal.total (fun _ : G => M)).property).symm (rawInclusion G M)⟩

theorem constantInjection_inv (g : G) :
    constantInjection G M g ≫ constantCoproductInv G M =
      SheafCoproductLocal.inclusion (fun _ : G => M) g := by
  have h := ((topology.W_of_isLocallyBijective (SmoothConstantAction.labelMap M)).homEquiv _
    (SheafCoproductLocal.total (fun _ : G => M)).property).apply_symm_apply (rawInclusion G M)
  ext U x
  exact congrArg (fun k => k.app U (g,x)) h

def constantProductIso : SheafCoproductLocal.total (fun _ : G => M) ≅
    SheafRelation.product (locallyConstantGroupSheaf G) M where
  hom := constantCoproductMap G M
  inv := constantCoproductInv G M
  hom_inv_id := by
    apply colimit.hom_ext
    rintro ⟨g⟩
    change SheafCoproductLocal.inclusion _ g ≫ (constantCoproductMap G M ≫ _) = _
    rw [← Category.assoc, constantCoproductMap, SheafCoproductLocal.inclusion_desc,
      constantInjection_inv, Category.comp_id]
  inv_hom_id := by
    apply Sheaf.hom_ext
    apply ((topology.W_of_isLocallyBijective (SmoothConstantAction.labelMap M)).homEquiv _
      (SheafRelation.product (locallyConstantGroupSheaf G) M).property).injective
    ext U x
    have h := congrArg (fun k => k.hom.app U x.2) (constantInjection_inv G M x.1)
    change (constantCoproductMap G M).hom.app U
      ((constantCoproductInv G M).hom.app U ((constantLabel G).app U x.1,x.2)) =
        ((constantLabel G).app U x.1,x.2)
    change (constantCoproductInv G M).hom.app U ((constantLabel G).app U x.1,x.2) = _ at h
    rw [h]
    exact congrArg (fun k => k.hom.app U x.2)
      (SheafCoproductLocal.inclusion_desc (fun _ : G => M) (constantInjection G M) x.1)
end ConstantProduct

section Geometry
open Orbifolds.FiniteActionPresentation SmoothLocalDiffeomorphModel
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]

abbrev ArrowModel := SmoothBranchActionComparison.ActionModel (d := d) (G := G) (M := M)
abbrev source : ArrowModel (d := d) (G := G) (M := M) → M :=
  SmoothBranchActionComparison.actionSource
abbrev target : ArrowModel (d := d) (G := G) (M := M) → M :=
  SmoothBranchActionComparison.actionTarget

abbrev source_smooth := SmoothBranchActionComparison.actionSource_smooth (d := d) (G := G) (M := M)

variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞
  (fun x : M => g • x))

abbrev target_smooth := SmoothBranchActionComparison.actionTarget_smooth smoothAction

def sheet (g : G) (x : M) : ArrowModel (d := d) (G := G) (M := M) := (g,x)

omit [Group G] [MulAction G M] in
theorem sheet_smooth (g : G) : ContMDiff (modelWithCorners d) (modelWithCorners d) ∞
    (sheet (d := d) (M := M) g) :=
  (toModel_smooth (Orbifolds.FiniteActionPresentation.source (G := G) (M := M))
    (source_etale (modelWithCorners d))).comp (contMDiff_const.prodMk contMDiff_id)

def piece (g : G) : Opens (ArrowModel (d := d) (G := G) (M := M)) :=
  ⟨{a | a.1 = g}, (isOpen_discrete {g}).preimage continuous_fst⟩

def pieceDiffeomorph (g : G) : Diffeomorph (modelWithCorners d) (modelWithCorners d)
    M (piece (d := d) (M := M) g) ∞ where
  toFun x := ⟨sheet (d := d) g x,rfl⟩
  invFun a := source a.val
  left_inv _ := rfl
  right_inv a := Subtype.ext (Prod.ext a.property.symm rfl)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp (sheet_smooth (d := d) (M := M) g)
  contMDiff_invFun := source_smooth.comp contMDiff_subtype_val

def coproductArrowIso : SheafCoproductLocal.total (fun _ : G => object d M) ≅
    object d (ArrowModel (d := d) (G := G) (M := M)) :=
  Limits.Sigma.mapIso (fun g => diffeomorphIso (pieceDiffeomorph (d := d) (M := M) g)) ≪≫
    DisjointOpen.assemblyIso (piece (d := d) (M := M)) (fun a => ⟨a.1,rfl⟩)
      (by intro g h hgh; exact Set.disjoint_left.mpr (fun _ ha hb => hgh (ha.symm.trans hb)))

omit [Group G] [MulAction G M] in
@[reassoc] theorem inclusion_coproductArrowIso (g : G) :
    SheafCoproductLocal.inclusion (fun _ : G => object d M) g ≫
      (coproductArrowIso (d := d) (G := G) (M := M)).hom =
        map (sheet (d := d) (M := M) g) (sheet_smooth (d := d) (M := M) g) := by
  change Sigma.ι (fun _ : G => object d M) g ≫ (_ ≫ _) = _
  rw [← Category.assoc, Sigma.ι_mapIso_hom, Category.assoc,
    DisjointOpen.assemblyIso_hom]
  change _ ≫ (SheafCoproductLocal.inclusion _ g ≫ DisjointOpen.assembly _) = _
  rw [DisjointOpen.inclusion_assembly]
  rw [DisjointOpen.inclusion, diffeomorphIso, ← map_comp]
  rfl

/-- All-stage arrow coordinates, obtained from the actual disjoint open sheets. -/
def arrowIso : object d (ArrowModel (d := d) (G := G) (M := M)) ≅
    SheafRelation.product (locallyConstantGroupSheaf G) (object d M) :=
  (coproductArrowIso (d := d) (G := G) (M := M)).symm ≪≫ constantProductIso G (object d M)

omit [MulAction G M] in
@[reassoc] theorem sheet_arrowIso (g : G) :
    map (sheet (d := d) (M := M) g) (sheet_smooth (d := d) (M := M) g) ≫ (arrowIso (d := d) (G := G) (M := M)).hom =
      constantInjection G (object d M) g := by
  rw [← inclusion_coproductArrowIso]
  simp only [arrowIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, constantProductIso, constantCoproductMap,
    SheafCoproductLocal.inclusion_desc]

omit [Group G] [MulAction G M] in
/-- Equality of maps out of the arrow object can be checked on every whole action sheet. -/
theorem arrow_hom_ext {F : Sheaf topology Type}
    (f g : object d (ArrowModel (d := d) (G := G) (M := M)) ⟶ F)
    (h : ∀ k : G, map (sheet (d := d) (M := M) k) (sheet_smooth (d := d) (M := M) k) ≫ f =
      map (sheet (d := d) (M := M) k) (sheet_smooth (d := d) (M := M) k) ≫ g) : f = g := by
  apply (cancel_epi (coproductArrowIso (d := d) (G := G) (M := M)).hom).mp
  apply colimit.hom_ext
  rintro ⟨k⟩
  simpa only [← Category.assoc, inclusion_coproductArrowIso] using h k

omit [MulAction G M] in
@[reassoc] theorem arrowIso_source :
    (arrowIso (d := d) (G := G) (M := M)).hom ≫ SheafRelation.snd _ _ =
      map source source_smooth := by
  apply arrow_hom_ext
  intro g
  rw [← Category.assoc, sheet_arrowIso, ← map_comp]
  change 𝟙 (object d M) = map id contMDiff_id
  exact map_id.symm

@[reassoc] theorem arrowIso_target :
    (arrowIso (d := d) (G := G) (M := M)).hom ≫
      (SmoothManifoldAction.representation smoothAction).actionMap = map target (target_smooth smoothAction) := by
  apply arrow_hom_ext
  intro g
  rw [← Category.assoc, sheet_arrowIso, ← map_comp]
  ext U x
  exact (SmoothManifoldAction.representation smoothAction).actionMap_constant U g x



def unit (x : M) : ArrowModel (d := d) (G := G) (M := M) := (1,x)
def inverse (a : ArrowModel (d := d) (G := G) (M := M)) : ArrowModel (d := d) (G := G) (M := M) :=
  (a.1⁻¹,target a)

omit [MulAction G M] in
theorem unit_smooth : ContMDiff (modelWithCorners d) (modelWithCorners d) ∞
    (unit (d := d) (G := G) (M := M)) := sheet_smooth (d := d) (M := M) 1

include smoothAction in
theorem inverse_smooth : ContMDiff (modelWithCorners d) (modelWithCorners d) ∞
    (inverse (d := d) (G := G) (M := M)) :=
  (toModel_smooth (Orbifolds.FiniteActionPresentation.source (G := G) (M := M))
    (source_etale (modelWithCorners d))).comp
      ((Orbifolds.FiniteActionPresentation.inverse_smooth (modelWithCorners d) smoothAction).comp
        (fromModel_smooth _ _))

omit [Group G] [MulAction G M] in
theorem source_etale' : IsLocalDiffeomorph (modelWithCorners d) (modelWithCorners d) ∞
    (source (d := d) (G := G) (M := M)) :=
  projection_localDiffeomorph _ _

theorem composableTransverse : SmoothTransversePullback.Transverse (m := d) (n := d) (p := d)
    (target (d := d) (G := G) (M := M)) (source (d := d) (G := G) (M := M)) := by
  intro q v
  let e := (source_etale' (d := d) (G := G) (M := M) q.val.2).mfderivToContinuousLinearEquiv (by simp)
  let w := SmoothTransversality.tangentTransport q.property (-v)
  refine ⟨(0,e.symm w), ?_⟩
  change (mfderiv (modelWithCorners d) (modelWithCorners d) target q.val.1) 0 -
    SmoothTransversality.tangentTransport q.property.symm
      ((mfderiv (modelWithCorners d) (modelWithCorners d) source q.val.2) (e.symm w)) = v
  change _ - SmoothTransversality.tangentTransport q.property.symm (e (e.symm w)) = v
  rw [e.apply_symm_apply]
  simp only [map_zero, zero_sub]
  have hi {a b : M} (h : a = b) (z : TangentSpace (modelWithCorners d) a) :
      SmoothTransversality.tangentTransport h.symm
        (SmoothTransversality.tangentTransport h z) = z := by
    subst b
    rfl
  rw [show SmoothTransversality.tangentTransport q.property.symm w = -v from
    hi q.property (-v), neg_neg]

abbrev Composable := SmoothTransversePullback.Pullback
  (target (d := d) (G := G) (M := M)) (source (d := d) (G := G) (M := M))

@[instance_reducible] def composableCharts : ChartedSpace (Space (d+d-d)) (Composable (d := d) (G := G) (M := M)) :=
  SmoothTransversePullback.chartedSpace (target_smooth smoothAction) source_smooth composableTransverse

theorem composableManifold : letI := composableCharts smoothAction
    IsManifold (modelWithCorners (d+d-d)) ∞
    (Composable (d := d) (G := G) (M := M)) :=
  SmoothTransversePullback.isManifold (target_smooth smoothAction) source_smooth composableTransverse

abbrev first : Composable (d := d) (G := G) (M := M) → ArrowModel (d := d) (G := G) (M := M) :=
  SmoothTransversePullback.fst
abbrev second : Composable (d := d) (G := G) (M := M) → ArrowModel (d := d) (G := G) (M := M) :=
  SmoothTransversePullback.snd

include smoothAction in
theorem first_smooth : letI := composableCharts smoothAction
    ContMDiff (modelWithCorners (d+d-d)) (modelWithCorners d) ∞
      (first (d := d) (G := G) (M := M)) :=
  SmoothTransversePullback.smooth_fst (target_smooth smoothAction) source_smooth composableTransverse

include smoothAction in
theorem second_smooth : letI := composableCharts smoothAction
    ContMDiff (modelWithCorners (d+d-d)) (modelWithCorners d) ∞
      (second (d := d) (G := G) (M := M)) :=
  SmoothTransversePullback.smooth_snd (target_smooth smoothAction) source_smooth composableTransverse



/-- Composition on the actual equality-subtype of composable arrows. -/
def composition (p : Composable (d := d) (G := G) (M := M)) : ArrowModel (d := d) (G := G) (M := M) :=
  (p.val.2.1 * p.val.1.1, p.val.1.2)

include smoothAction in
theorem composition_smooth : letI := composableCharts smoothAction
    ContMDiff (modelWithCorners (d+d-d)) (modelWithCorners d) ∞
      (composition (d := d) (G := G) (M := M)) := by
  let := composableCharts smoothAction
  have hf := (fromModel_smooth (Orbifolds.FiniteActionPresentation.source (G := G) (M := M))
    (source_etale (modelWithCorners d))).comp (first_smooth smoothAction)
  have hs := (fromModel_smooth (Orbifolds.FiniteActionPresentation.source (G := G) (M := M))
    (source_etale (modelWithCorners d))).comp (second_smooth smoothAction)
  have hc := (Orbifolds.FiniteActionPresentation.compose_smooth (G := G) (M := M)
    (modelWithCorners d)).comp (((contMDiff_fst.comp hf).prodMk
      (contMDiff_fst.comp hs)).prodMk (contMDiff_snd.comp hf))
  exact (toModel_smooth _ _).comp hc

/-- Interpretation preserves the actual composable-arrow object at every stage. -/
theorem realizedComposable_isPullback : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    IsPullback (map (first (d := d) (G := G) (M := M)) (first_smooth smoothAction))
      (map second (second_smooth smoothAction)) (map target (target_smooth smoothAction))
      (map (source (d := d) (G := G) (M := M)) source_smooth) :=
  SmoothTransversePullback.Realization.isPullback
    (target_smooth smoothAction) source_smooth composableTransverse

/-- The canonical all-stage comparison into the categorical pullback. -/
def composableIso : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    object (d+d-d) (Composable (d := d) (G := G) (M := M)) ≅
      pullback (map target (target_smooth smoothAction)) (map (source (d := d) (G := G) (M := M)) source_smooth) :=
  (realizedComposable_isPullback smoothAction).isoPullback

def unitMap : object d M ⟶ object d (ArrowModel (d := d) (G := G) (M := M)) :=
  map unit unit_smooth

def inverseMap : object d (ArrowModel (d := d) (G := G) (M := M)) ⟶
    object d (ArrowModel (d := d) (G := G) (M := M)) := map inverse (inverse_smooth smoothAction)

/-- Multiplication is the interpretation of geometric composition through the proved pullback. -/
def compositionMap : pullback (map target (target_smooth smoothAction))
    (map source (source_smooth (d := d) (G := G) (M := M))) ⟶
      object d (ArrowModel (d := d) (G := G) (M := M)) := by
  letI := composableCharts smoothAction
  letI := composableManifold smoothAction
  exact (composableIso smoothAction).inv ≫ map composition (composition_smooth smoothAction)



omit [Group G] [MulAction G M] in
/-- Continuous discrete labels and a smooth base map give an actual smooth arrow map. -/
theorem pair_smooth {k : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (Space k) N]
    (l : N → G) (x : N → M) (hl : Continuous l)
    (hx : ContMDiff (modelWithCorners k) (modelWithCorners d) ∞ x) :
    ContMDiff (modelWithCorners k) (modelWithCorners d) ∞
      (show N → ArrowModel (d := d) (G := G) (M := M) from fun y => (l y,x y)) :=
  (sheets (Orbifolds.FiniteActionPresentation.source (G := G) (M := M))
    (source_etale (modelWithCorners d))).smooth_of_proj_model _ (hl.prodMk hx.continuous) hx

abbrev PairModel := ArrowModel (d := d) (G := G × G) (M := M)

def pairFirst (p : PairModel (d := d) (G := G) (M := M)) : ArrowModel (d := d) (G := G) (M := M) :=
  (p.1.1,p.2)
def pairSecond (p : PairModel (d := d) (G := G) (M := M)) : ArrowModel (d := d) (G := G) (M := M) :=
  (p.1.2,p.1.1 • p.2)

omit [Group G] [MulAction G M] in
theorem pairFirst_smooth : ContMDiff (modelWithCorners d) (modelWithCorners d) ∞
    (pairFirst (d := d) (G := G) (M := M)) :=
  pair_smooth _ _ (continuous_fst.comp continuous_fst)
    (source_smooth (d := d) (G := G × G) (M := M))

include smoothAction in
theorem pairSecond_smooth : ContMDiff (modelWithCorners d) (modelWithCorners d) ∞
    (pairSecond (d := d) (G := G) (M := M)) :=
  pair_smooth _ _ (continuous_snd.comp continuous_fst)
    ((target_smooth smoothAction).comp pairFirst_smooth)

/-- Product coordinates on composable arrows, with both geometric projections preserved. -/
def pairDiffeomorph : letI := composableCharts smoothAction
    Diffeomorph (modelWithCorners d) (modelWithCorners (d+d-d))
      (PairModel (d := d) (G := G) (M := M)) (Composable (d := d) (G := G) (M := M)) ∞ := by
  letI := composableCharts smoothAction
  refine {
    toFun := fun p => ⟨(pairFirst p,pairSecond p),rfl⟩
    invFun := fun p => ((p.val.1.1,p.val.2.1),p.val.1.2)
    left_inv := fun _ => rfl
    right_inv := fun p => Subtype.ext (Prod.ext rfl (Prod.ext rfl p.property))
    contMDiff_toFun := SmoothTransversePullback.smooth_lift
      (target_smooth smoothAction) source_smooth composableTransverse
      pairFirst pairSecond (fun _ => rfl) pairFirst_smooth (pairSecond_smooth smoothAction)
    contMDiff_invFun := ?_ }
  exact pair_smooth _ _
    (((continuous_fst.comp SmoothTransversePullback.continuous_fst).prodMk
      (continuous_fst.comp SmoothTransversePullback.continuous_snd)))
    (source_smooth.comp (first_smooth smoothAction))

/-- These whole sheets cover the actual composable-arrow manifold. -/
def composableSheet (g h : G) (x : M) : Composable (d := d) (G := G) (M := M) :=
  ⟨((g,x),(h,g • x)),rfl⟩

include smoothAction in
theorem composableSheet_smooth (g h : G) : letI := composableCharts smoothAction
    ContMDiff (modelWithCorners d) (modelWithCorners (d+d-d)) ∞
      (composableSheet (d := d) (M := M) g h) := by
  let := composableCharts smoothAction
  exact (pairDiffeomorph smoothAction).contMDiff.comp (sheet_smooth (d := d) (M := M) (g,h))

/-- All maps out of interpreted composable arrows are determined on the coordinate sheets. -/
theorem composable_hom_ext {F : Sheaf topology Type} : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    ∀ (f g : object (d+d-d) (Composable (d := d) (G := G) (M := M)) ⟶ F),
      (∀ a b : G, map (composableSheet (d := d) (M := M) a b)
        (composableSheet_smooth smoothAction a b) ≫ f =
        map (composableSheet (d := d) (M := M) a b)
          (composableSheet_smooth smoothAction a b) ≫ g) → f = g := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  intro f g h
  apply (cancel_epi (diffeomorphIso (pairDiffeomorph smoothAction)).hom).mp
  apply arrow_hom_ext
  rintro ⟨a,b⟩
  rw [← Category.assoc, ← Category.assoc]
  have he : map (sheet (d := d) (M := M) (a,b)) (sheet_smooth (d := d) (M := M) (a,b)) ≫
      (diffeomorphIso (pairDiffeomorph smoothAction)).hom =
        map (composableSheet (d := d) (M := M) a b) (composableSheet_smooth smoothAction a b) := by
    rw [diffeomorphIso, ← map_comp]
    congr 1
  rw [he]
  exact h a b



omit [MulAction G M] in
@[reassoc] theorem unitMap_arrowIso :
    unitMap (d := d) (G := G) (M := M) ≫ (arrowIso (d := d) (G := G) (M := M)).hom =
      constantInjection G (object d M) 1 := sheet_arrowIso 1

@[reassoc] theorem sheet_inverseMap (g : G) :
    map (sheet (d := d) (M := M) g) (sheet_smooth (d := d) (M := M) g) ≫
      inverseMap smoothAction =
        map (fun x : M => g • x) (smoothAction g) ≫
          map (sheet (d := d) (M := M) g⁻¹) (sheet_smooth (d := d) (M := M) g⁻¹) := by
  rw [inverseMap, ← map_comp, ← map_comp]
  rfl

@[reassoc] theorem composableSheet_first (g h : G) : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    map (composableSheet (d := d) (M := M) g h) (composableSheet_smooth smoothAction g h) ≫
      map first (first_smooth smoothAction) = map (sheet (d := d) (M := M) g) (sheet_smooth (d := d) (M := M) g) := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  rw [← map_comp]
  rfl

@[reassoc] theorem composableSheet_second (g h : G) : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    map (composableSheet (d := d) (M := M) g h) (composableSheet_smooth smoothAction g h) ≫
      map second (second_smooth smoothAction) = map (fun x : M => g • x) (smoothAction g) ≫
        map (sheet (d := d) (M := M) h) (sheet_smooth (d := d) (M := M) h) := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  rw [← map_comp, ← map_comp]
  rfl

@[reassoc] theorem composableSheet_composition (g h : G) : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    map (composableSheet (d := d) (M := M) g h) (composableSheet_smooth smoothAction g h) ≫
      map composition (composition_smooth smoothAction) =
        map (sheet (d := d) (M := M) (h*g)) (sheet_smooth (d := d) (M := M) (h*g)) := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  rw [← map_comp]
  rfl

@[reassoc] theorem composableIso_first : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    (composableIso smoothAction).hom ≫ pullback.fst _ _ =
      map first (first_smooth smoothAction) :=
  (realizedComposable_isPullback smoothAction).isoPullback_hom_fst

@[reassoc] theorem composableIso_second : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    (composableIso smoothAction).hom ≫ pullback.snd _ _ =
      map second (second_smooth smoothAction) :=
  (realizedComposable_isPullback smoothAction).isoPullback_hom_snd

@[reassoc] theorem composableIso_compositionMap : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    (composableIso smoothAction).hom ≫ compositionMap smoothAction =
      map composition (composition_smooth smoothAction) := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  exact Iso.hom_inv_id_assoc _ _



include smoothAction in
theorem target_etale' : IsLocalDiffeomorph (modelWithCorners d) (modelWithCorners d) ∞
    (target (d := d) (G := G) (M := M)) := by
  intro a
  exact ((diffeomorph (Orbifolds.FiniteActionPresentation.source (G := G) (M := M))
    (source_etale (modelWithCorners d))).symm.isLocalDiffeomorph a).comp (modelWithCorners d) M
      (target_etale (modelWithCorners d) smoothAction a)

include smoothAction in
/-- Properness and étaleness apply to the same arrow model used by interpretation. -/
theorem proper_etale [Finite G] [T2Space M] :
    IsProperMap (fun a : ArrowModel (d := d) (G := G) (M := M) => (source a,target a)) ∧
      IsLocalDiffeomorph (modelWithCorners d) (modelWithCorners d) ∞
        (source (d := d) (G := G) (M := M)) ∧
      IsLocalDiffeomorph (modelWithCorners d) (modelWithCorners d) ∞
        (target (d := d) (G := G) (M := M)) :=
  ⟨anchor_proper_of_compact (target_etale (modelWithCorners d) smoothAction).contMDiff.continuous,
    source_etale', target_etale' smoothAction⟩



abbrev action := (SmoothManifoldAction.representation smoothAction).action

/-- The reusable presentation retains actual geometric arrows. -/
def groupoid : SheafGroupoid topology where
  toOperations := (SheafGroupoidAction.operations (action smoothAction)).changeArrows
    (arrowIso (d := d) (G := G) (M := M))
  lawful := SheafGroupoid.Operations.changeArrows_laws _ _

@[simp] theorem groupoid_source : (groupoid smoothAction).source = map source source_smooth :=
  arrowIso_source

@[simp] theorem groupoid_target : (groupoid smoothAction).target = map target (target_smooth smoothAction) :=
  arrowIso_target smoothAction

@[simp] theorem groupoid_unit : (groupoid smoothAction).unit = unitMap (d := d) (G := G) (M := M) := by
  apply (cancel_mono (arrowIso (d := d) (G := G) (M := M)).hom).mp
  change (SheafGroupoidAction.unit ≫ (arrowIso (d := d) (G := G) (M := M)).inv) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, unitMap_arrowIso]
  ext U x
  exact Prod.ext (((constantLabel G).app U).hom.map_one.symm) rfl

@[reassoc] theorem inverseMap_arrowIso :
    inverseMap smoothAction ≫ (arrowIso (d := d) (G := G) (M := M)).hom =
      (arrowIso (d := d) (G := G) (M := M)).hom ≫
        SheafGroupoidAction.inverse (action smoothAction) := by
  apply arrow_hom_ext
  intro g
  rw [← Category.assoc, sheet_inverseMap, Category.assoc, sheet_arrowIso,
    ← Category.assoc, sheet_arrowIso]
  ext U x
  apply Prod.ext
  · exact ((constantLabel G).app U).hom.map_inv g
  · exact ((SmoothManifoldAction.representation smoothAction).actionMap_constant U g x).symm

@[simp] theorem groupoid_inverse : (groupoid smoothAction).inverse = inverseMap smoothAction := by
  apply (cancel_mono (arrowIso (d := d) (G := G) (M := M)).hom).mp
  change (_ ≫ _ ≫ (arrowIso (d := d) (G := G) (M := M)).inv) ≫ _ = _
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using (inverseMap_arrowIso smoothAction).symm

/-- The map of composable-arrow pullbacks remembers the same two arrows in action coordinates. -/
def arrowPairMap : pullback (map target (target_smooth smoothAction))
    (map (source (d := d) (G := G) (M := M)) source_smooth) ⟶
      pullback (SheafGroupoidAction.target (action smoothAction))
        (SheafGroupoidAction.source (G := locallyConstantGroup G)) :=
  pullback.lift (pullback.fst _ _ ≫ (arrowIso (d := d) (G := G) (M := M)).hom)
    (pullback.snd _ _ ≫ (arrowIso (d := d) (G := G) (M := M)).hom) (by
      have ht : (arrowIso (d := d) (G := G) (M := M)).hom ≫
          SheafGroupoidAction.target (action smoothAction) = map target (target_smooth smoothAction) :=
        arrowIso_target smoothAction
      rw [Category.assoc, Category.assoc, arrowIso_source, ht]
      exact pullback.condition)

@[reassoc] theorem arrowPairMap_first : arrowPairMap smoothAction ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ (arrowIso (d := d) (G := G) (M := M)).hom := pullback.lift_fst _ _ _
@[reassoc] theorem arrowPairMap_second : arrowPairMap smoothAction ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ (arrowIso (d := d) (G := G) (M := M)).hom := pullback.lift_snd _ _ _



/-- Interpreted geometric composition has the actual action multiplication order. -/
@[reassoc] theorem compositionMap_arrowIso :
    compositionMap smoothAction ≫ (arrowIso (d := d) (G := G) (M := M)).hom =
      arrowPairMap smoothAction ≫ SheafGroupoidAction.comp (action smoothAction) := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  apply (cancel_epi (composableIso smoothAction).hom).mp
  apply composable_hom_ext smoothAction
  intro g h
  simp only [composableIso_compositionMap_assoc]
  rw [← Category.assoc, composableSheet_composition, sheet_arrowIso]
  let f := map (composableSheet (d := d) (M := M) g h) (composableSheet_smooth smoothAction g h) ≫
    (composableIso smoothAction).hom ≫ arrowPairMap smoothAction
  have hf : f ≫ pullback.fst _ _ = constantInjection G (object d M) g := by
    dsimp only [f]
    rw [Category.assoc, Category.assoc, arrowPairMap_first,
      ← Category.assoc ((composableIso smoothAction).hom), composableIso_first,
      ← Category.assoc, composableSheet_first, sheet_arrowIso]
  have hs : f ≫ pullback.snd _ _ =
      map (fun x : M => g • x) (smoothAction g) ≫ constantInjection G (object d M) h := by
    dsimp only [f]
    rw [Category.assoc, Category.assoc, arrowPairMap_second,
      ← Category.assoc ((composableIso smoothAction).hom), composableIso_second,
      ← Category.assoc, composableSheet_second, Category.assoc, sheet_arrowIso]
  change constantInjection G (object d M) (h*g) = f ≫ SheafGroupoidAction.comp (action smoothAction)
  ext U x
  have hf' := congrArg (fun k => k.hom.app U x) hf
  have hs' := congrArg (fun k => k.hom.app U x) hs
  change (pullback.fst (SheafGroupoidAction.target (action smoothAction))
    (SheafGroupoidAction.source (G := locallyConstantGroup G))).hom.app U (f.hom.app U x) =
    ((constantLabel G).app U g,x) at hf'
  change (pullback.snd (SheafGroupoidAction.target (action smoothAction))
    (SheafGroupoidAction.source (G := locallyConstantGroup G))).hom.app U (f.hom.app U x) =
    ((constantLabel G).app U h,_) at hs'
  change ((constantLabel G).app U (h*g),x) =
    ((show (locallyConstantGroup G).obj.obj U from
      ((pullback.snd (SheafGroupoidAction.target (action smoothAction))
        (SheafGroupoidAction.source (G := locallyConstantGroup G))).hom.app U (f.hom.app U x)).1) *
      (show (locallyConstantGroup G).obj.obj U from
        ((pullback.fst (SheafGroupoidAction.target (action smoothAction))
          (SheafGroupoidAction.source (G := locallyConstantGroup G))).hom.app U (f.hom.app U x)).1),
      ((pullback.fst (SheafGroupoidAction.target (action smoothAction))
    (SheafGroupoidAction.source (G := locallyConstantGroup G))).hom.app U (f.hom.app U x)).2)
  rw [hf', hs']
  exact Prod.ext (((constantLabel G).app U).hom.map_mul h g) rfl

/-- The geometric pullback also supplies the composition domain for the public presentation. -/
theorem groupoid_composable_isPullback : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    IsPullback (map first (first_smooth smoothAction)) (map second (second_smooth smoothAction))
      (groupoid smoothAction).target (groupoid smoothAction).source := by
  rw [groupoid_target, groupoid_source]
  exact realizedComposable_isPullback smoothAction

/-- The public groupoid operation agrees with composition on actual composable arrows. -/
@[reassoc] theorem groupoid_composition : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    (groupoid_composable_isPullback smoothAction).isoPullback.hom ≫ (groupoid smoothAction).comp =
      map composition (composition_smooth smoothAction) := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  apply (cancel_mono (arrowIso (d := d) (G := G) (M := M)).hom).mp
  have he : (groupoid_composable_isPullback smoothAction).isoPullback.hom ≫
      pullback.lift
        (pullback.fst (groupoid smoothAction).target (groupoid smoothAction).source ≫
          (arrowIso (d := d) (G := G) (M := M)).hom)
        (pullback.snd (groupoid smoothAction).target (groupoid smoothAction).source ≫
          (arrowIso (d := d) (G := G) (M := M)).hom)
        (by simpa only [groupoid, SheafGroupoid.Operations.changeArrows,
          SheafGroupoidAction.operations, Category.assoc] using
          pullback.condition (f := (groupoid smoothAction).target) (g := (groupoid smoothAction).source)) =
      (composableIso smoothAction).hom ≫ arrowPairMap smoothAction := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst,
        IsPullback.isoPullback_hom_fst_assoc, arrowPairMap_first, composableIso_first_assoc]
    · simp only [Category.assoc, pullback.lift_snd,
        IsPullback.isoPullback_hom_snd_assoc, arrowPairMap_second, composableIso_second_assoc]
  change (_ ≫ (_ ≫ SheafGroupoidAction.comp (action smoothAction) ≫
    (arrowIso (d := d) (G := G) (M := M)).inv)) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [groupoid, SheafGroupoid.Operations.changeArrows, SheafGroupoidAction.operations] at he
  rw [← Category.assoc, he, Category.assoc, ← compositionMap_arrowIso,
    ← Category.assoc, composableIso_compositionMap]



/-- The public operation composes `g` first and `h` second on whole geometric sheets. -/
@[reassoc] theorem groupoid_compose_sheets (g h : G) : letI := composableCharts smoothAction
    letI := composableManifold smoothAction
    map (composableSheet (d := d) (M := M) g h) (composableSheet_smooth smoothAction g h) ≫
      (groupoid_composable_isPullback smoothAction).isoPullback.hom ≫
        (groupoid smoothAction).comp =
          map (sheet (d := d) (M := M) (h*g)) (sheet_smooth (d := d) (M := M) (h*g)) := by
  let := composableCharts smoothAction
  let := composableManifold smoothAction
  rw [groupoid_composition, composableSheet_composition]

end Geometry
end SquareKit.SmoothActionGroupoid
