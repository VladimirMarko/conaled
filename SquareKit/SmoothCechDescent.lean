import SquareKit.SmoothCechData
import SquareKit.SheafActionQuotientCechEquivalence
import SquareKit.SheafActionQuotientDescentDisplay

/-! Interpretation of independent smooth Čech data on represented covers. -/
noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
open SmoothRepresentedCover SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))

/-- Pointwise multiplication of sheaf labels preserves their naturality. -/
def labelMul {Y : Sheaf topology Type}
    (g h : Y ⟶ locallyConstantGroupSheaf G) : Y ⟶ locallyConstantGroupSheaf G :=
  SheafTorsor.labelMul g h

def labelOne (Y : Sheaf topology Type) : Y ⟶ locallyConstantGroupSheaf G :=
  SheafTorsor.labelOne Y

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem labelMul_precomp {Y Z : Sheaf topology Type} (f : Z ⟶ Y)
    (g h : Y ⟶ locallyConstantGroupSheaf G) :
    f ≫ labelMul g h = labelMul (f ≫ g) (f ≫ h) := rfl

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem labelOne_precomp {Y Z : Sheaf topology Type} (f : Z ⟶ Y) :
    f ≫ labelOne (G := G) Y = labelOne Z := rfl

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem ordinary_labelMul {U : Domain} (g h : embedding.obj U ⟶ locallyConstantGroupSheaf G)
    (x : Points U) : ordinaryHomLabelEquiv G U (labelMul g h) x =
      ordinaryHomLabelEquiv G U g x * ordinaryHomLabelEquiv G U h x :=
  ordinaryLabel_mul G U _ _ x

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem ordinary_labelOne (U : Domain) (x : Points U) :
    ordinaryHomLabelEquiv G U (labelOne (embedding.obj U)) x = 1 := by
  change ordinaryLabel G U (1 : (locallyConstantGroup G).obj.obj (op (toSite.obj U))) x = 1
  rw [← ((constantLabel G).app _).hom.map_one]
  exact ordinaryLabel_constant G U 1 x

namespace Datum
variable (p : Datum (d := d) (G := G) (M := M) A)

/-- The local smooth maps assemble on the actual sheaf coproduct of charts. -/
def localMapSheaf : A.total ⟶ object d M :=
  SheafCoproductLocal.desc A.family (fun i => hat (p.localMap i).val (p.localMap i).property)

omit [TopologicalSpace G] [DiscreteTopology G] in
@[simp, reassoc] theorem localMapSheaf_fac (i : I) :
    A.inclusion i ≫ p.localMapSheaf = hat (p.localMap i).val (p.localMap i).property :=
  SheafCoproductLocal.inclusion_desc _ _ _

/-- Forward external labels become the complete regular-torsor transition arrow. -/
def transitionArrow (i j : I) :=
  (External.chartLabelsEquiv smoothAction
    ((p.localMap i).restrict (A.left i j))
    ((p.localMap j).restrict (A.right i j))).symm (p.transition i j)

/-- The regular-torsor coordinate is the inverse of the forward action label. -/
def overlapLabel : SheafCoverCech.double A.cover ⟶ locallyConstantGroupSheaf G :=
  A.pairHom (fun i j => arrowLabel (p.transitionArrow smoothAction i j))

omit [TopologicalSpace G] [DiscreteTopology G] in
@[simp, reassoc] theorem overlapLabel_fac (i j : I) :
    A.pairMap i j ≫ p.overlapLabel smoothAction =
      arrowLabel (p.transitionArrow smoothAction i j) := A.pairHom_fac _ i j

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- Pulling back an action equation preserves its complete sheaf maps. -/
theorem onMap_precomp {Y Z : Sheaf topology Type}
    (f : Z ⟶ Y) (g : Y ⟶ locallyConstantGroupSheaf G) (m : Y ⟶ object d M) :
    f ≫ (representation smoothAction).action.onMap g m =
      (representation smoothAction).action.onMap (f ≫ g) (f ≫ m) := rfl

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- Local endpoint equations glue to the actual overlap endpoint equation. -/
theorem overlapLabel_relation :
    (representation smoothAction).action.onMap (p.overlapLabel smoothAction)
      (SheafCoverCech.second A.cover ≫ p.localMapSheaf) =
        SheafCoverCech.first A.cover ≫ p.localMapSheaf := by
  apply A.pairHom_ext
  intro i j
  rw [onMap_precomp]
  simp only [overlapLabel_fac, A.pairMap_second_assoc, A.pairMap_first_assoc,
    localMapSheaf_fac]
  rw [External.hat_restrict, External.hat_restrict]
  exact arrowLabel_relation (p.transitionArrow smoothAction i j)

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- Actual right-translation labels are recovered from the supplied forward labels. -/
theorem transitionArrow_label (i j : I) (x : Points (A.pair i j)) :
    ordinaryHomLabelEquiv G (A.pair i j) (arrowLabel (p.transitionArrow smoothAction i j)) x =
      ((p.transition i j).val x)⁻¹ := by
  have h := congrArg (fun z => z.val x)
    ((External.chartLabelsEquiv smoothAction
      ((p.localMap i).restrict (A.left i j))
      ((p.localMap j).restrict (A.right i j))).apply_symm_apply (p.transition i j))
  change (ordinaryHomLabelEquiv G (A.pair i j)
    (arrowLabel (p.transitionArrow smoothAction i j)) x)⁻¹ = _ at h
  exact inv_eq_iff_eq_inv.mp h

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem overlapLabel_diagonal :
    SheafCoverCech.diagonal A.cover ≫ p.overlapLabel smoothAction = labelOne A.total := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ (SheafCoverCech.diagonal A.cover ≫ p.overlapLabel smoothAction) = _
  rw [← Category.assoc, ← A.diagonal_pairMap, Category.assoc, overlapLabel_fac]
  apply (ordinaryHomLabelEquiv G (A.domain i)).injective
  apply LocallyConstant.ext
  intro x
  rw [ordinaryHomLabelEquiv_natural, transitionArrow_label]
  change ((p.transition i i).val ((show EuclideanOpen.Map _ _ from A.diagonal i) x))⁻¹ =
    ordinaryHomLabelEquiv G (A.domain i) (labelOne _) x
  rw [p.diagonal, inv_one, ordinary_labelOne]

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem overlapLabel_cocycle :
    SheafCoverCech.firstThird A.cover ≫ p.overlapLabel smoothAction =
      labelMul (SheafCoverCech.firstSecond A.cover ≫ p.overlapLabel smoothAction)
        (SheafCoverCech.secondThird A.cover ≫ p.overlapLabel smoothAction) := by
  apply A.tripleHom_ext
  intro i j k
  rw [labelMul_precomp]
  simp only [A.tripleMap_firstThird_assoc, A.tripleMap_firstSecond_assoc,
    A.tripleMap_secondThird_assoc, overlapLabel_fac]
  apply (ordinaryHomLabelEquiv G (A.triple i j k)).injective
  apply LocallyConstant.ext
  intro x
  rw [ordinary_labelMul, ordinaryHomLabelEquiv_natural, ordinaryHomLabelEquiv_natural,
    ordinaryHomLabelEquiv_natural, transitionArrow_label, transitionArrow_label,
    transitionArrow_label, p.cocycle, mul_inv_rev]

/-- The selected split display merely re-expresses the actual cover. -/
def splitLocalMap : SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover) ⟶ object d M :=
  (SplitSheaf.displayIso A.cover).hom ≫ p.localMapSheaf

def splitLabel : SplitSheaf.Cech.double (SplitSheaf.ofDisplay A.cover) ⟶
    locallyConstantGroupSheaf G :=
  (SheafCoverCech.splitDoubleIso A.cover).hom ≫ p.overlapLabel smoothAction

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem splitLabel_relation :
    (representation smoothAction).action.onMap (p.splitLabel smoothAction)
      (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫ p.splitLocalMap) =
        SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫ p.splitLocalMap := by
  have h := congrArg (fun f => (SheafCoverCech.splitDoubleIso A.cover).hom ≫ f)
    (p.overlapLabel_relation smoothAction)
  simp only [onMap_precomp, ← Category.assoc, SheafCoverCech.splitDouble_first,
    SheafCoverCech.splitDouble_second] at h
  simpa only [splitLabel, splitLocalMap, Category.assoc] using h

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem splitLabel_diagonal :
    SplitSheaf.Cech.diagonal (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction =
      labelOne (SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover)) := by
  unfold splitLabel
  rw [← Category.assoc, SheafCoverCech.splitDouble_diagonal, Category.assoc,
    overlapLabel_diagonal, labelOne_precomp]

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem splitLabel_cocycle :
    SplitSheaf.Cech.firstThird (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction =
      labelMul (SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction)
        (SplitSheaf.Cech.secondThird (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction) := by
  have h := congrArg (fun f => (SheafCoverCech.splitTripleIso A.cover).hom ≫ f)
    (p.overlapLabel_cocycle smoothAction)
  simp only [labelMul_precomp, ← Category.assoc, SheafCoverCech.splitTriple_firstThird,
    SheafCoverCech.splitTriple_firstSecond, SheafCoverCech.splitTriple_secondThird] at h
  simpa only [splitLabel, Category.assoc] using h

/-- The ordinary cocycle supplies actual quotient Čech descent data. -/
def cech : SheafActionQuotient.Cech.Datum (a := (representation smoothAction).action)
    (SplitSheaf.ofDisplay A.cover) where
  localObject := chart (representation smoothAction).action p.splitLocalMap
  overlap := (chartArrowOfRelation (p.splitLabel smoothAction)
    (SplitSheaf.Cech.first _ ≫ p.splitLocalMap)
    (SplitSheaf.Cech.second _ ≫ p.splitLocalMap) (p.splitLabel_relation smoothAction)).toIso
  diagonal := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x z
    change (locallyConstantGroup G).obj.obj x.obj at z
    change z * (show (locallyConstantGroup G).obj.obj x.obj from
      (SplitSheaf.Cech.diagonal (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction).hom.app x.obj x.val) = z
    rw [p.splitLabel_diagonal smoothAction]
    exact mul_one z
  cocycle := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x z
    change (locallyConstantGroup G).obj.obj x.obj at z
    change (z * (show (locallyConstantGroup G).obj.obj x.obj from
      (SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction).hom.app x.obj x.val)) *
      (show (locallyConstantGroup G).obj.obj x.obj from
      (SplitSheaf.Cech.secondThird (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction).hom.app x.obj x.val) =
      z * (show (locallyConstantGroup G).obj.obj x.obj from
      (SplitSheaf.Cech.firstThird (SplitSheaf.ofDisplay A.cover) ≫ p.splitLabel smoothAction).hom.app x.obj x.val)
    rw [p.splitLabel_cocycle smoothAction]
    exact mul_assoc _ _ _

/-- Effective descent is reused after the represented-cover adapter. -/
def interpreted : Object (representation smoothAction).action X :=
  (Descent.displayDescentEquivalence (representation smoothAction).action A.cover).functor.obj
    (p.cech smoothAction).toDescent

end Datum
end SquareKit.SmoothCech
