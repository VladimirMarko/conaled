import SquareKit.SmoothCechComparison

/-! Extract ordinary smooth cocycles from regular sheaf coordinates. -/
noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
open SmoothRepresentedCover SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

abbrev assembledMap (m : ∀ i, External.SmoothMap (A.domain i) d M) :=
  SheafCoproductLocal.desc A.family (fun i => hat (m i).val (m i).property)

/-- Coordinates on regular sheaf Čech transport. Its laws concern actual maps
on actual pullbacks, before reconstruction of ordinary transition families. -/
structure RegularLabels (m : ∀ i, External.SmoothMap (A.domain i) d M) where
  label : SheafCoverCech.double A.cover ⟶ locallyConstantGroupSheaf G
  relation : (representation smoothAction).action.onMap label
    (SheafCoverCech.second A.cover ≫ assembledMap m) =
      SheafCoverCech.first A.cover ≫ assembledMap m
  diagonal : SheafCoverCech.diagonal A.cover ≫ label = labelOne A.total
  cocycle : SheafCoverCech.firstThird A.cover ≫ label =
    labelMul (SheafCoverCech.firstSecond A.cover ≫ label)
      (SheafCoverCech.secondThird A.cover ≫ label)

namespace RegularLabels
variable {m : ∀ i, External.SmoothMap (A.domain i) d M}
variable (k : RegularLabels smoothAction m)

def transitionArrow (i j : I) : External.ChartArrow smoothAction
    ((m i).restrict (A.left i j)) ((m j).restrict (A.right i j)) :=
  chartArrowOfRelation (A.pairMap i j ≫ k.label) _ _ (by
    have h := congrArg (fun h => A.pairMap i j ≫ h) k.relation
    simp only [Datum.onMap_precomp, A.pairMap_first_assoc, A.pairMap_second_assoc] at h
    simpa only [assembledMap, SheafCoproductLocal.inclusion_desc, External.hat_restrict] using h)

def transition (i j : I) := External.chartLabelsEquiv smoothAction
    ((m i).restrict (A.left i j)) ((m j).restrict (A.right i j))
    (k.transitionArrow smoothAction i j)

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem transition_apply (i j : I) (x : Points (A.pair i j)) :
    (k.transition smoothAction i j).val x =
      (ordinaryHomLabelEquiv G (A.pair i j) (A.pairMap i j ≫ k.label) x)⁻¹ := by
  change (ordinaryHomLabelEquiv G (A.pair i j)
    (arrowLabel (k.transitionArrow smoothAction i j)) x)⁻¹ = _
  apply congrArg Inv.inv
  apply congrArg (fun h => ordinaryHomLabelEquiv G (A.pair i j) h x)
  ext U x
  exact one_mul (show (locallyConstantGroup G).obj.obj U from (A.pairMap i j ≫ k.label).hom.app U x)

def datum : Datum (d := d) (G := G) (M := M) A where
  localMap := m
  transition := k.transition smoothAction
  diagonal i x := by
    rw [transition_apply, ← ordinaryHomLabelEquiv_natural]
    rw [← Category.assoc, A.diagonal_pairMap, Category.assoc, k.diagonal, labelOne_precomp,
      ordinary_labelOne, inv_one]
  cocycle i j l x := by
    simp only [transition_apply, ← ordinaryHomLabelEquiv_natural]
    have h := congrArg (fun h => A.tripleMap i j l ≫ h) k.cocycle
    simp only [labelMul_precomp, A.tripleMap_firstThird_assoc, A.tripleMap_firstSecond_assoc,
      A.tripleMap_secondThird_assoc] at h
    have he := congrArg (fun h => ordinaryHomLabelEquiv G (A.triple i j l) h x) h
    rw [ordinary_labelMul] at he
    simpa only [mul_inv_rev] using congrArg Inv.inv he

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem datum_label : (k.datum smoothAction).overlapLabel smoothAction = k.label := by
  apply A.pairHom_ext
  intro i j
  rw [Datum.overlapLabel_fac]
  apply (ordinaryHomLabelEquiv G (A.pair i j)).injective
  apply LocallyConstant.ext
  intro x
  rw [Datum.transitionArrow_label]
  change ((k.transition smoothAction i j).val x)⁻¹ = _
  rw [transition_apply, inv_inv]

/-- Reconstruct regular coordinates from an actual Čech datum whose local
object has the stated regular presentation. The overlap laws are derived. -/
def fromCech (c : SheafActionQuotient.Cech.Datum
    (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover))
    (hm : c.localObject = chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) : RegularLabels smoothAction m := by
  rcases c with ⟨Q,e,hd,hc⟩
  cases hm
  change chart (representation smoothAction).action
    (SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) ≅
    chart (representation smoothAction).action
    (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) at e
  let r := arrowLabel e.hom
  have hr : (representation smoothAction).action.onMap r
      (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫
        ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) =
      SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫
        ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m) := arrowLabel_relation e.hom
  have hid : SplitSheaf.Cech.diagonal (SplitSheaf.ofDisplay A.cover) ≫ r =
      labelOne (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)) := by
    ext U x
    exact congrArg (fun a => a.torsorArrow.iso.hom.app
      ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U x)
      (1 : (locallyConstantGroup G).obj.obj U)) hd
  have hcomp : SplitSheaf.Cech.firstThird (SplitSheaf.ofDisplay A.cover) ≫ r =
      labelMul (SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay A.cover) ≫ r)
        (SplitSheaf.Cech.secondThird (SplitSheaf.ofDisplay A.cover) ≫ r) := by
    ext U x
    have hh := congrArg (fun a : SheafActionQuotient.Arrow
      (chart (representation smoothAction).action
        (SplitSheaf.Cech.firstThird (SplitSheaf.ofDisplay A.cover) ≫
          SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫
          (SplitSheaf.displayIso A.cover).hom ≫ assembledMap m))
      (chart (representation smoothAction).action
        (SplitSheaf.Cech.firstThird (SplitSheaf.ofDisplay A.cover) ≫
          SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫
          (SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) =>
      (arrowLabel a).hom.app U x) hc
    have he := e.hom.torsorArrow.equivariant
      ((SplitSheaf.Cech.double (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U
        ((SplitSheaf.Cech.secondThird (SplitSheaf.ofDisplay A.cover)).hom.app U x))
      (show (locallyConstantGroup G).obj.obj U from
        r.hom.app U ((SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay A.cover)).hom.app U x))
      (1 : (locallyConstantGroup G).obj.obj U)
    change e.hom.torsorArrow.iso.hom.app
      ((SplitSheaf.Cech.double (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U
        ((SplitSheaf.Cech.secondThird (SplitSheaf.ofDisplay A.cover)).hom.app U x))
      ((show (locallyConstantGroup G).obj.obj U from
        r.hom.app U ((SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay A.cover)).hom.app U x)) * 1) =
      (show (locallyConstantGroup G).obj.obj U from
        r.hom.app U ((SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay A.cover)).hom.app U x)) *
      (show (locallyConstantGroup G).obj.obj U from
        r.hom.app U ((SplitSheaf.Cech.secondThird (SplitSheaf.ofDisplay A.cover)).hom.app U x)) at he
    erw [mul_one] at he
    exact hh.symm.trans he
  refine { label := (SheafCoverCech.splitDoubleIso A.cover).inv ≫ r
           relation := ?_, diagonal := ?_, cocycle := ?_ }
  · apply (cancel_epi (SheafCoverCech.splitDoubleIso A.cover).hom).mp
    simp only [Datum.onMap_precomp, Iso.hom_inv_id_assoc]
    simpa only [SheafCoverCech.splitDoubleIso_first_assoc,
      SheafCoverCech.splitDoubleIso_second_assoc] using hr
  · apply (cancel_epi (SplitSheaf.displayIso A.cover).hom).mp
    rw [← Category.assoc, ← SheafCoverCech.splitDoubleIso_diagonal,
      Category.assoc, Iso.hom_inv_id_assoc, hid, labelOne_precomp]
  · apply (cancel_epi (SheafCoverCech.splitTripleIso A.cover).hom).mp
    simp only [labelMul_precomp, ← Category.assoc, SheafCoverCech.splitTripleIso_firstThird,
      SheafCoverCech.splitTripleIso_firstSecond, SheafCoverCech.splitTripleIso_secondThird]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hcomp

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- Reconstruction retains the complete chosen Čech record. -/
theorem fromCech_roundtrip (c : SheafActionQuotient.Cech.Datum
    (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover))
    (hm : c.localObject = chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) :
    ((fromCech smoothAction c hm).datum smoothAction).cech smoothAction = c := by
  rcases c with ⟨Q,e,hd,hc⟩
  cases hm
  change chart (representation smoothAction).action
    (SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) ≅
    chart (representation smoothAction).action
    (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m)) at e
  have hl := (fromCech smoothAction ⟨chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m),e,hd,hc⟩ rfl).datum_label smoothAction
  unfold Datum.cech
  congr 1
  apply CategoryTheory.Iso.ext
  dsimp only [SheafActionQuotient.Arrow.toIso]
  have hs : ((fromCech smoothAction ⟨chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m),e,hd,hc⟩ rfl).datum smoothAction).splitLabel smoothAction =
      arrowLabel e.hom := by
    unfold Datum.splitLabel
    rw [hl]
    change (SheafCoverCech.splitDoubleIso A.cover).hom ≫
      ((SheafCoverCech.splitDoubleIso A.cover).inv ≫ arrowLabel e.hom) = _
    exact Iso.hom_inv_id_assoc _ _
  apply (chartArrowEquiv
    (SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m))
    (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m))).injective
  apply Subtype.ext
  refine Eq.trans ?_ hs
  ext U x
  exact one_mul (show (locallyConstantGroup G).obj.obj U from
    (((fromCech smoothAction ⟨chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap m),e,hd,hc⟩ rfl).datum smoothAction).splitLabel smoothAction).hom.app U x)

end RegularLabels
end SquareKit.SmoothCech
