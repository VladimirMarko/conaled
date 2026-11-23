import SquareKit.SmoothBundleMapsRealization
import SquareKit.SheafTorsorReindexMaps
import Mathlib.CategoryTheory.HomCongr

/-! Complete ordinary target-preserving bundle maps and their quotient arrows,
on the preferred realization of the common base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothPrincipalBundle
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n d : ℕ} {G B E E' M : Type} [Group G]
  [MulAction G E] [MulAction G E'] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [ChartedSpace (Space d) M]
  [IsManifold (Model n) ∞ B] [IsManifold (Model n) ∞ E]
  [IsManifold (Model n) ∞ E'] [IsManifold (Model d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))

namespace Bundle
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (F : E → M) (hF : ContMDiff (Model n) (Model d) ∞ F)
  (hG : ∀ (g : G) e, F (g • e) = g • F e)

/-- Normalize the existing quotient object onto the preferred base realization. -/
def realizedQuotient : SheafActionQuotient.Object (representation smoothAction).action (object n B) :=
  SheafActionQuotient.reindex (P.quotientObject smoothAction F hF hG)
    (atlasIso P.baseCharts).hom

theorem realizedQuotient_totalMap :
    (P.realizedQuotient smoothAction F hF hG).totalMap =
      P.realizedTotalIso.hom ≫ ManifoldRealization.map F hF := by
  change (SheafActionQuotient.reindex (P.quotientObject smoothAction F hF hG)
    (atlasIso P.baseCharts).hom).totalMap = _
  rw [SheafActionQuotient.reindex_totalMap, P.quotientObject_totalMap]
  rfl

theorem realizedQuotient_chart (A : ChartFamily n B) :
    SheafActionQuotient.reindex (P.realizedQuotient smoothAction F hF hG) (atlasIso A).inv =
      SheafActionQuotient.reindex (P.quotientObject smoothAction F hF hG)
        (A.comparison P.baseCharts).hom := by
  change SheafActionQuotient.reindex (P.quotientObject smoothAction F hF hG)
    ((atlasIso A).inv ≫ (atlasIso P.baseCharts).hom) = _
  have he : (atlasIso A).inv ≫ (atlasIso P.baseCharts).hom =
      (A.comparison P.baseCharts).hom :=
    congrArg Iso.hom (A.comparison_trans .preferred P.baseCharts)
  rw [he]

theorem realizedQuotient_original :
    SheafActionQuotient.reindex (P.realizedQuotient smoothAction F hF hG)
      (atlasIso P.baseCharts).inv = P.quotientObject smoothAction F hF hG := by
  rw [P.realizedQuotient_chart, ChartFamily.comparison_refl]
  rfl

end Bundle

variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}
  {F : E → M} {F' : E' → M}
  (hF : ContMDiff (Model n) (Model d) ∞ F)
  (hF' : ContMDiff (Model n) (Model d) ∞ F')
  (hG : ∀ (g : G) e, F (g • e) = g • F e)
  (hG' : ∀ (g : G) e, F' (g • e) = g • F' e)

namespace TargetMap
variable (f : TargetMap P Q F F')

/-- Target preservation of the derived inverse follows from the original map. -/
def inverse : TargetMap Q P F' F where
  toMap := f.toMap.inverse
  target e := by
    have he := f.target (f.toMap.inverse.toFun e)
    rw [f.toMap.apply_inverse_apply] at he
    exact he.symm

omit [MulAction G M] [TopologicalSpace M] in
@[simp] theorem comp_inverse : f.comp f.inverse = TargetMap.ident P F :=
  TargetMap.ext _ _ f.toMap.comp_inverse

omit [MulAction G M] [TopologicalSpace M] in
@[simp] theorem inverse_comp : f.inverse.comp f = TargetMap.ident Q F' :=
  TargetMap.ext _ _ f.toMap.inverse_comp

def realizedArrow : SheafActionQuotient.Arrow
    (P.realizedQuotient smoothAction F hF hG)
    (Q.realizedQuotient smoothAction F' hF' hG') where
  torsorArrow := f.toMap.realizedArrow
  preserves := by
    apply (SheafActionQuotient.preserves_iff_totalMap _).mpr
    rw [P.realizedQuotient_totalMap, Q.realizedQuotient_totalMap]
    change SplitSheaf.totalMap f.toMap.realizedFiberMap ≫ _ = _
    rw [Map.realizedFiberMap_total]
    simp only [Map.realizedTotalMap, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← ManifoldRealization.map_comp]
    have he : F' ∘ f.toFun = F := funext f.target
    simp only [he]

theorem realizedArrow_inverse :
    f.inverse.realizedArrow smoothAction hF' hF hG' hG =
      (f.realizedArrow smoothAction hF hF' hG hG').inverse := by
  apply SheafActionQuotient.Arrow.ext
  exact f.toMap.realizedArrow_inverse

theorem realizedArrow_ident :
    (TargetMap.ident P F).realizedArrow smoothAction hF hF hG hG =
      SheafActionQuotient.Arrow.ident (P.realizedQuotient smoothAction F hF hG) := by
  apply SheafActionQuotient.Arrow.ext
  exact Map.realizedArrow_ident

variable {E'' : Type} [MulAction G E''] [TopologicalSpace E'']
  [ChartedSpace (Space n) E''] [IsManifold (Model n) ∞ E'']
  {R : Bundle (n := n) (G := G) (B := B) (E := E'')}
  {F'' : E'' → M}

theorem realizedArrow_comp (hF'' : ContMDiff (Model n) (Model d) ∞ F'')
    (hG'' : ∀ (g : G) e, F'' (g • e) = g • F'' e) (g : TargetMap Q R F' F'') :
    (f.comp g).realizedArrow smoothAction hF hF'' hG hG'' =
      (f.realizedArrow smoothAction hF hF' hG hG').comp
        (g.realizedArrow smoothAction hF' hF'' hG' hG'') := by
  apply SheafActionQuotient.Arrow.ext
  exact f.toMap.realizedArrow_comp g.toMap

end TargetMap

namespace RealizedQuotientArrow
variable (h : SheafActionQuotient.Arrow
    (P.realizedQuotient smoothAction F hF hG)
    (Q.realizedQuotient smoothAction F' hF' hG'))

theorem totalMap_target :
    RealizedArrow.totalMap h.torsorArrow ≫ ManifoldRealization.map F' hF' =
      ManifoldRealization.map F hF := by
  have hh := (SheafActionQuotient.preserves_iff_totalMap h.torsorArrow).mp h.preserves
  rw [P.realizedQuotient_totalMap, Q.realizedQuotient_totalMap] at hh
  simp only [RealizedArrow.totalMap, Category.assoc]
  rw [hh, Iso.inv_hom_id_assoc]

/-- Recover target preservation as an equality of ordinary smooth maps. -/
def ordinaryMap : TargetMap P Q F F' where
  toMap := RealizedArrow.ordinaryMap h.torsorArrow
  target e := by
    have he : F' ∘ (RealizedArrow.ordinaryMap h.torsorArrow).toFun = F := by
      apply ManifoldRealization.map_injective
        (hF'.comp (RealizedArrow.ordinaryMap h.torsorArrow).smooth) hF
      rw [ManifoldRealization.map_comp _ _
        (RealizedArrow.ordinaryMap h.torsorArrow).smooth hF',
        RealizedArrow.ordinaryMap_map]
      exact totalMap_target smoothAction hF hF' hG hG' h
    exact congrFun he e

end RealizedQuotientArrow

/-- All ordinary target-preserving maps correspond to all quotient arrows;
neither side selects a trivialization or a global section. -/
def targetMapEquiv : TargetMap P Q F F' ≃ SheafActionQuotient.Arrow
    (P.realizedQuotient smoothAction F hF hG)
    (Q.realizedQuotient smoothAction F' hF' hG') where
  toFun := TargetMap.realizedArrow smoothAction hF hF' hG hG'
  invFun := RealizedQuotientArrow.ordinaryMap smoothAction hF hF' hG hG'
  left_inv f := TargetMap.ext _ _ (Map.ordinary_realized f.toMap)
  right_inv h := SheafActionQuotient.Arrow.ext _ _
    (RealizedArrow.realized_ordinary h.torsorArrow)

/-- All quotient arrows on any chosen chart base, including the explicit equality
transports back to the original supplied bundle presentations. -/
def targetMapChartEquiv (A : ChartFamily n B) : TargetMap P Q F F' ≃ SheafActionQuotient.Arrow
    (SheafActionQuotient.reindex (P.quotientObject smoothAction F hF hG)
      (A.comparison P.baseCharts).hom)
    (SheafActionQuotient.reindex (Q.quotientObject smoothAction F' hF' hG')
      (A.comparison Q.baseCharts).hom) :=
  (targetMapEquiv smoothAction hF hF' hG hG').trans
    (((SheafActionQuotient.restrictionEquivalence (atlasIso A).symm).fullyFaithfulFunctor.homEquiv).trans
      ((eqToIso (P.realizedQuotient_chart smoothAction F hF hG A)).homCongr
        (eqToIso (Q.realizedQuotient_chart smoothAction F' hF' hG' A))))

theorem targetMapChartEquiv_roundtrip (A : ChartFamily n B) (k : TargetMap P Q F F') :
    (targetMapChartEquiv smoothAction hF hF' hG hG' A).symm
      (targetMapChartEquiv smoothAction hF hF' hG hG' A k) = k :=
  (targetMapChartEquiv smoothAction hF hF' hG hG' A).symm_apply_apply k

theorem targetMapChartEquiv_apply (A : ChartFamily n B) (k : TargetMap P Q F F') :
    targetMapChartEquiv smoothAction hF hF' hG hG' A k =
      eqToHom (P.realizedQuotient_chart smoothAction F hF hG A).symm ≫
        (k.realizedArrow smoothAction hF hF' hG hG').reindex (atlasIso A).inv ≫
          eqToHom (Q.realizedQuotient_chart smoothAction F' hF' hG' A) := rfl

theorem targetMapChartEquiv_ident (A : ChartFamily n B) :
    targetMapChartEquiv smoothAction hF hF hG hG A (TargetMap.ident P F) = SheafActionQuotient.Arrow.ident _ := by
  rw [targetMapChartEquiv_apply, TargetMap.realizedArrow_ident]
  exact SheafActionQuotient.Arrow.reindexTransport_ident (atlasIso A).inv
    (P.realizedQuotient_chart smoothAction F hF hG A)

theorem targetMapChartEquiv_inverse (A : ChartFamily n B) (k : TargetMap P Q F F') :
    targetMapChartEquiv smoothAction hF' hF hG' hG A k.inverse =
      (targetMapChartEquiv smoothAction hF hF' hG hG' A k).inverse := by
  rw [targetMapChartEquiv_apply, targetMapChartEquiv_apply, TargetMap.realizedArrow_inverse]
  exact SheafActionQuotient.Arrow.reindexTransport_inverse
    (k.realizedArrow smoothAction hF hF' hG hG') (atlasIso A).inv
    (P.realizedQuotient_chart smoothAction F hF hG A)
    (Q.realizedQuotient_chart smoothAction F' hF' hG' A)

variable {E'' : Type} [MulAction G E''] [TopologicalSpace E'']
  [ChartedSpace (Space n) E''] [IsManifold (Model n) ∞ E'']
  {R : Bundle (n := n) (G := G) (B := B) (E := E'')}
  {F'' : E'' → M}

theorem targetMapChartEquiv_comp (A : ChartFamily n B)
    (hF'' : ContMDiff (Model n) (Model d) ∞ F'')
    (hG'' : ∀ (g : G) e, F'' (g • e) = g • F'' e)
    (k : TargetMap P Q F F') (l : TargetMap Q R F' F'') :
    targetMapChartEquiv smoothAction hF hF'' hG hG'' A (k.comp l) =
      (targetMapChartEquiv smoothAction hF hF' hG hG' A k).comp
        (targetMapChartEquiv smoothAction hF' hF'' hG' hG'' A l) := by
  rw [targetMapChartEquiv_apply, targetMapChartEquiv_apply, targetMapChartEquiv_apply,
    TargetMap.realizedArrow_comp smoothAction hF hF' hG hG' k hF'' hG'' l]
  exact SheafActionQuotient.Arrow.reindexTransport_comp
    (k.realizedArrow smoothAction hF hF' hG hG')
    (l.realizedArrow smoothAction hF' hF'' hG' hG'') (atlasIso A).inv
    (P.realizedQuotient_chart smoothAction F hF hG A)
    (Q.realizedQuotient_chart smoothAction F' hF' hG' A)
    (R.realizedQuotient_chart smoothAction F'' hF'' hG'' A)

end SquareKit.SmoothPrincipalBundle
