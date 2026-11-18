import SquareKit.SmoothChartOverlap
import SquareKit.SmoothChartLocalLifting
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! Chosen ordinary chart overlaps are pullbacks in the chart realization at every site stage. -/
noncomputable section
open CategoryTheory

namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen SmoothAlgebra SmoothPresentationSite CategoryTheory.Limits
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)
theorem diagonal_left (i : A.Index) : A.diagonal i ≫ A.left i i = 𝟙 _ := A.factor_left _
theorem diagonal_right (i : A.Index) : A.diagonal i ≫ A.right i i = 𝟙 _ := A.factor_right _
theorem reverse_left (i j : A.Index) : A.reverse i j ≫ A.left j i = A.right i j := A.factor_left _
theorem reverse_right (i j : A.Index) : A.reverse i j ≫ A.right j i = A.left i j := A.factor_right _
theorem compose_left (i j k : A.Index) : A.compose i j k ≫ A.left i k = A.composeFirst i j k ≫ A.left i j := A.factor_left _
theorem compose_right (i j k : A.Index) : A.compose i j k ≫ A.right i k = A.composeSecond i j k ≫ A.right j k := A.factor_right _
abbrev Stage (X : Site) := Σ i, X ⟶ toSite.obj (A.charts.domain i)
def StageRel (X : Site) (a b : A.Stage X) : Prop :=
  ∃ z : X ⟶ toSite.obj (A.pair a.1 b.1), z ≫ toSite.map (A.left a.1 b.1) = a.2 ∧
    z ≫ toSite.map (A.right a.1 b.1) = b.2
theorem stage_refl (X : Site) (a : A.Stage X) : A.StageRel X a a := by
  refine ⟨a.2 ≫ toSite.map (A.diagonal a.1), ?_, ?_⟩
  · rw [Category.assoc, ← toSite.map_comp, diagonal_left, toSite.map_id, Category.comp_id]
  · rw [Category.assoc, ← toSite.map_comp, diagonal_right, toSite.map_id, Category.comp_id]
theorem stage_symm (X : Site) {a b : A.Stage X} (h : A.StageRel X a b) : A.StageRel X b a := by
  obtain ⟨z,hl,hr⟩ := h
  refine ⟨z ≫ toSite.map (A.reverse a.1 b.1), ?_, ?_⟩
  · rw [Category.assoc, ← toSite.map_comp, reverse_left, hr]
  · rw [Category.assoc, ← toSite.map_comp, reverse_right, hl]
theorem stage_trans (X : Site) {a b c : A.Stage X} (h : A.StageRel X a b) (h' : A.StageRel X b c) :
    A.StageRel X a c := by
  obtain ⟨u,ul,ur⟩ := h
  obtain ⟨v,vl,vr⟩ := h'
  have hp := inverse_site_pullback (A.right a.1 b.1) (A.overlapDefining b.1 c.1)
  let w := hp.lift u v (ur.trans vl.symm)
  refine ⟨w ≫ toSite.map (A.compose a.1 b.1 c.1), ?_, ?_⟩
  · rw [Category.assoc, ← toSite.map_comp, compose_left, toSite.map_comp, ← Category.assoc]
    exact (congrArg (fun k => k ≫ toSite.map (A.left a.1 b.1)) (hp.lift_fst u v _)).trans ul
  · rw [Category.assoc, ← toSite.map_comp, compose_right, toSite.map_comp, ← Category.assoc]
    exact (congrArg (fun k => k ≫ toSite.map (A.right b.1 c.1)) (hp.lift_snd u v _)).trans vr
def stageSetoid (X : Site) : Setoid (A.Stage X) :=
  ⟨A.StageRel X, A.stage_refl X, A.stage_symm X, A.stage_trans X⟩
end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen SmoothAlgebra SmoothPresentationSite CategoryTheory.Limits Opposite
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)
def stageCocone (X : Site) : Cocone (A.charts.rawDiagram ⋙ (evaluation _ Type).obj (op X)) where
  pt := Quotient (A.stageSetoid X)
  ι := {
    app := fun j => match j with
      | .right i => ↾fun x => Quotient.mk _ ⟨i,x⟩
      | .left r => ↾fun x => Quotient.mk _ ⟨r.first,x ≫ toSite.map r.left⟩
    naturality := by
      intro j k f
      cases f with
      | id => simp
      | fst r => rfl
      | snd r =>
        apply ConcreteCategory.hom_ext
        intro x
        change A.charts.Relation at r
        change X ⟶ toSite.obj r.domain at x
        apply Quotient.sound
        apply A.stage_symm X
        refine ⟨x ≫ toSite.map (A.factor r), ?_, ?_⟩
        · change (x ≫ toSite.map (A.factor r)) ≫ toSite.map (A.left r.first r.second) = x ≫ toSite.map r.left
          rw [Category.assoc, ← toSite.map_comp, factor_left]
        · change (x ≫ toSite.map (A.factor r)) ≫ toSite.map (A.right r.first r.second) = x ≫ toSite.map r.right
          rw [Category.assoc, ← toSite.map_comp, factor_right] }
def stageLabel (X : Site) : A.charts.rawRealization.obj (op X) ⟶ Quotient (A.stageSetoid X) :=
  (isColimitOfPreserves ((evaluation _ Type).obj (op X)) (colimit.isColimit A.charts.rawDiagram)).desc
    (A.stageCocone X)
theorem stageLabel_chart (X : Site) (i : A.Index) (a : X ⟶ toSite.obj (A.charts.domain i)) :
    A.stageLabel X ((colimit.ι A.charts.rawDiagram (.right i)).app (op X) a) =
      Quotient.mk (A.stageSetoid X) ⟨i,a⟩ := by
  exact ConcreteCategory.congr_hom
    ((isColimitOfPreserves ((evaluation _ Type).obj (op X))
      (colimit.isColimit A.charts.rawDiagram)).fac (A.stageCocone X) (.right i)) a
theorem raw_chart_eq (X : Site) (i j : A.Index)
    (a : X ⟶ toSite.obj (A.charts.domain i)) (b : X ⟶ toSite.obj (A.charts.domain j))
    (h : (colimit.ι A.charts.rawDiagram (.right i)).app (op X) a =
      (colimit.ι A.charts.rawDiagram (.right j)).app (op X) b) :
      A.StageRel X ⟨i,a⟩ ⟨j,b⟩ := by
  apply @Quotient.exact _ (A.stageSetoid X) ⟨i,a⟩ ⟨j,b⟩
  simpa only [stageLabel_chart] using congrArg (A.stageLabel X) h
end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.EuclideanOpen
open SmoothAlgebra SmoothPresentationSite SmoothAlgebra.Localization Opposite
theorem subInclusion_site_cancel (U : Domain) (q : Free U.dimension) (X : Site)
    (u v : X ⟶ toSite.obj (subdomain U q))
    (h : u ≫ toSite.map (subInclusion U q) = v ≫ toSite.map (subInclusion U q)) : u = v := by
  apply Quiver.Hom.unop_inj
  apply sub_unique (B := Carrier X.unop) U.defining q
    (smoothMap u.unop) (smoothMap v.unop)
  have hh := congrArg Quiver.Hom.unop h
  change Hom.comp u.unop (Localization.pullback (subInclusion U q)) =
    Hom.comp v.unop (Localization.pullback (subInclusion U q)) at hh
  rw [nested_pullback] at hh
  apply Hom.ext
  intro a
  exact congrArg (fun k : Hom (Principal U.defining) (Carrier X.unop) => k a) hh
end SquareKit.EuclideanOpen
namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen SmoothAlgebra SmoothPresentationSite CategoryTheory.Limits Opposite
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)
abbrev rawChart (i : A.Index) : (embedding.obj (A.charts.domain i)).obj ⟶ A.charts.rawRealization := colimit.ι A.charts.rawDiagram (.right i)
theorem raw_square (i j : A.Index) :
    (embedding.map (A.left i j)).hom ≫ A.rawChart i =
      (embedding.map (A.right i j)).hom ≫ A.rawChart j := by
  have h (r : A.charts.Relation) :
      (embedding.map r.left).hom ≫ colimit.ι A.charts.rawDiagram (.right r.first) =
        (embedding.map r.right).hom ≫ colimit.ι A.charts.rawDiagram (.right r.second) := by
    have hl := colimit.w A.charts.rawDiagram (WalkingMultispan.Hom.fst r)
    have hr := colimit.w A.charts.rawDiagram (WalkingMultispan.Hom.snd r)
    exact hl.trans hr.symm
  exact h (A.relation i j)
theorem raw_sections_pullback (X : Site) (i j : A.Index) :
    IsPullback ((embedding.map (A.left i j)).hom.app (op X))
      ((embedding.map (A.right i j)).hom.app (op X))
      ((A.rawChart i).app (op X)) ((A.rawChart j).app (op X)) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (A.raw_square i j) (op X), ?_, ?_⟩
  · intro u v h
    exact subInclusion_site_cancel _ _ X u v h.1
  · intro u v h
    exact A.raw_chart_eq X i j u v h
theorem raw_pullback (i j : A.Index) :
    IsPullback (embedding.map (A.left i j)).hom (embedding.map (A.right i j)).hom
      (A.rawChart i) (A.rawChart j) :=
  IsPullback.of_forall_isPullback_app (fun X => A.raw_sections_pullback X.unop i j)
end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen SmoothAlgebra SmoothPresentationSite CategoryTheory.Limits Opposite SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)
theorem sheafified_chart (i : A.Index) :
    (presheafToSheaf SmoothOpenSite.topology Type).map (A.rawChart i) ≫ A.charts.sheafifiedIso.hom =
      (sheafificationAdjunction SmoothOpenSite.topology Type).counit.app (embedding.obj (A.charts.domain i)) ≫
        A.charts.chart i := by
  apply (sheafToPresheaf SmoothOpenSite.topology Type).map_injective
  apply sheafify_hom_ext SmoothOpenSite.topology _ _ A.charts.realization.property
  change toSheafify SmoothOpenSite.topology _ ≫
      sheafifyMap SmoothOpenSite.topology (A.rawChart i) ≫ A.charts.sheafifiedIso.hom.hom =
    toSheafify SmoothOpenSite.topology _ ≫
      ((sheafificationAdjunction SmoothOpenSite.topology Type).counit.app
        (embedding.obj (A.charts.domain i))).hom ≫ (A.charts.chart i).hom
  rw [← toSheafify_naturality_assoc, sheafificationAdjunction_counit_app_val,
    toSheafify_sheafifyLift_assoc]
  exact (A.charts.rawMap_ι (.right i)).trans (Category.id_comp _).symm
theorem chart_pullback (i j : A.Index) :
    IsPullback (embedding.map (A.left i j)) (embedding.map (A.right i j))
      (A.charts.chart i) (A.charts.chart j) := by
  apply ((A.raw_pullback i j).map (presheafToSheaf SmoothOpenSite.topology Type)).of_iso
    (asIso ((sheafificationAdjunction SmoothOpenSite.topology Type).counit.app (embedding.obj (A.pair i j))))
    (asIso ((sheafificationAdjunction SmoothOpenSite.topology Type).counit.app (embedding.obj (A.charts.domain i))))
    (asIso ((sheafificationAdjunction SmoothOpenSite.topology Type).counit.app (embedding.obj (A.charts.domain j))))
    A.charts.sheafifiedIso
  · exact (sheafificationAdjunction SmoothOpenSite.topology Type).counit.naturality (embedding.map (A.left i j))
  · exact (sheafificationAdjunction SmoothOpenSite.topology Type).counit.naturality (embedding.map (A.right i j))
  · exact A.sheafified_chart i
  · exact A.sheafified_chart j
end SquareKit.ManifoldRealization.ChartFamily
