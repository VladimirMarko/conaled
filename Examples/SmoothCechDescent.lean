import SquareKit.SmoothCechGauge
import SquareKit.SmoothClutchingRefinement
import SquareKit.SmoothQuarterTurnArcs
import Examples.SmoothManifoldAction

/-! Checked specializations of represented smooth Čech descent. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Manifold ContDiff
namespace Examples.SmoothCechDescent
open SquareKit SquareKit.EuclideanOpen SquareKit.SmoothOpenSite
open SquareKit.SmoothRepresentedCover SquareKit.SmoothCech
open SquareKit.SmoothManifoldAction SquareKit.ManifoldRealization

/-- The identity chart is an admitted cover with actual represented intersections. -/
def identityAtlas (U : Domain) : Atlas (embedding.obj U) Unit where
  domain _ := U
  chart _ := 𝟙 _
  covering V x := by
    apply topology.superset_covering _ (topology.top_mem V)
    intro W r hr
    exact ⟨(), (embedding.obj U).obj.map r.op x, rfl⟩
  pair _ _ := U
  left _ _ := 𝟙 _
  right _ _ := 𝟙 _
  square _ _ := by simpa using (IsPullback.of_id_snd (f := 𝟙 (embedding.obj U)))
  triple _ _ _ := U
  firstSecond _ _ _ := 𝟙 _
  third _ _ _ := 𝟙 _
  tripleSquare _ _ _ := by simpa using (IsPullback.of_id_snd (f := 𝟙 (embedding.obj U)))

variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]

def identityDatum (U : Domain) (m : External.SmoothMap U d M) :
    Datum (d := d) (G := G) (M := M) (identityAtlas U) where
  localMap _ := m
  transition _ _ := ⟨1, fun x => one_smul G (m.val x)⟩
  diagonal _ _ := rfl
  cocycle _ _ _ _ := (one_mul 1).symm

example (U : Domain) (m : External.SmoothMap U d M)
    (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x)) :
    SheafActionQuotient.Object (representation smoothAction).action (embedding.obj U) :=
  (identityDatum (G := G) U m).interpreted smoothAction

example (U : Domain) (m : External.SmoothMap U d M) :
    (Hom.ident (identityDatum (G := G) U m)).inverse.comp
      (Hom.ident (identityDatum (G := G) U m)) = Hom.ident (identityDatum (G := G) U m) :=
  Hom.inverse_comp _

namespace OneChart
variable (U : Domain) (m : External.SmoothMap U d M)
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))

def admitted : TrivializedOn (identityAtlas U) smoothAction
    (SheafActionQuotient.chart (representation smoothAction).action (hat m.val m.property)) where
  trivialization _ := SheafTorsor.Arrow.ident _

theorem localMap_hat : hat ((admitted U m smoothAction).localMap ()).val
    ((admitted U m smoothAction).localMap ()).property = hat m.val m.property := by
  rw [TrivializedOn.localMap_hat]
  ext V x
  exact (representation smoothAction).action.one_act V _

theorem smoothMap_of_hat_eq (m n : External.SmoothMap U d M)
    (he : hat m.val m.property = hat n.val n.property) : m = n := by
  apply Subtype.ext
  funext x
  have h := congrArg (fun f : embedding.obj U ⟶ object d M =>
    pointEquiv (d := d) (M := M)
      (f.hom.app (op (op (SmoothPresentationSite.free 0))) (ordinaryPoint U x))) he
  exact (hat_eval m.val m.property x).symm.trans (h.trans (hat_eval n.val n.property x))

theorem localMap_eq : (admitted U m smoothAction).localMap () = m :=
  smoothMap_of_hat_eq U _ _ (localMap_hat U m smoothAction)

theorem datum_unique (p : Datum (d := d) (G := G) (M := M) (identityAtlas U)) :
    p = identityDatum U (p.localMap ()) := by
  refine Datum.ext _ _ ?_ ?_
  · funext i
    cases i
    rfl
  · apply heq_of_eq
    funext i j
    cases i
    cases j
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    have hd : (identityAtlas U).diagonal () = 𝟙 U := by
      simpa only [identityAtlas, Category.comp_id] using (identityAtlas U).diagonal_left ()
    have h := p.diagonal () x
    rw [hd] at h
    exact h

theorem extracted_eq : (admitted U m smoothAction).extractedDatum = identityDatum (G := G) U m := by
  rw [datum_unique U ((admitted U m smoothAction).extractedDatum)]
  change identityDatum U ((admitted U m smoothAction).localMap ()) = _
  rw [localMap_eq]

def recovery : SheafActionQuotient.Arrow ((identityDatum (G := G) U m).interpreted smoothAction)
    (SheafActionQuotient.chart (representation smoothAction).action (hat m.val m.property)) :=
  (eqToHom (congrArg (fun p : Datum (d := d) (G := G) (M := M) (identityAtlas U) =>
    p.interpreted smoothAction) (extracted_eq U m smoothAction).symm)).comp
      (admitted U m smoothAction).extractedRecovery


/-- On the identity atlas, compatible arrows are exactly the original labels. -/
def labelsEquiv (n : External.SmoothMap U d M) :
    Hom (identityDatum (G := G) U m) (identityDatum U n) ≃ External.Labels (G := G) U m n where
  toFun f := f.labels ()
  invFun a := {
    labels _ := a
    commutes _ _ x := by change 1 * a.val x = a.val x * 1; simp }
  left_inv f := by
    apply Hom.ext
    funext i
    cases i
    rfl
  right_inv _ := rfl

/-- The one-chart family comparison preserves both coordinates and certificates. -/
def familiesEquiv (n : External.SmoothMap U d M) :
    Hom (identityDatum (G := G) U m) (identityDatum U n) ≃ External.Family (G := G) U m n :=
  (labelsEquiv U m n).trans (External.labelsEquiv m n)

theorem native_family_agreement (n : External.SmoothMap U d M)
    (f : Hom (identityDatum (G := G) U m) (identityDatum U n)) :
    External.smoothChartEquiv smoothAction m n (f.chartArrow smoothAction ()) =
      familiesEquiv U m n f := by
  exact congrArg (External.labelsEquiv m n)
    ((External.chartLabelsEquiv smoothAction m n).apply_symm_apply (f.labels ()))


/-- The canonical descent comparison built from actual regularization recovers
an original chart arrow, with the selected #566 recovery. -/
theorem canonical_arrow_agreement (n : External.SmoothMap U d M)
    (f : External.ChartArrow smoothAction m n) :
    SheafActionQuotient.Descent.canonicalArrowEquiv
      (SplitSheaf.ofDisplay (identityAtlas U).cover) _ _
      ((admitted U m smoothAction).canonicalArrowMap (admitted U n smoothAction)
        ((admitted U m smoothAction).extractArrow (admitted U n smoothAction) f)) = f := by
  rw [TrivializedOn.canonicalArrowMap_agreement, TrivializedOn.arrow_roundtrip]

/-- Agreement retains the entire native smooth family, not only its point labels. -/
theorem canonical_family_agreement (n : External.SmoothMap U d M)
    (f : External.ChartArrow smoothAction m n) :
    External.smoothChartEquiv smoothAction m n
      (SheafActionQuotient.Descent.canonicalArrowEquiv
        (SplitSheaf.ofDisplay (identityAtlas U).cover) _ _
        ((admitted U m smoothAction).canonicalArrowMap (admitted U n smoothAction)
          ((admitted U m smoothAction).extractArrow (admitted U n smoothAction) f))) =
      External.smoothChartEquiv smoothAction m n f := by
  rw [canonical_arrow_agreement]

/-- Changing the canonical descent cover preserves that same complete family. -/
theorem canonical_family_cover_comparison (n : External.SmoothMap U d M)
    (B : SplitSheaf.Ty (embedding.obj U))
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]
    (f : External.ChartArrow smoothAction m n) :
    External.smoothChartEquiv smoothAction m n
      (SheafActionQuotient.Descent.canonicalArrowEquiv B _ _
        (SheafActionQuotient.Descent.recoveryArrowComparison
          (SplitSheaf.ofDisplay (identityAtlas U).cover) B _ _
          ((admitted U m smoothAction).canonicalArrowMap (admitted U n smoothAction)
            ((admitted U m smoothAction).extractArrow (admitted U n smoothAction) f)))) =
      External.smoothChartEquiv smoothAction m n f := by
  rw [SheafActionQuotient.Descent.recoveryArrowComparison_commutes,
    canonical_arrow_agreement]

end OneChart

namespace Clutching
open SquareKit.SmoothClutching
open scoped Orbifolds.FiniteActionPresentation
local instance trivialAction (G : Type) [Group G] : MulAction G (Space 1) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smooth (G : Type) [Group G] (g : G) : ContMDiff (Model 1) (Model 1) ∞
    (fun x : Space 1 => g • x) := contMDiff_id

def zeroMap : base ⟶ object 1 (Space 1) :=
  pushout.desc (hat (fun _ : Points line => (0 : Space 1)) contMDiff_const)
    (hat (fun _ : Points line => (0 : Space 1)) contMDiff_const) rfl

theorem trivial_act (G : Type) [Group G] (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (m : (object 1 (Space 1)).obj.obj U) :
    (representation (smooth G)).action.act U g m = m := by
  let r := representation (smooth G)
  let S := Presheaf.imageSieve (constantLabel G) g
  have hS : S ∈ topology U.unop := Presheaf.imageSieve_mem topology (constantLabel G) g
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (object 1 (Space 1)).property) S hS).isSeparatedFor.ext
  intro V f hf
  obtain ⟨k,hk⟩ := hf
  change (object 1 (Space 1)).obj.map f.op (r.act U g m) = _
  rw [r.act_natural, ← hk, r.act_constant]
  change ((ManifoldRealization.map id contMDiff_id).hom.app _ _) = _
  rw [ManifoldRealization.map_id]
  rfl

def quotient (G : Type) [Group G] (c : G) :
    SheafActionQuotient.Object (representation (smooth G)).action base :=
  SheafActionQuotient.invariantObject (torsor G c) zeroMap
    (fun x g => trivial_act G x.obj g _)

def admitted (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] (c : G) :
    TrivializedOn Represented.atlas (smooth G) (quotient G c) where
  trivialization := Represented.localTrivialization G c


theorem split_trivialization_apply (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) (i : Bool) (U : SmoothPresentationSite.Siteᵒᵖ)
    (z : (SplitSheaf.Ext (SplitSheaf.ofDisplay Represented.atlas.cover)).obj.obj U)
    (x : lineSheaf.obj.obj U)
    (hx : (SplitSheaf.displayIso Represented.atlas.cover).hom.hom.app U z =
      (Represented.atlas.inclusion i).hom.app U x)
    (g : (locallyConstantGroup G).obj.obj U) :
    ((admitted G c).splitRegularization.torsorArrow.iso.hom.app
      ((SplitSheaf.Ext (SplitSheaf.ofDisplay Represented.atlas.cover)).obj.elementsMk U z) g).val =
      (if i then totalChartRight G c else totalChartLeft G c).hom.app U
        (pairSection _ _ U x g) := by
  have h := (admitted G c).splitRegularization_apply U z g
  rw [hx] at h
  have ht := h.trans ((admitted G c).regularization_chart_apply i U x g)
  have hv := congrArg (fun z : (SplitSheaf.Ext (torsor G c).family).obj.obj U =>
    (show (total G c).obj.obj U from z.2.val)) ht
  cases i
  · exact hv.trans (Represented.localTrivialization_left_apply G c (lineSheaf.obj.elementsMk U x) g)
  · exact hv.trans (Represented.localTrivialization_right_apply G c (lineSheaf.obj.elementsMk U x) g)


theorem extracted_overlap (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) :
    Represented.atlas.pairMap false true ≫
      (admitted G c).extractedDatum.overlapLabel (smooth G) = transition G c := by
  rw [TrivializedOn.extractedDatum_overlapLabel]
  ext U x
  let A := Represented.atlas
  let t := admitted G c
  let z := (SheafCoverCech.splitDoubleIso A.cover).inv.hom.app U
    ((A.pairMap false true).hom.app U x)
  let a := (SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover)).hom.app U z
  let b := (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover)).hom.app U z
  let ea := (SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U a
  let eb := (SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U b
  let label : (locallyConstantGroup G).obj.obj U :=
    t.splitRegularization.torsorArrow.iso.inv.app eb
      (t.splitRegularization.torsorArrow.iso.hom.app ea (1 : (locallyConstantGroup G).obj.obj U))
  change label = (transition G c).hom.app U x
  have first : (SplitSheaf.displayIso A.cover).hom.hom.app U a =
      (A.inclusion false).hom.app U (inclusion.hom.app U x) := by
    have h : A.pairMap false true ≫ (SheafCoverCech.splitDoubleIso A.cover).inv ≫
        SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫ (SplitSheaf.displayIso A.cover).hom =
        embedding.map (A.left false true) ≫ A.inclusion false := by
      rw [← SheafCoverCech.splitDouble_first]
      simp only [Iso.inv_hom_id_assoc, A.pairMap_first]
    exact congrArg (fun f => f.hom.app U x) h
  have second : (SplitSheaf.displayIso A.cover).hom.hom.app U b =
      (A.inclusion true).hom.app U (inclusion.hom.app U x) := by
    have h : A.pairMap false true ≫ (SheafCoverCech.splitDoubleIso A.cover).inv ≫
        SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫ (SplitSheaf.displayIso A.cover).hom =
        embedding.map (A.right false true) ≫ A.inclusion true := by
      rw [← SheafCoverCech.splitDouble_second]
      simp only [Iso.inv_hom_id_assoc, A.pairMap_second]
    exact congrArg (fun f => f.hom.app U x) h
  have cancel := congrArg (fun f => f.app eb
    (t.splitRegularization.torsorArrow.iso.hom.app ea (1 : (locallyConstantGroup G).obj.obj U)))
    t.splitRegularization.torsorArrow.iso.inv_hom_id
  change t.splitRegularization.torsorArrow.iso.hom.app eb label =
    t.splitRegularization.torsorArrow.iso.hom.app ea (1 : (locallyConstantGroup G).obj.obj U) at cancel
  have raw := congrArg (fun y => (show (total G c).obj.obj U from y.val)) cancel
  rw [split_trivialization_apply G c true U b _ second label,
    split_trivialization_apply G c false U a _ first 1] at raw
  have glue := Represented.chart_gluing G c U x (1 : (locallyConstantGroup G).obj.obj U)
  rw [one_mul] at glue
  have same := raw.trans glue
  let y := lineSheaf.obj.elementsMk U (inclusion.hom.app U x)
  apply (((Represented.localTrivialization G c true).iso.app y).toEquiv).injective
  apply Subtype.ext
  exact (Represented.localTrivialization_right_apply G c y label).trans
    (same.trans (Represented.localTrivialization_right_apply G c y _).symm)


theorem extracted_transition (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) (x : Points punctured) :
    ((admitted G c).extractedDatum.transition false true).val x =
      (labelAt G (transition G c) x)⁻¹ := by
  have h := congrArg (fun f : embedding.obj punctured ⟶ locallyConstantGroupSheaf G =>
    ordinaryHomLabelEquiv G punctured f x) (extracted_overlap G c)
  rw [Datum.overlapLabel_fac] at h
  have hl := Datum.transitionArrow_label (smooth G) (admitted G c).extractedDatum false true x
  have hh := hl.symm.trans h
  have he : ordinaryHomLabelEquiv G punctured (transition G c) x =
      labelAt G (transition G c) x := (labelAt_eq_ordinary G _ x).symm
  have hh' := hh.trans he
  exact inv_eq_iff_eq_inv.mp hh'

theorem extracted_transition_sign (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) (b : Bool) (x : Points punctured)
    (hx : x.val ∈ signOpen b) :
    ((admitted G c).extractedDatum.transition false true).val x =
      (if b then c else 1)⁻¹ := by
  rw [extracted_transition, transition_label G c b x hx]

theorem localMap_hat_zero (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) (i : Bool) :
    hat ((admitted G c).localMap i).val ((admitted G c).localMap i).property =
      hat (fun _ : Points line => (0 : Space 1)) contMDiff_const := by
  rw [TrivializedOn.localMap_hat]
  change Represented.chart i ≫ zeroMap = _
  cases i
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

theorem localMap_zero (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) (i : Bool) (x : Points line) :
    ((admitted G c).localMap i).val x = 0 := by
  have h := congrArg (fun f : embedding.obj line ⟶ object 1 (Space 1) =>
    pointEquiv (d := 1) (M := Space 1)
      (f.hom.app (op (op (SmoothPresentationSite.free 0))) (ordinaryPoint line x)))
    (localMap_hat_zero G c i)
  erw [hat_eval, hat_eval] at h
  exact h

theorem interpreted_no_section (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) (hc : c ≠ 1) :
    ¬ Nonempty (SplitSheaf.Tm ((admitted G c).extractedDatum.interpreted (smooth G)).torsor.family) := by
  rintro ⟨s⟩
  exact no_global_section G c hc ⟨SheafTorsor.sectionOfArrow
    ((SheafTorsor.ofSection _ s).comp (admitted G c).extractedRecovery.torsorArrow)⟩

open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩

def quarterTurnDatum := (admitted C4 quarterTurn).extractedDatum

theorem quarterTurn_no_section :
    ¬ Nonempty (SplitSheaf.Tm (quarterTurnDatum.interpreted (smooth C4)).torsor.family) :=
  interpreted_no_section C4 quarterTurn SquareKit.SmoothQuarterTurnArcs.quarterTurn_ne_one


theorem quarterTurn_transition_negative :
    (quarterTurnDatum.transition false true).val (puncturedPoint (-1) (by norm_num)) = 1 := by
  simpa only [quarterTurnDatum, Bool.false_eq_true, ite_false, inv_one] using
    extracted_transition_sign C4 quarterTurn false
    (puncturedPoint (-1) (by norm_num)) (by norm_num [signOpen, puncturedPoint])

theorem quarterTurn_transition_positive :
    (quarterTurnDatum.transition false true).val (puncturedPoint 1 one_ne_zero) = quarterTurn⁻¹ := by
  exact extracted_transition_sign C4 quarterTurn true
    (puncturedPoint 1 one_ne_zero) (by norm_num [signOpen, puncturedPoint])

theorem quarterTurn_transition_varies :
    (quarterTurnDatum.transition false true).val (puncturedPoint (-1) (by norm_num)) ≠
      (quarterTurnDatum.transition false true).val (puncturedPoint 1 one_ne_zero) := by
  rw [quarterTurn_transition_negative, quarterTurn_transition_positive]
  intro h
  exact SquareKit.SmoothQuarterTurnArcs.quarterTurn_ne_one
    (inv_eq_one.mp h.symm)

def quarterGauge (i : Bool) : External.Labels (G := C4) line
    (quarterTurnDatum.localMap i) (quarterTurnDatum.localMap i) :=
  ⟨LocallyConstant.const _ (if i then 1 else quarterTurn), fun _ => rfl⟩

def gaugedQuarterTurnDatum := quarterTurnDatum.gauge quarterTurnDatum.localMap quarterGauge

theorem quarterGauge_nonidentity : (quarterGauge false).val (realLinePoint 0) ≠ 1 :=
  SquareKit.SmoothQuarterTurnArcs.quarterTurn_ne_one

theorem gaugedQuarterTurn_forward (x : Points punctured) :
    (gaugedQuarterTurnDatum.transition false true).val x =
      (quarterTurnDatum.transition false true).val x * quarterTurn⁻¹ := by
  change (1 * (quarterTurnDatum.transition false true).val x) * quarterTurn⁻¹ = _
  rw [one_mul]

/-- The nonidentity chart gauge gives an actual recovery arrow. -/
def gaugeRecovery : SheafActionQuotient.Arrow
    (gaugedQuarterTurnDatum.interpreted (smooth C4)) (quotient C4 quarterTurn) :=
  (quarterTurnDatum.gaugeComparison quarterTurnDatum.localMap quarterGauge (smooth C4)).comp
    (admitted C4 quarterTurn).extractedRecovery

namespace OrderControl
abbrev S3 := Equiv.Perm (Fin 3)
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩

def zero : External.SmoothMap line 1 (Space 1) := ⟨fun _ => 0, contMDiff_const⟩
def datum : Datum (d := 1) (G := S3) (M := Space 1) (identityAtlas line) := identityDatum line zero

def labels (g : S3) (_i : Unit) : External.Labels (G := S3) line zero zero :=
  ⟨LocallyConstant.const _ g, fun _ => rfl⟩

def arrow (g : S3) : Hom datum datum where
  labels := labels g
  commutes _ _ _ := by change 1 * g = g * 1; simp

def changedArrow := (arrow SmoothManifoldAction.g).gauge (fun _ => zero) (fun _ => zero)
  (labels 1) (labels SmoothManifoldAction.h)

theorem gauge_order : (changedArrow.labels ()).val (realLinePoint 0) =
    SmoothManifoldAction.h * SmoothManifoldAction.g := by
  change (SmoothManifoldAction.h * SmoothManifoldAction.g) * (1 : S3)⁻¹ = _
  simp

theorem gauge_wrong_order : (changedArrow.labels ()).val (realLinePoint 0) ≠
    SmoothManifoldAction.g * SmoothManifoldAction.h := by
  rw [gauge_order]
  intro e
  have he := congrArg (fun p : S3 => p 0) e
  norm_num [SmoothManifoldAction.g, SmoothManifoldAction.h,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] at he

/-- An incorrect self-transition is rejected by the diagonal law. -/
theorem reject_bad_diagonal (p : Datum (d := 1) (G := S3) (M := Space 1) (identityAtlas line))
    (h : (p.transition () ()).val = LocallyConstant.const _ SmoothManifoldAction.g) : False := by
  have he := p.diagonal () (realLinePoint 0)
  rw [h] at he
  have hz := congrArg (fun p : S3 => p 0) he
  norm_num [SmoothManifoldAction.g, Equiv.swap_apply_def] at hz

def one : External.SmoothMap line 1 (Space 1) := ⟨fun _ _ => 1, contMDiff_const⟩

theorem reject_endpoint : IsEmpty (Hom datum (identityDatum (G := S3) line one)) := by
  refine ⟨fun f => ?_⟩
  have h := congrArg (fun y : Space 1 => y 0) ((f.labels ()).property (realLinePoint 0))
  change (0 : ℝ) = 1 at h
  exact zero_ne_one h

def emptyArrow : Hom
    (identityDatum (G := S3) SmoothManifoldAction.emptyDomain
      (SmoothManifoldAction.constant _ 0))
    (identityDatum (G := S3) SmoothManifoldAction.emptyDomain
      (SmoothManifoldAction.constant _ 1)) where
  labels _ := ⟨1, fun x => False.elim (SmoothManifoldAction.empty_no_point x)⟩
  commutes _ _ x := False.elim (SmoothManifoldAction.empty_no_point x)

theorem emptyArrow_roundtrip :
    (interpretedHomEquiv (smooth S3) _ _).symm
      (interpretedHomEquiv (smooth S3) _ _ emptyArrow) = emptyArrow :=
  (interpretedHomEquiv (smooth S3) _ _).symm_apply_apply emptyArrow

def threeAtlas : Atlas lineSheaf (Fin 3) where
  domain _ := line
  chart _ := 𝟙 _
  covering V x := by
    apply topology.superset_covering _ (topology.top_mem V)
    intro W r hr
    exact ⟨0, lineSheaf.obj.map r.op x, rfl⟩
  pair _ _ := line
  left _ _ := 𝟙 _
  right _ _ := 𝟙 _
  square _ _ := by simpa using (IsPullback.of_id_snd (f := 𝟙 lineSheaf))
  triple _ _ _ := line
  firstSecond _ _ _ := 𝟙 _
  third _ _ _ := 𝟙 _
  tripleSquare _ _ _ := by simpa using (IsPullback.of_id_snd (f := 𝟙 lineSheaf))

def badCocycle (i j : Fin 3) : LocallyConstant (Points line) S3 :=
  LocallyConstant.const _ (if i = j then 1 else SmoothManifoldAction.g)

theorem badCocycle_diagonal (i : Fin 3) (x : Points line) : badCocycle i i x = 1 := by
  simp [badCocycle]

/-- Every displayed diagonal is valid, but the off-diagonal cocycle is not. -/
theorem reject_bad_cocycle (p : Datum (d := 1) (G := S3) (M := Space 1) threeAtlas)
    (h : ∀ i j, (p.transition i j).val = badCocycle i j) : False := by
  have he := p.cocycle 0 1 2 (realLinePoint 0)
  rw [h, h, h] at he
  change SmoothManifoldAction.g = SmoothManifoldAction.g * SmoothManifoldAction.g at he
  have hz := congrArg (fun p : S3 => p 0) he
  norm_num [badCocycle, SmoothManifoldAction.g, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hz

end OrderControl

def shiftedAdmitted : TrivializedOn Represented.atlas (smooth C4) (quotient C4 quarterTurn) where
  trivialization i :=
    (SheafTorsor.regularArrow (constantSection lineSheaf (if i then 1 else quarterTurn))).comp
      ((admitted C4 quarterTurn).trivialization i)

theorem shifted_trivialization_nonidentity : shiftedAdmitted.trivialization false ≠
    (admitted C4 quarterTurn).trivialization false := by
  intro h
  let x := lineSheaf.obj.elementsMk (op (op (SmoothPresentationSite.free 0)))
    (ordinaryPoint line (realLinePoint 0))
  have he := congrArg (fun a => a.iso.hom.app x
    (1 : (locallyConstantGroup C4).obj.obj x.obj)) h
  have hi := (((admitted C4 quarterTurn).trivialization false).iso.app x).toEquiv.injective he
  change (1 : (locallyConstantGroup C4).obj.obj x.obj) *
    ((constantLabel C4).app x.obj quarterTurn) = 1 at hi
  rw [one_mul] at hi
  apply SquareKit.SmoothQuarterTurnArcs.quarterTurn_ne_one
  apply (constantLabelRealEquiv C4).injective
  exact hi.trans (((constantLabel C4).app x.obj).hom.map_one).symm

theorem actual_changed_datum :
    quarterTurnDatum.gauge shiftedAdmitted.extractedDatum.localMap
      ((admitted C4 quarterTurn).changeOfTrivialization (smooth C4) shiftedAdmitted).labels =
        shiftedAdmitted.extractedDatum :=
  (admitted C4 quarterTurn).changed_datum (smooth C4) shiftedAdmitted

namespace Refinements
open SquareKit.SmoothClutching.Refined

def onOne := quarterTurnDatum.restrict (refinement (punctures 1) (punctures_cover 1 (by norm_num)))
def onTwo := quarterTurnDatum.restrict (refinement (punctures 2) (punctures_cover 2 (by norm_num)))
def onCommon := quarterTurnDatum.restrict (refinement commonFunctions common_cover)

theorem onOne_map_zero (i : Bool × Bool) (x : Points (atlasOne.domain i)) :
    (onOne.localMap i).val x = 0 := localMap_zero C4 quarterTurn i.1 _

theorem two_nonidentity : baseScale 2 (by norm_num) ≠ 𝟙 base :=
  baseScale_ne_identity 2 (by norm_num) (by norm_num)

theorem three_nonidentity : baseScale 3 (by norm_num) ≠ 𝟙 base :=
  baseScale_ne_identity 3 (by norm_num) (by norm_num)

theorem original_accepts_half : (fun _ : Fin 1 => (1/2 : ℝ)) ∈ Points (principal (hole 1)) := by
  change (1/2 : ℝ) - 1 ≠ 0
  norm_num

theorem pullback_two_excludes_half :
    ¬ (fun _ : Fin 1 => (1/2 : ℝ)) ∈ Points (principal (scaledFunction 2 (hole 1))) := by
  change ¬ (2 : ℝ) * (1/2) - 1 ≠ 0
  norm_num


/-- The genuine principal refinement retains the nontrivial torsor through
its selected interpretation comparison. -/
theorem onOne_no_section :
    ¬ Nonempty (SplitSheaf.Tm (onOne.interpreted (smooth C4)).torsor.family) := by
  rintro ⟨s⟩
  apply quarterTurn_no_section
  exact ⟨SheafTorsor.sectionOfArrow ((SheafTorsor.ofSection _ s).comp
    (quarterTurnDatum.restrictComparison
      (refinement (punctures 1) (punctures_cover 1 (by norm_num))) (smooth C4)).inverse.torsorArrow)⟩

theorem onTwo_no_section :
    ¬ Nonempty (SplitSheaf.Tm (onTwo.interpreted (smooth C4)).torsor.family) := by
  rintro ⟨s⟩
  apply quarterTurn_no_section
  exact ⟨SheafTorsor.sectionOfArrow ((SheafTorsor.ofSection _ s).comp
    (quarterTurnDatum.restrictComparison
      (refinement (punctures 2) (punctures_cover 2 (by norm_num))) (smooth C4)).inverse.torsorArrow)⟩

theorem onCommon_no_section :
    ¬ Nonempty (SplitSheaf.Tm (onCommon.interpreted (smooth C4)).torsor.family) := by
  rintro ⟨s⟩
  apply quarterTurn_no_section
  exact ⟨SheafTorsor.sectionOfArrow ((SheafTorsor.ofSection _ s).comp
    (quarterTurnDatum.restrictComparison
      (refinement commonFunctions common_cover) (smooth C4)).inverse.torsorArrow)⟩

def scaleTwoMap := scaledAtlasMap (punctures 1) (punctures_cover 1 (by norm_num)) 2 (by norm_num)
def scaleThreeAfterTwoMap := scaledAtlasMap
  (fun k => scaledFunction 2 (punctures 1 k))
  (scaled_cover (punctures 1) (punctures_cover 1 (by norm_num)) 2) 3 (by norm_num)
def scaledTwo := onOne.restrict scaleTwoMap
def scaledThreeAfterTwo := scaledTwo.restrict scaleThreeAfterTwoMap

theorem scaling_complete_datum : scaledThreeAfterTwo =
    onOne.restrict (scaleTwoMap.comp scaleThreeAfterTwoMap) :=
  onOne.restrict_comp scaleTwoMap scaleThreeAfterTwoMap

theorem scaling_domain_six (k : Bool) :
    principal (scaledFunction 3 (scaledFunction 2 (punctures 1 k))) =
      principal (scaledFunction 6 (punctures 1 k)) := by
  rw [scaledFunction_comp]
  norm_num

def scalingTwoComparison : SheafActionQuotient.Arrow
    (SheafActionQuotient.reindex (onOne.interpreted (smooth C4)) (baseScale 2 (by norm_num)))
    (scaledTwo.interpreted (smooth C4)) :=
  onOne.restrictComparison scaleTwoMap (smooth C4)

def scalingThreeAfterTwoComparison : SheafActionQuotient.Arrow
    (SheafActionQuotient.reindex (scaledTwo.interpreted (smooth C4)) (baseScale 3 (by norm_num)))
    (scaledThreeAfterTwo.interpreted (smooth C4)) :=
  scaledTwo.restrictComparison scaleThreeAfterTwoMap (smooth C4)

def commonViaOne :=
  (refinement (punctures 1) (punctures_cover 1 (by norm_num))).comp commonToOne
def commonViaTwo :=
  (refinement (punctures 2) (punctures_cover 2 (by norm_num))).comp commonToTwo

def commonRouteComparison := quarterTurnDatum.commonComparison commonViaOne commonViaTwo (smooth C4)

theorem common_route_coherence :
    (quarterTurnDatum.commonComparison commonViaOne commonViaTwo (smooth C4)).comp
      (quarterTurnDatum.commonComparison commonViaTwo
        (refinement commonFunctions common_cover) (smooth C4)) =
    quarterTurnDatum.commonComparison commonViaOne
      (refinement commonFunctions common_cover) (smooth C4) :=
  quarterTurnDatum.commonComparison_comp commonViaOne commonViaTwo
    (refinement commonFunctions common_cover) (smooth C4)

end Refinements
end Clutching
end Examples.SmoothCechDescent
