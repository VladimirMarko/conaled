import SquareKit.SmoothCechGauge
import SquareKit.SmoothClutchingAtlas
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

end OrderControl
end Clutching
end Examples.SmoothCechDescent
