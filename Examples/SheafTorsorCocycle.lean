import SquareKit.SheafTorsorCocycleRefinement
import Examples.SheafFamilyDescent
import SquareKit.SheafTorsorCocycleClassification
import SquareKit.SheafTorsorCocycleCover
import Examples.SmoothFiniteCover

/-! Noncommuting automorphisms and a nontrivial smooth cocycle survive classification. -/
noncomputable section
namespace Examples.SheafTorsorCocycle
open CategoryTheory Opposite SquareKit SquareKit.ManifoldRealization SquareKit.SmoothOpenSite
open SquareKit.EuclideanOpen SquareKit.SheafTorsor.Cocycle
abbrev S3 := Equiv.Perm (Fin 3)
def base := object 1 (Space 1)
def group := locallyConstantGroup S3
def cover := (SheafTorsor.trivial group base).family
instance : Presheaf.IsLocallySurjective topology (SplitSheaf.p cover).hom :=
  (SheafTorsor.trivial group base).locallySurjective

def datum : Datum group cover := trivial

def gauge (g : S3) : Gauge datum datum where
  label := constantSection _ g
  compatible x a b := by
    change 1 * (constantLabel S3).app x.obj g = (constantLabel S3).app x.obj g * 1
    simp

theorem gauge_injective : Function.Injective gauge := by
  intro g h he
  have hl := congrArg Gauge.label he
  let x := (SquareKit.SmoothManifoldAction.pointEquiv (d := 1) (M := Space 1)).symm 0
  have hx := congrArg (fun k : SplitSheaf.extension cover ⟶ locallyConstantGroupSheaf S3 =>
    k.hom.app (op (op (SmoothPresentationSite.free 0))) ⟨x, (1 : group.obj.obj (op (op (SmoothPresentationSite.free 0))))⟩) hl
  exact constantLabel_injective S3 (SmoothPresentationSite.free 0) (𝟙 _) hx

theorem gauge_comp (g h : S3) : (gauge g).comp (gauge h) = gauge (g * h) := by
  apply Gauge.ext
  ext U x
  exact (((constantLabel S3).app U).hom.map_mul g h).symm

def automorphism (g : S3) : datum.glue ⟶ datum.glue := stabilizerEquiv datum (gauge g)

theorem automorphism_injective : Function.Injective automorphism := by
  intro g h he
  exact gauge_injective ((stabilizerEquiv datum).injective he)

theorem noncommuting :
    stabilizerEquiv datum ((gauge SmoothManifoldAction.g).comp (gauge SmoothManifoldAction.h)) ≠
      automorphism (SmoothManifoldAction.h * SmoothManifoldAction.g) := by
  rw [gauge_comp]
  intro he
  have hp := congrArg (fun p : S3 => p 0) (automorphism_injective he)
  norm_num [SmoothManifoldAction.g, SmoothManifoldAction.h,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hp

def coboundaryTrivialization (g : SplitSheaf.extension cover ⟶ SheafTorsor.groupSheaf group) :
    SheafTorsor.Arrow (coboundary g).glue.obj (SheafTorsor.trivial group base) :=
  coboundaryRecovery g

end Examples.SheafTorsorCocycle

namespace Examples.SheafTorsorCocycle.Clutching
open CategoryTheory SquareKit SquareKit.SmoothOpenSite SquareKit.SheafTorsor.Cocycle
open Examples.SmoothCechDescent.Clutching
open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : MulAction C4 (ManifoldRealization.Space 1) := trivialAction _

def datum := ofDescent (quarterTurnDatum.cech (smooth C4)).toDescent.torsorDatum

theorem decoded_label : datum.splitLabel = quarterTurnDatum.splitLabel (smooth C4) := by
  ext U z
  change (1 : (locallyConstantGroup C4).obj.obj U) *
    (show (locallyConstantGroup C4).obj.obj U from
      (quarterTurnDatum.splitLabel (smooth C4)).hom.app U z) = _
  exact one_mul _

theorem glued_eq : datum.glue.obj = (quarterTurnDatum.interpreted (smooth C4)).torsor := by
  change SheafTorsor.Descent.torsor datum.toDescent =
    SheafTorsor.Descent.torsor (quarterTurnDatum.cech (smooth C4)).toDescent.torsorDatum
  exact congrArg (fun d => SheafTorsor.Descent.torsor d)
    (toDescent_ofDescent (quarterTurnDatum.cech (smooth C4)).toDescent.torsorDatum)

theorem no_section : ¬ Nonempty (SplitSheaf.Tm datum.glue.obj.family) := by
  rw [glued_eq]
  exact quarterTurn_no_section

theorem not_gauge_trivial : ¬ Nonempty (Gauge trivial datum) := by
  rintro ⟨g⟩
  exact no_section ⟨SheafTorsor.sectionOfArrow
    ((trivialRecovery.inverse).comp g.glue.hom)⟩

end Examples.SheafTorsorCocycle.Clutching

namespace Examples.SheafTorsorCocycle.ProperCover
open CategoryTheory Limits Opposite SquareKit
open SquareKit.SheafTorsor.Cocycle
open SmoothTorsors Orbifolds.QuarterTurn Examples.SheafFamilyDescent

abbrev aggregate := Sigma.desc charts
abbrev cover := SplitSheaf.ofDisplay aggregate
local instance : Presheaf.IsLocallySurjective SmoothOpenSite.topology aggregate.hom :=
  (SheafFamilyCover.jointlyLocallySurjective_iff_sigmaDesc charts).mp charts_joint

/-- The admitted object is the existing nontrivial torsor on a proper two-chart cover. -/
def admitted : Admitted (G := SmoothTorsors.group) cover := ⟨nontrivialTorsor,
  (admitsCover_iff_split aggregate nontrivialTorsor).mp
    ((admitsCover_family charts nontrivialTorsor).mpr fun b =>
      ⟨SmoothClutching.Represented.localTrivialization C4 quarterTurn b⟩)⟩

def datum : Datum SmoothTorsors.group cover := extract admitted

def recovered : datum.glue ≅ admitted := recovery admitted

example : ∀ b, ¬ Presheaf.IsLocallySurjective SmoothOpenSite.topology (charts b).hom :=
  chart_not_surjective

example : Sieve.ofArrows (fun _ : Bool => SmoothClutching.lineSheaf) charts ≠ ⊤ := charts_proper

theorem not_trivial :
    ¬ Nonempty (SheafTorsor.Arrow (SheafTorsor.trivial SmoothTorsors.group SmoothClutching.base) datum.glue.obj) := by
  rintro ⟨h⟩
  exact nontrivialTorsor_not_trivializable ⟨h.comp recovered.hom.hom⟩

abbrev scaleTwo := CoverMap.baseChange cover scale2
abbrev scaleThree := CoverMap.baseChange (SplitSheaf.tySub cover scale2) scale3

example : scale2 ≠ 𝟙 SmoothClutching.base :=
  SmoothClutching.baseScale_ne_identity 2 (by norm_num) (by norm_num)
example : scale3 ≠ 𝟙 SmoothClutching.base :=
  SmoothClutching.baseScale_ne_identity 3 (by norm_num) (by norm_num)


example {c d : Datum SmoothTorsors.group cover} (g : Gauge c d) :
    ((scaleTwo.pullGauge g).glue.hom).comp (scaleTwo.comparison d) =
      (scaleTwo.comparison c).comp (g.glue.hom.reindex scale2) :=
  scaleTwo.comparison_natural g

abbrev swappedCover := SplitSheaf.ofDisplay (Sigma.desc swappedCharts)
local instance : Presheaf.IsLocallySurjective SmoothOpenSite.topology (Sigma.desc swappedCharts).hom :=
  (SheafFamilyCover.jointlyLocallySurjective_iff_sigmaDesc swappedCharts).mp swappedCharts_joint

def swap : CoverMap (𝟙 SmoothClutching.base) cover swappedCover :=
  CoverMap.ofSquare aggregate (Sigma.desc swappedCharts)
    (SheafFamilyCover.refinementMap Bool.not (fun _ => 𝟙 _)) (by
      simpa using SheafFamilyCover.refinementMap_aggregate charts swappedCharts Bool.not
        (fun _ => 𝟙 _) (by intro b; simp [swappedCharts]))

/-- Refinement retains all gauges, including automorphisms, on this proper cover. -/
example {c d : Datum SmoothTorsors.group cover} : Gauge c d ≃ Gauge (swap.pull c) (swap.pull d) :=
  swap.refinementFullyFaithful.homEquiv

example : SheafTorsor.Arrow (swap.pull datum).glue.obj datum.glue.obj := swap.comparison datum

/-- Even the identity cover does not admit this nontrivial torsor. -/
example : ¬ AdmitsCover (𝟙 SmoothClutching.base) nontrivialTorsor :=
  nontrivialTorsor_not_trivializable

/-- Admission on an empty family needs no chosen index. -/
example (P : SheafTorsor.Torsor finiteGroup (Examples.SheafFamilyCover.constant Empty)) :
    AdmitsCover (Sigma.desc (fun i : Empty => (nomatch i :
      Examples.SheafFamilyCover.constant PUnit ⟶ Examples.SheafFamilyCover.constant Empty))) P :=
  (admitsCover_family _ P).mpr (fun i => nomatch i)

end Examples.SheafTorsorCocycle.ProperCover

namespace Examples.SheafTorsorCocycle.FiniteBaseChange
open CategoryTheory SquareKit SquareKit.SheafTorsor.Cocycle
open Examples.SheafFamilyCover Examples.SheafFamilyDescent
abbrev cover := SplitSheaf.ofDisplay (𝟙 (constant Bool))
abbrev first := CoverMap.baseChange cover negation
abbrev second := CoverMap.baseChange (SplitSheaf.tySub cover negation) negation
/-- Negation is not the identity map of the two-point base. -/
example : negation ≠ 𝟙 (constant Bool) := by
  intro h
  have e := congrArg (fun k : constant Bool ⟶ constant Bool =>
    k.hom.app (Opposite.op (Discrete.mk PUnit.unit)) false) h
  change true = false at e
  cases e

/-- Successive nonidentity base changes agree on the actual recovery arrow. -/
example (c : Datum finiteGroup cover) :
    (first.comp second).comparison c =
      (second.comparison (first.pull c)).comp ((first.comparison c).reindex negation) :=
  first.comparison_comp second c
end Examples.SheafTorsorCocycle.FiniteBaseChange
