import SquareKit.ChartElementSite
import SquareKit.SheafSiteComparisonDescent
import Examples.SubcanonicalTorsor

/-! Changing the actual doubled-origin torsor's site to its two-chart generated subsite. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.SheafSiteComparison
open CategoryTheory Limits Opposite SquareKit
open SmoothTorsors Orbifolds.QuarterTurn
open SquareKit.SheafSiteComparison

abbrev base := SmoothClutching.base
abbrev charts := SmoothClutching.Represented.chart
abbrev originalTopology := SmoothOpenSite.topology
abbrev baseTopology := ElementSite.topology base.obj originalTopology
abbrev chartTopology := ChartElementSite.topology charts
abbrev comparison := ChartElementSite.inclusion charts

instance comparison_dense : comparison.IsCoverDense baseTopology :=
  ChartElementSite.coverDense charts SheafFamilyDescent.charts_joint

instance comparison_denseSubsite : comparison.IsDenseSubsite chartTopology baseTopology :=
  inferInstanceAs (comparison.IsDenseSubsite (comparison.inducedTopology baseTopology) baseTopology)

example : comparison.IsContinuous chartTopology baseTopology := inferInstance
example : comparison.IsCocontinuous chartTopology baseTopology := inferInstance

/-- Each chart alone fails the necessary density hypothesis. -/
theorem single_chart_not_dense (b : Bool) :
    ¬ (ChartElementSite.inclusion (fun _ : PUnit => charts b)).IsCoverDense baseTopology := by
  intro h
  apply SheafFamilyDescent.chart_not_surjective b
  exact (SquareKit.SheafFamilyCover.singleton_iff (charts b)).mp
    ((ChartElementSite.coverDense_iff (fun _ : PUnit => charts b)).mp h)

example : Sieve.ofArrows (fun _ : Bool => SmoothClutching.lineSheaf) charts ≠ ⊤ :=
  SheafFamilyDescent.charts_proper

abbrev elementGroup := PrincipalSheafContext.group base group
abbrev parameter := PrincipalSheafContext.elementTerminal base
abbrev originalTorsor := PrincipalSheafContext.onElements base group nontrivialTorsor
abbrev changedTorsor := torsor chartTopology baseTopology comparison originalTorsor
abbrev torsorE := torsorEquivalence (G := elementGroup) (X := parameter)
  chartTopology baseTopology comparison

/-- The comparison transports the independently nontrivial quarter-turn torsor. -/
theorem changed_not_trivializable :
    ¬ Nonempty (SheafTorsor.trivial (groupRestriction chartTopology baseTopology comparison |>.obj elementGroup)
      (sheaf chartTopology baseTopology comparison parameter) ⟶ changedTorsor) := by
  rintro ⟨h⟩
  apply PrincipalSheafContext.onElements_nontrivial base group nontrivialTorsor
    nontrivialTorsor_not_trivializable
  exact ⟨(torsorFunctor chartTopology baseTopology comparison).preimage h⟩

abbrev elementAction := PrincipalSheafContext.elementAction base ActionQuotientStack.targetAction
abbrev originalQuotient := PrincipalSheafContext.quotientOnElements base
  ActionQuotientStack.targetAction ActionQuotientStack.genuine
abbrev changedQuotient := quotientObject chartTopology baseTopology comparison elementAction originalQuotient

/-- The changed-site quotient has the exact restricted original target map. -/
example : changedQuotient.totalMap = map chartTopology baseTopology comparison originalQuotient.totalMap :=
  quotient_totalMap chartTopology baseTopology comparison elementAction originalQuotient

abbrev ineffective := PrincipalSheafContext.elementAction base SheafFamilyDescent.ineffectiveBase
abbrev stabilizerFunctor :=
  PrincipalSheafContext.quotientOnElementsFunctor base SheafFamilyDescent.ineffectiveBase ⋙
    quotientFunctor chartTopology baseTopology comparison ineffective

/-- Ineffective isotropy survives both the context presentation and site change. -/
theorem changed_stabilizers_distinct :
    stabilizerFunctor.map (SheafFamilyDescent.baseStabilizer quarterTurn) ≠
      stabilizerFunctor.map (SheafFamilyDescent.baseStabilizer 1) := by
  intro h
  exact SheafFamilyDescent.baseStabilizers_distinct (stabilizerFunctor.map_injective h)

/-- The two original display fibers cover the terminal sheaf of the base element site. -/
abbrev liftedChart (i : Bool) := SplitSheaf.elementSheaf (SplitSheaf.ofDisplay (charts i))
def liftedCharts (i : Bool) : liftedChart i ⟶ parameter :=
  ⟨{ app := fun _ => TypeCat.ofHom (fun _ => PUnit.unit) }⟩

theorem liftedCharts_joint : SquareKit.SheafFamilyCover.JointlyLocallySurjective liftedCharts := by
  intro U x
  apply originalTopology.superset_covering ?_ (SheafFamilyDescent.charts_joint U.unop.val)
  rintro V f ⟨i,y,hy⟩
  refine ⟨_, rfl, i, ⟨y,hy⟩, ?_⟩
  change PUnit.unit = _
  exact Subsingleton.elim _ _

theorem liftedChart_not_surjective (i : Bool) :
    ¬ Presheaf.IsLocallySurjective baseTopology (liftedCharts i).hom := by
  intro h
  apply SheafFamilyDescent.chart_not_surjective i
  constructor
  intro U x
  have hs := Presheaf.imageSieve_mem baseTopology (liftedCharts i).hom
    (show parameter.obj.obj (op (ElementSite.point base.obj U x)) from PUnit.unit)
  apply originalTopology.superset_covering ?_ hs
  rintro V f ⟨y,hy,⟨p,hp⟩⟩
  exact ⟨p.val, p.property.trans hy.symm⟩

theorem liftedCharts_proper : Sieve.ofArrows liftedChart liftedCharts ≠ ⊤ := by
  intro h
  have hi : Sieve.ofArrows liftedChart liftedCharts (𝟙 parameter) := by rw [h]; trivial
  obtain ⟨i,k,hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hi
  exact liftedChart_not_surjective i (Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    baseTopology (congrArg (fun f => f.hom) hk.symm))

abbrev overlapObject := SubcanonicalTorsor.overlapObject
abbrev overlapSection := EuclideanOpen.toSite.map
  (EuclideanOpen.subInclusion SmoothClutching.line (SmoothAlgebra.generator 0))
def overlapChart (b : Bool) : ChartElementSite.Site charts :=
  ⟨b, ElementSite.point SmoothClutching.lineSheaf.obj overlapObject overlapSection⟩

/-- The induced chart category retains the actual cross-chart overlap arrow. -/
def crossChart : overlapChart false ⟶ overlapChart true :=
  InducedCategory.homMk (Functor.Elements.homMk (𝟙 (op overlapObject)) (by
    change base.obj.map (𝟙 _) ((charts true).hom.app _ overlapSection) =
      (charts false).hom.app _ overlapSection
    rw [base.obj.map_id]
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => f.hom) (pushout.condition
        (f := SmoothClutching.inclusion) (g := SmoothClutching.inclusion)))
          (op overlapObject)) (𝟙 overlapObject)).symm)).op

theorem overlapChart_distinct : overlapChart false ≠ overlapChart true := by
  intro h
  exact Bool.false_ne_true (congrArg Sigma.fst h)

abbrev changedPoint (b : Bool) :=
  (sheaf chartTopology baseTopology comparison parameter).obj.elementsMk
    (op (overlapChart b)) PUnit.unit

def changedChartLift (b : Bool) (g : group.obj.obj (op overlapObject)) :
    changedTorsor.family.family.obj (changedPoint b) :=
  (SmoothClutching.Represented.localTrivialization C4 quarterTurn b).iso.hom.app
    (overlapChart b).2.unop g

/-- The retained cross-chart map acts by the original quarter-turn clutching equation. -/
theorem changed_chart_gluing (g : group.obj.obj (op overlapObject)) :
    changedTorsor.family.family.map (Functor.Elements.homMk (x := changedPoint true) (y := changedPoint false) crossChart.op rfl)
      (changedChartLift true (g * (show group.obj.obj (op overlapObject) from
        (SmoothClutching.transition C4 quarterTurn).hom.app (op overlapObject) (𝟙 overlapObject)))) = changedChartLift false g := by
  apply Subtype.ext
  change (SmoothClutching.total C4 quarterTurn).obj.map (𝟙 _) _ = _
  rw [(SmoothClutching.total C4 quarterTurn).obj.map_id]
  exact (SubcanonicalTorsor.slice_chart_gluing g).symm

abbrev overlapQuarterTurn : group.obj.obj (op overlapObject) :=
  (SmoothOpenSite.constantLabel C4).app (op overlapObject) quarterTurn

/-- The actual changed target distinguishes two sections of a torsor fiber. -/
theorem changed_target_nonconstant :
    changedQuotient.value (changedPoint false) (changedChartLift false overlapQuarterTurn) ≠
      changedQuotient.value (changedPoint false) (changedChartLift false 1) := by
  intro h
  have hp : changedChartLift false overlapQuarterTurn = changedChartLift false 1 := Subtype.ext h
  have hg : overlapQuarterTurn = 1 :=
    (CategoryTheory.mono_iff_injective
      ((SmoothClutching.Represented.localTrivialization C4 quarterTurn false).iso.hom.app
        (overlapChart false).2.unop)).mp inferInstance hp
  exact quarterTurn_ne_one (SmoothOpenSite.constantLabel_injective C4 overlapObject.unop
    (SmoothOpenSite.ordinaryPoint SmoothClutching.punctured
      (SmoothClutching.puncturedPoint 1 one_ne_zero)) (hg.trans (map_one _).symm))

abbrev overlapTransition : group.obj.obj (op overlapObject) :=
  (SmoothClutching.transition C4 quarterTurn).hom.app (op overlapObject) (𝟙 overlapObject)

theorem overlapTransition_ne_one : overlapTransition ≠ 1 := by
  intro h
  apply SmoothClutching.transition_not_constant C4 quarterTurn quarterTurn_ne_one 1
  apply Sheaf.hom_ext
  apply yonedaEquiv.injective
  exact h.trans (map_one ((SmoothOpenSite.constantLabel C4).app (op overlapObject)).hom).symm

abbrev projection := ElementSite.projection base.obj
instance projection_cocontinuous : projection.IsCocontinuous baseTopology originalTopology where
  cover_lift {U} S hS := by
    change ElementSite.down base.obj (ElementSite.up base.obj S) ∈ originalTopology _
    rwa [ElementSite.down_up]

abbrev scaleParameter := sheaf baseTopology originalTopology projection base
abbrev projectedScale (r : ℝ) (hr : r ≠ 0) :=
  map baseTopology originalTopology projection (SmoothClutching.baseScale r hr)

theorem projectedScale_ne_identity (r : ℝ) (hr : r ≠ 0) (hne : r ≠ 1) :
    projectedScale r hr ≠ 𝟙 scaleParameter := by
  intro h
  let x := ElementSite.point base.obj SubcanonicalTorsor.lineObject
    (SmoothClutching.left.hom.app _ (𝟙 _))
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun k => k.hom) h) (op x))
    (SmoothClutching.left.hom.app _ (𝟙 _))
  have he : SmoothClutching.left ≫ SmoothClutching.baseScale r hr = SmoothClutching.left := by
    apply Sheaf.hom_ext
    apply yonedaEquiv.injective
    exact hv
  have hm : EuclideanOpen.embedding.map (SmoothClutching.lineScale r) = 𝟙 SmoothClutching.lineSheaf := by
    apply (cancel_mono SmoothClutching.left).mp
    simpa only [Category.id_comp] using (SmoothClutching.left_baseScale r hr).symm.trans he
  have hl : SmoothClutching.lineScale r = 𝟙 SmoothClutching.line := by
    apply (EuclideanOpen.homEquiv _ _).injective
    change EuclideanOpen.embedding.map _ = EuclideanOpen.embedding.map _
    simpa only [EuclideanOpen.embedding.map_id] using hm
  have hh := congrArg (fun u : SmoothClutching.line ⟶ SmoothClutching.line =>
    ((show EuclideanOpen.Map _ _ from u) (SmoothOpenSite.realLinePoint 1)).val 0) hl
  apply hne
  change r * 1 = 1 at hh
  simpa only [mul_one] using hh

abbrev scale2 := projectedScale 2 (by norm_num)
abbrev scale3 := projectedScale 3 (by norm_num)
example : scale2 ≠ 𝟙 scaleParameter := projectedScale_ne_identity 2 (by norm_num) (by norm_num)
example : scale3 ≠ 𝟙 scaleParameter := projectedScale_ne_identity 3 (by norm_num) (by norm_num)
abbrev scaleTorsor := torsor baseTopology originalTopology projection nontrivialTorsor
abbrev scaleAction := action baseTopology originalTopology projection ActionQuotientStack.targetAction
abbrev scaleQuotient := quotientObject baseTopology originalTopology projection
  ActionQuotientStack.targetAction ActionQuotientStack.genuine

/-- Two actual nonidentity substitutions commute with the concrete site change. -/
example : torsor chartTopology baseTopology comparison
    (SheafTorsor.reindex (SheafTorsor.reindex scaleTorsor scale2) scale3) =
      SheafTorsor.reindex (torsor chartTopology baseTopology comparison scaleTorsor)
        (map chartTopology baseTopology comparison (scale3 ≫ scale2)) :=
  torsor_reindex_comp chartTopology baseTopology comparison scaleTorsor scale2 scale3

example : quotientObject chartTopology baseTopology comparison scaleAction
    (SheafActionQuotient.reindex (SheafActionQuotient.reindex scaleQuotient scale2) scale3) =
      SheafActionQuotient.reindex (quotientObject chartTopology baseTopology comparison scaleAction scaleQuotient)
        (map chartTopology baseTopology comparison (scale3 ≫ scale2)) :=
  quotient_reindex_comp chartTopology baseTopology comparison scaleAction scaleQuotient scale2 scale3

abbrev scaleCover := fun i => map baseTopology originalTopology projection (charts i)
theorem scaleCover_joint : SquareKit.SheafFamilyCover.JointlyLocallySurjective scaleCover :=
  joint_cover baseTopology originalTopology projection charts SheafFamilyDescent.charts_joint
abbrev scaleChart (r : ℝ) :=
  map baseTopology originalTopology projection (EuclideanOpen.embedding.map (SmoothClutching.lineScale r))
theorem scale_refinement (r : ℝ) (hr : r ≠ 0) (i : Bool) :
    scaleChart r ≫ scaleCover i = scaleCover i ≫ projectedScale r hr := by
  have h : EuclideanOpen.embedding.map (SmoothClutching.lineScale r) ≫ charts i =
      charts i ≫ SmoothClutching.baseScale r hr := by
    cases i
    · exact (SmoothClutching.left_baseScale r hr).symm
    · exact (SmoothClutching.right_baseScale r hr).symm
  simpa only [Functor.map_comp] using congrArg
    (fun k => (restriction baseTopology originalTopology projection).map k) h

/-- Cover descent commutes with the same nonidentity scaling refinement. -/
def scaleTorsorRefinement (r : ℝ) (hr : r ≠ 0) :=
  torsorDescentRefinement chartTopology baseTopology comparison
    scaleCover scaleCover_joint scaleCover scaleCover_joint id
    (projectedScale r hr) (fun _ => scaleChart r) (scale_refinement r hr) elementGroup

def scaleQuotientRefinement (r : ℝ) (hr : r ≠ 0) :=
  quotientDescentRefinement chartTopology baseTopology comparison
    scaleCover scaleCover_joint scaleCover scaleCover_joint id
    (projectedScale r hr) (fun _ => scaleChart r) (scale_refinement r hr) scaleAction

/-- Successive scale-by-two and scale-by-three descent refinements use the
comparison with their actual composite on both sites. -/
def scaleTorsorRepeated :=
  torsorDescentRefinementComp chartTopology baseTopology comparison
    scaleCover scaleCover_joint scaleCover scaleCover scaleCover_joint
    id scale2 (fun _ => scaleChart 2) (scale_refinement 2 (by norm_num))
    id scale3 (fun _ => scaleChart 3) (scale_refinement 3 (by norm_num)) elementGroup

def scaleQuotientRepeated :=
  quotientDescentRefinementComp chartTopology baseTopology comparison
    scaleCover scaleCover_joint scaleCover scaleCover scaleCover_joint
    id scale2 (fun _ => scaleChart 2) (scale_refinement 2 (by norm_num))
    id scale3 (fun _ => scaleChart 3) (scale_refinement 3 (by norm_num)) scaleAction

/-- The repeated refinement square acts on the original quarter-turn consumer. -/
def scaleTorsorRepeatedConsumer := scaleTorsorRepeated.app
  ((SquareKit.SheafFamilyDescent.torsorEquivalence elementGroup scaleCover scaleCover_joint).functor.obj
    scaleTorsor)

def scaleQuotientRepeatedConsumer := scaleQuotientRepeated.app
  ((SquareKit.SheafFamilyDescent.quotientEquivalence scaleAction scaleCover scaleCover_joint).functor.obj
    scaleQuotient)

abbrev changedCover := fun i => map chartTopology baseTopology comparison (liftedCharts i)
theorem changedCover_joint : SquareKit.SheafFamilyCover.JointlyLocallySurjective changedCover :=
  joint_cover chartTopology baseTopology comparison liftedCharts liftedCharts_joint

abbrev sourceTorsorDescent := SquareKit.SheafFamilyDescent.torsorEquivalence
  elementGroup liftedCharts liftedCharts_joint
abbrev targetTorsorDescent := SquareKit.SheafFamilyDescent.torsorEquivalence
  (SheafSiteComparison.group chartTopology baseTopology comparison elementGroup)
  changedCover changedCover_joint
abbrev siteTorsorDescent := torsorDescentEquivalence chartTopology baseTopology comparison
  elementGroup liftedCharts liftedCharts_joint
abbrev changedTorsorData := siteTorsorDescent.functor.obj
  (sourceTorsorDescent.functor.obj originalTorsor)
abbrev recoveredTorsor := targetTorsorDescent.inverse.obj changedTorsorData

def changedTorsorRecovery : recoveredTorsor ≅ changedTorsor :=
  targetTorsorDescent.inverse.mapIso
    ((torsorDescentSquare chartTopology baseTopology comparison elementGroup
      liftedCharts liftedCharts_joint).app originalTorsor) ≪≫
    (targetTorsorDescent.unitIso.app changedTorsor).symm

/-- Full proper-cover descent and site change recover the same nontrivial torsor. -/
theorem recovered_not_trivializable :
    ¬ Nonempty (SheafTorsor.trivial (SheafSiteComparison.group chartTopology baseTopology comparison elementGroup)
      (sheaf chartTopology baseTopology comparison parameter) ⟶ recoveredTorsor) := by
  rintro ⟨h⟩
  exact changed_not_trivializable ⟨h ≫ changedTorsorRecovery.hom⟩

abbrev sourceQuotientDescent := SquareKit.SheafFamilyDescent.quotientEquivalence
  elementAction liftedCharts liftedCharts_joint
abbrev targetQuotientDescent := SquareKit.SheafFamilyDescent.quotientEquivalence
  (action chartTopology baseTopology comparison elementAction) changedCover changedCover_joint
abbrev siteQuotientDescent := quotientDescentEquivalence chartTopology baseTopology comparison
  liftedCharts liftedCharts_joint elementAction
abbrev changedQuotientData := siteQuotientDescent.functor.obj
  (sourceQuotientDescent.functor.obj originalQuotient)
abbrev recoveredQuotient := targetQuotientDescent.inverse.obj changedQuotientData

def changedQuotientRecovery : recoveredQuotient ≅ changedQuotient :=
  targetQuotientDescent.inverse.mapIso
    ((quotientDescentSquare chartTopology baseTopology comparison
      liftedCharts liftedCharts_joint elementAction).app originalQuotient) ≪≫
    (targetQuotientDescent.unitIso.app changedQuotient).symm

/-- Recovery retains the actual section-valued target map at every stage. -/
theorem changed_recovery_target (x : (sheaf chartTopology baseTopology comparison parameter).obj.Elements)
    (p : recoveredQuotient.torsor.family.family.obj x) :
    ((changedQuotientRecovery.hom.torsorArrow.iso.hom.app x) p).val =
      recoveredQuotient.value x p := changedQuotientRecovery.hom.preserves x p

abbrev stabilizerDescent :=
  PrincipalSheafContext.quotientOnElementsFunctor base SheafFamilyDescent.ineffectiveBase ⋙
    (SquareKit.SheafFamilyDescent.quotientEquivalence ineffective liftedCharts liftedCharts_joint).functor ⋙
    (quotientDescentEquivalence chartTopology baseTopology comparison
      liftedCharts liftedCharts_joint ineffective).functor ⋙
    (SquareKit.SheafFamilyDescent.quotientEquivalence
      (action chartTopology baseTopology comparison ineffective) changedCover changedCover_joint).inverse

/-- The proper-cover recovery square also retains the two distinct automorphisms. -/
theorem recovered_stabilizers_distinct :
    stabilizerDescent.map (SheafFamilyDescent.baseStabilizer quarterTurn) ≠
      stabilizerDescent.map (SheafFamilyDescent.baseStabilizer 1) := by
  intro h
  exact SheafFamilyDescent.baseStabilizers_distinct (stabilizerDescent.map_injective h)

/-- The same constructor with no charts removes density. -/
def emptyCharts : ∀ _ : Empty, SmoothClutching.lineSheaf ⟶ base := fun i => nomatch i
abbrev emptyTopology := ChartElementSite.topology emptyCharts
abbrev emptyComparison := ChartElementSite.inclusion emptyCharts

instance : IsEmpty (ChartElementSite.Site emptyCharts) := inferInstanceAs (IsEmpty (Σ _ : Empty, _))

instance empty_continuous : emptyComparison.IsContinuous emptyTopology baseTopology where
  op_comp_isSheaf_of_types _ U := isEmptyElim U
instance empty_cocontinuous : emptyComparison.IsCocontinuous emptyTopology baseTopology where
  cover_lift {U} := False.elim (isEmptyElim U)

abbrev emptyRestriction := quotientFunctor (X := parameter) emptyTopology baseTopology emptyComparison ineffective
abbrev emptyContext := PrincipalSheafContext.quotientOnElementsFunctor base SheafFamilyDescent.ineffectiveBase

/-- The actual forward restriction identifies the previously distinct stabilizer arrows. -/
theorem empty_identifies_stabilizers :
    emptyRestriction.map (emptyContext.map (SheafFamilyDescent.baseStabilizer quarterTurn)) =
      emptyRestriction.map (emptyContext.map (SheafFamilyDescent.baseStabilizer 1)) := by
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x
  exact isEmptyElim x.obj.unop

theorem empty_not_faithful : ¬ emptyRestriction.Faithful := by
  intro h
  exact SheafFamilyDescent.baseStabilizers_distinct
    (emptyContext.map_injective (emptyRestriction.map_injective empty_identifies_stabilizers))

theorem empty_not_dense : ¬ emptyComparison.IsCoverDense baseTopology := by
  intro h
  have : emptyComparison.IsDenseSubsite emptyTopology baseTopology :=
    inferInstanceAs (emptyComparison.IsDenseSubsite (emptyComparison.inducedTopology baseTopology) baseTopology)
  exact empty_not_faithful (quotientFunctor_faithful emptyTopology baseTopology emptyComparison ineffective)

end Examples.SheafSiteComparison
