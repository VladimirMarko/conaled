import SquareKit.Internal.Cubical.ChartFamily
import Examples.CubicalLargeConstructors

/-! Chart-family clients retain a genuine universe-code context. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalChartFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse ChartFamily CubicalLargeConstructors

/-- The actual base natural, including zero, is the label count. -/
def count : Count context :=
  (Raising.raiseTerm CubicalDiscreteFilling.index).reindex baseProjection

def data (e : Nat) : Inputs context where
  count := count
  targetCode := naturalsCode
  domainCode := labelProjection count ≫ countCode
  target := (naturalSection 0).reindex
    (projection (liftedDecode (labelProjection count ≫ countCode)) ≫ labelProjection count)
  endpoint := naturalSection e

noncomputable def charts := (data 0).outerResult
noncomputable def incompatible := (data 1).outerResult

def labelFiber (n : Nat) : (labels count).obj (point n) ≃ Fin n := Equiv.ulift
noncomputable def decodedLabelFiber (n : Nat) :
    (liftedDecode (labelCode count).code).obj (point n) ≃ Fin n :=
  ((labelCode count).decoding.app (point n)).toEquiv.trans (labelFiber n)

theorem zero_labels : IsEmpty ((liftedDecode (labelCode count).code).obj (point 0)) :=
  ⟨fun z => Fin.elim0 (decodedLabelFiber 0 z)⟩

theorem varying_labels : ¬ Nonempty
    ((liftedDecode (labelCode count).code).obj (point 1) ≃
      (liftedDecode (labelCode count).code).obj (point 2)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr ((decodedLabelFiber 1).symm.trans (e.trans (decodedLabelFiber 2)))
  simp at h

theorem zero_charts : IsEmpty ((liftedDecode charts.code).obj (point 0)) :=
  ⟨fun z => Fin.elim0 (charts.decoding.hom.app (point 0) z).1.down⟩

noncomputable def successorComparison := (data 0).outerComparison successorSub
noncomputable def twiceComparison := (data 0).outerComparison twiceSub
noncomputable def compositeComparison := (data 0).outerComparison (twiceSub ≫ successorSub)

example : successorSub ≠ 𝟙 context := successor_nonidentity
example : twiceSub ≠ 𝟙 context := twice_nonidentity
example : ((data 0).substitute successorSub).count.val (point 2) = ⟨3⟩ := rfl
example : ((data 0).substitute twiceSub).count.val (point 2) = ⟨4⟩ := rfl
example : ((data 0).substitute (twiceSub ≫ successorSub)).count.val (point 2) = ⟨5⟩ := rfl

example : (charts.filling.reindex successorSub).transport successorComparison =
    ((data 0).substitute successorSub).outerResult.filling := (data 0).outerComparison_filling _
example : (charts.filling.reindex twiceSub).transport twiceComparison =
    ((data 0).substitute twiceSub).outerResult.filling := (data 0).outerComparison_filling _
example : (charts.filling.reindex (twiceSub ≫ successorSub)).transport compositeComparison =
    ((data 0).substitute (twiceSub ≫ successorSub)).outerResult.filling :=
  (data 0).outerComparison_filling _
noncomputable def fullEquivalence := HomotopyEquivalence.ofIso compositeComparison

def lastDomain : Term (liftedDecode countCode) :=
  (Raising.raiseTerm CubicalSmallFamilies.selectedLast).reindex baseProjection

def innerWitness : Term (data 0).inner :=
  sigmaIntro (lastDomain.reindex (labelProjection count))
    ((homogeneousRefl (data 0).target).reindex
      (pair (𝟙 (labelContext count)) (lastDomain.reindex (labelProjection count))))

noncomputable def decodedInnerWitness : Term (liftedDecode (data 0).innerResult.code) :=
  Term.map (data 0).innerResult.decoding.inv innerWitness

private theorem cast_zero (m n : Nat) (h : m = n) :
    cast (congrArg (fun k => ULift.{1} (Fin (k+1))) h)
      ⟨⟨0, Nat.zero_lt_succ m⟩⟩ = ⟨⟨0, Nat.zero_lt_succ n⟩⟩ := by
  cases h
  rfl

def firstLabel : Term (labels (count.reindex successorSub)) where
  val x := ⟨⟨0, Nat.zero_lt_succ x.val.1.down⟩⟩
  property {x y} f := by
    exact cast_zero _ _ (congrArg ULift.down (count.property f))

noncomputable def positive : Term (liftedDecode ((data 0).substitute successorSub).outerResult.code) :=
  Term.map ((data 0).substitute successorSub).outerResult.decoding.inv
    (sigmaIntro firstLabel ((Term.map ((data 0).innerSubstitution successorSub).hom
      (innerWitness.reindex ((data 0).labelLift successorSub))).reindex (pair (𝟙 context) firstLabel)))

set_option backward.isDefEq.respectTransparency false in
theorem positive_label :
    sigmaFst (Term.map ((data 0).substitute successorSub).outerResult.decoding.hom positive) =
      firstLabel := by
  apply Term.ext
  intro x
  exact congrArg (fun v => v.1) (congrArg (fun k => k.app x
    ((sigmaIntro firstLabel ((Term.map ((data 0).innerSubstitution successorSub).hom
      (innerWitness.reindex ((data 0).labelLift successorSub))).reindex
        (pair (𝟙 context) firstLabel))).val x))
      ((data 0).substitute successorSub).outerResult.decoding.inv_hom_id)

/-- Empty D is rejected even at a nonempty label fiber. -/
def emptyData : Inputs context where
  count := count
  targetCode := naturalsCode
  domainCode := labelProjection count ≫ emptyCode
  target := (naturalSection 0).reindex
    (projection (liftedDecode (labelProjection count ≫ emptyCode)) ≫ labelProjection count)
  endpoint := naturalSection 0

theorem empty_domain (x : context.Elements) :
    IsEmpty ((liftedDecode emptyData.outerResult.code).obj x) :=
  ⟨fun z => Empty.elim (emptyFiber x (emptyData.outerResult.decoding.hom.app x z).2.1)⟩

def badData := (data 1).substitute successorSub

set_option maxHeartbeats 800000 in
theorem incompatible_endpoints : ¬ Nonempty (Term (liftedDecode badData.outerResult.code)) := by
  rintro ⟨z⟩
  let q := Term.map badData.outerResult.decoding.hom z
  let ρ := badData.selectedDisplay q
  let p := badData.selectedNativePath q
  let σ := ρ ≫ badData.display ≫ successorSub
  let obs := Functor.whiskerLeft σ.mapElements observeNatural
  have h := constantFamily_path_endpoints (homogeneousPathMap obs p)
  have e := congrArg (fun t => (t.val (point 1)).down) h
  let x := (Raising.lowerElements CubicalPresheaf.naturals).obj
    ((σ ≫ baseProjection).mapElements.obj (point 1))
  have h₀ := congrArg (fun k => k.app x (0 : Nat)) CubicalSmallFamilies.natDecode.inv_hom_id
  have h₁ := congrArg (fun k => k.app x (1 : Nat)) CubicalSmallFamilies.natDecode.inv_hom_id
  exact Nat.zero_ne_one (h₀.symm.trans (e.trans h₁))

/-- Two independent universe-code parameters and an actual generic function. -/
abbrev codeContext := total (SmallUniverse.family context)
def codeY : codeContext ⟶ smallFamilyCodes.{0} := projection (SmallUniverse.family context) ≫ parameter
def codeD : codeContext ⟶ smallFamilyCodes.{0} := SmallUniverse.code (generic (SmallUniverse.family context))
abbrev functions := Presheaf.pi (liftedDecode codeD)
  (liftedDecode (projection (liftedDecode codeD) ≫ codeY))
abbrev functionContext := total functions
def functionY : functionContext ⟶ smallFamilyCodes.{0} := projection functions ≫ codeY
def functionD : functionContext ⟶ smallFamilyCodes.{0} := projection functions ≫ codeD
def functionCount : Count functionContext :=
  count.reindex (projection functions ≫ projection (SmallUniverse.family context))
def targetFunction : Term (Presheaf.pi (liftedDecode functionD)
    (liftedDecode (projection (liftedDecode functionD) ≫ functionY))) :=
  Term.map (piReindexIso _ _ (projection functions)).hom (generic functions)
def labelledD : labelContext functionCount ⟶ smallFamilyCodes.{0} :=
  labelProjection functionCount ≫ functionD
def targetSection : Term (liftedDecode
    (projection (liftedDecode labelledD) ≫ labelProjection functionCount ≫ functionY)) :=
  (app targetFunction).reindex (liftSub (liftedDecode functionD) (labelProjection functionCount))
def genericData := genericEndpoint functionCount functionY labelledD targetSection
noncomputable def genericCharts := genericData.outerResult
noncomputable def genericStockInner := genericData.encodedInner

example : genericData.endpoint = generic (liftedDecode functionY) := rfl
example : genericCharts.filling.transport genericCharts.decoding = genericData.outerFiller :=
  genericData.outer_selected

end Examples.CubicalChartFamily
