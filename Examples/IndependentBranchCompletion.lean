import Examples.IndependentBranchCharts
import Examples.GroupoidCompletion
import SquareKit.SheafGroupoidCompletion

/-! Independent branch coordinates complete the action restricted to the punctured object.
The object atlas is the identity; the punctured window is not treated as a cover of the line. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Manifold ContDiff
namespace Examples.IndependentBranchCompletion
open SquareKit ManifoldRealization SmoothOpenSite SmoothBranchRealization EuclideanOpen
open Orbifolds.QuarterTurn IndependentBranchCharts
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : MulAction C4 window where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smooth (g : C4) : ContMDiff I I ∞ (fun x : window => g • x) := contMDiff_id

abbrev restrictedGroupoid := SmoothActionGroupoid.groupoid smooth
abbrev restrictedAction := SmoothActionGroupoid.action smooth
abbrev restrictedArrowIso := SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := window)

/-- Restriction keeps the actual groupoid proper and étale. -/
theorem restricted_proper_etale :
    IsProperMap (fun a : SmoothActionGroupoid.ArrowModel (d := 1) (G := C4) (M := window) =>
      (SmoothActionGroupoid.source a, SmoothActionGroupoid.target a)) ∧
      IsLocalDiffeomorph I I ∞ (SmoothActionGroupoid.source (d := 1) (G := C4) (M := window)) ∧
      IsLocalDiffeomorph I I ∞ (SmoothActionGroupoid.target (d := 1) (G := C4) (M := window)) :=
  SmoothActionGroupoid.proper_etale smooth

def domainIso (g : C4) : object 1 (fixed.domain g) ≅ object 1 window :=
  eqToIso (congrArg (fun U : Opens Line => object 1 U) (fixed_domain g))

def fixedCoordinatesIso : branches fixed ≅ SheafCoproductLocal.total (fun _ : C4 => object 1 window) :=
  Sigma.mapIso domainIso

/-- Actual restricted arrows are recovered from the original smooth branch assembly. -/
def regionIso : arrowObject fixed ≅ restrictedGroupoid.arrows :=
  (assemblyIso fixed).symm ≪≫ fixedCoordinatesIso ≪≫
    SmoothActionGroupoid.coproductArrowIso (d := 1) (G := C4) (M := window)

private theorem inclusion_identity {U V : Opens Line} (h : U = V) :
    map (Opens.inclusion h.le) (contMDiff_inclusion h.le) =
      (eqToIso (congrArg (fun W : Opens Line => object 1 W) h)).hom := by
  subst V
  exact map_id

theorem domainIso_source (g : C4) : (domainIso g).hom =
    map (fixed.domainInclusion g) (contMDiff_inclusion (fixed.domain_le g)) := by
  exact (inclusion_identity (fixed_domain g)).symm


def fixedAssemblyIso : branches fixed ≅ restrictedGroupoid.arrows :=
  fixedCoordinatesIso ≪≫ SmoothActionGroupoid.coproductArrowIso (d := 1) (G := C4) (M := window)

theorem fixedAssembly_source : fixedAssemblyIso.hom ≫ restrictedGroupoid.source =
    branchSource fixed := by
  rw [SmoothActionGroupoid.groupoid_source]
  apply colimit.hom_ext
  rintro ⟨g⟩
  change Sigma.ι _ g ≫ ((fixedCoordinatesIso.hom ≫ _) ≫ _) = _
  simp only [fixedCoordinatesIso, ← Category.assoc, Sigma.ι_mapIso_hom]
  rw [Category.assoc, Category.assoc, SmoothActionGroupoid.inclusion_coproductArrowIso_assoc]
  rw [← map_comp]
  change (domainIso g).hom ≫ map (id : window → window) contMDiff_id = _
  rw [map_id, Category.comp_id, domainIso_source]
  exact (SheafCoproductLocal.inclusion_desc _
    (fun g => map (fixed.domainInclusion g) (contMDiff_inclusion (fixed.domain_le g))) g).symm

theorem fixed_source_target : branchSource fixed = branchTarget fixed source_smooth := by
  rw [← assembly_source fixed source_smooth, ← assembly_target fixed source_smooth]
  rfl

theorem fixedAssembly_target : fixedAssemblyIso.hom ≫ restrictedGroupoid.target =
    branchTarget fixed source_smooth := by
  rw [SmoothActionGroupoid.groupoid_target]
  have h := fixedAssembly_source
  rw [SmoothActionGroupoid.groupoid_source] at h
  exact h.trans fixed_source_target

/-- A complete arrow chart over the identity object atlas. -/
def fixedChart : SheafGroupoid.Chart restrictedGroupoid.toOperations
    (𝟙 (object 1 window)) (𝟙 (object 1 window)) where
  coordinates := branches fixed
  source := branchSource fixed
  target := branchTarget fixed source_smooth
  assembly := fixedAssemblyIso.hom
  isPullback := by
    apply IsPullback.of_horiz_isIso
    constructor
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
      exact fixedAssembly_source.trans
        (prod.lift_fst (branchSource fixed) (branchTarget fixed source_smooth)).symm
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd, Category.comp_id]
      exact fixedAssembly_target.trans
        (prod.lift_snd (branchSource fixed) (branchTarget fixed source_smooth)).symm

open SmoothBranchComparison

def switchedAssemblyIso : branches switched ≅ restrictedGroupoid.arrows :=
  comparisonIso switched fixed ≪≫ fixedAssemblyIso

theorem switchedAssembly_source : switchedAssemblyIso.hom ≫ restrictedGroupoid.source =
    branchSource switched := by
  change ((comparisonIso switched fixed).hom ≫ fixedAssemblyIso.hom) ≫ _ = _
  rw [Category.assoc, fixedAssembly_source]
  exact comparison_source switched fixed source_smooth

theorem switchedAssembly_target : switchedAssemblyIso.hom ≫ restrictedGroupoid.target =
    branchTarget switched source_smooth := by
  change ((comparisonIso switched fixed).hom ≫ fixedAssemblyIso.hom) ≫ _ = _
  rw [Category.assoc, fixedAssembly_target]
  exact comparison_target switched fixed source_smooth

/-- Independently selected branches form another complete chart of the restricted groupoid. -/
def switchedChart : SheafGroupoid.Chart restrictedGroupoid.toOperations
    (𝟙 (object 1 window)) (𝟙 (object 1 window)) where
  coordinates := branches switched
  source := branchSource switched
  target := branchTarget switched source_smooth
  assembly := switchedAssemblyIso.hom
  isPullback := by
    apply IsPullback.of_horiz_isIso
    constructor
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
      exact switchedAssembly_source.trans
        (prod.lift_fst (branchSource switched) (branchTarget switched source_smooth)).symm
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd, Category.comp_id]
      exact switchedAssembly_target.trans
        (prod.lift_snd (branchSource switched) (branchTarget switched source_smooth)).symm

/-- Restriction to the punctured object still reconstructs the original geometric arrows. -/
theorem switched_assembly_recovery : switchedChart.assembly = assembly switched ≫ regionIso.hom := by
  change (comparisonIso switched fixed).hom ≫ fixedAssemblyIso.hom = _
  rw [comparisonIso_hom]
  rfl

theorem fixed_assembly_recovery : fixedChart.assembly = assembly fixed ≫ regionIso.hom := by
  change fixedAssemblyIso.hom = assembly fixed ≫ ((assemblyIso fixed).inv ≫ fixedAssemblyIso.hom)
  rw [← Category.assoc]
  rw [← assemblyIso_hom]
  simp

/-- The completion chart transition is the independent geometric transition. -/
theorem completion_comparison {T : Sheaf topology Type}
    (m n : T ⟶ object 1 window) (f : fixedChart.Arrow m n) :
    (fixedChart.comparison switchedChart m n f).val =
      f.val ≫ (comparisonIso fixed switched).hom := by
  apply (cancel_mono switchedAssemblyIso.hom).mp
  have h := congrArg SheafGroupoid.Operations.Arrow.map
    (fixedChart.comparison_recovery switchedChart m n f)
  change (fixedChart.comparison switchedChart m n f).val ≫ switchedAssemblyIso.hom =
    f.val ≫ fixedAssemblyIso.hom at h
  rw [h]
  change f.val ≫ fixedAssemblyIso.hom =
    (f.val ≫ (comparisonIso fixed switched).hom) ≫
      ((comparisonIso switched fixed).hom ≫ fixedAssemblyIso.hom)
  rw [Category.assoc, ← Category.assoc (comparisonIso fixed switched).hom,
    comparison_trans, comparison_refl]
  simp

open scoped CategoryTheory.Pseudofunctor.StrongTrans

abbrev output := SheafGroupoidCompletion.completion restrictedAction
abbrev fixedUnit := SheafGroupoidCompletion.chartUnit restrictedAction restrictedArrowIso fixedChart
abbrev switchedUnit := SheafGroupoidCompletion.chartUnit restrictedAction restrictedArrowIso switchedChart

/-- The actual chart transition leaves the completed torsor and all its arrows unchanged. -/
theorem change_completion (X : Sheaf topology Type) :
    fixedChart.changeFunctor (T := X) switchedChart ⋙
        SheafGroupoidCompletion.chartQuotient restrictedAction restrictedArrowIso switchedChart =
      SheafGroupoidCompletion.chartQuotient restrictedAction restrictedArrowIso fixedChart :=
  SheafGroupoidCompletion.changeChart_quotient (X := X) restrictedAction restrictedArrowIso fixedChart switchedChart

/-- Completion units agree by an invertible modification induced by the actual chart transition. -/
def unitComparison : PseudofunctorCoherence.ModificationIso
    (Pseudofunctor.StrongTrans.vcomp (fixedChart.changeTransformation switchedChart) switchedUnit)
    fixedUnit :=
  SheafGroupoidCompletion.chartUnitComparison restrictedAction restrictedArrowIso fixedChart switchedChart

/-- Independent comparison commutes with every parameter restriction, including covers. -/
theorem change_restriction {X Y : Sheaf topology Type} (r : Y ⟶ X) :
    fixedChart.changeFunctor switchedChart ⋙ switchedChart.restriction r =
      fixedChart.restriction r ⋙ fixedChart.changeFunctor switchedChart :=
  fixedChart.changeFunctor_restriction switchedChart r

theorem change_roundtrip (X : Sheaf topology Type) :
    fixedChart.changeFunctor (T := X) switchedChart ⋙ switchedChart.changeFunctor fixedChart =
      𝟭 (fixedChart.Object X) := by
  rw [SheafGroupoid.Chart.changeFunctor_comp, SheafGroupoid.Chart.changeFunctor_self]

example : fixedChart.pseudofunctor.IsPrestack (SheafCover.topology (J := topology)) := inferInstance
example : switchedChart.pseudofunctor.IsPrestack (SheafCover.topology (J := topology)) := inferInstance

/-- Local action labels still act trivially on the restricted object manifold. -/
theorem restricted_action_trivial (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup C4).obj.obj U) (x : (object 1 window).obj.obj U) :
    restrictedAction.act U g x = x := by
  let representation := SmoothManifoldAction.representation smooth
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (object 1 window).property)
    (Presheaf.imageSieve (constantLabel C4) g)
    (Presheaf.imageSieve_mem topology (constantLabel C4) g)).isSeparatedFor.ext
  intro V f hf
  obtain ⟨k, hk⟩ := hf
  rw [restrictedAction.natural, ← hk]
  change representation.act _ ((constantLabel C4).app _ k) _ = _
  rw [representation.act_constant]
  change (map (id : window → window) contMDiff_id).hom.app _ _ = _
  rw [map_id]
  rfl

/-- A constant target inside the restricted object, for arbitrary sheaf parameters. -/
def negativeTarget (X : Sheaf topology Type) : X ⟶ object 1 window :=
  SmoothOpenSite.tuple (fun i : Fin 0 => Fin.elim0 i) ≫ (fullPowerIso 0).inv ≫
    SmoothManifoldAction.hat (fun _ : ordinaryOpen (EuclideanOpen.full 0) =>
      (⟨fun _ => -1, by change (-1 : ℝ) ≠ 0; norm_num⟩ : window)) contMDiff_const

/-- Genuine descent data retains the nontrivial torsor over the punctured-object quotient. -/
def genuine : SheafActionQuotient.Object restrictedAction SmoothClutching.base :=
  GroupoidCompletion.invariantTarget restrictedAction SmoothTorsors.nontrivialTorsor
    (negativeTarget SmoothClutching.base) (fun U g _ => restricted_action_trivial U g _)

def switchedFullyFaithful (X : Sheaf topology Type) :
    (StackDescentTransformation.component switchedUnit X).FullyFaithful :=
  SheafGroupoidCompletion.chartFullyFaithful restrictedAction restrictedArrowIso switchedChart

/-- The chart completion supplies a covering branch presentation of the genuine torsor. -/
def localPresentation : StackificationUniversal.LocalPresentation
    (SheafCover.topology (J := topology)) switchedUnit genuine :=
  StackificationUniversal.presentation
    (SheafGroupoidCompletion.chartLocallyGenerating restrictedAction restrictedArrowIso switchedChart) genuine

def localData := localPresentation.sourceData switchedFullyFaithful

/-- No global independently indexed branch object realizes these local data. -/
theorem no_global_branch_chart :
    ¬ ∃ N : switchedChart.Object SmoothClutching.base,
      Nonempty ((switchedChart.pseudofunctor.toDescentData
        (fun _ : Unit => localPresentation.cover)).obj N ≅ localData) := by
  rintro ⟨N, ⟨h⟩⟩
  let recovery := localPresentation.ambientRecovery switchedFullyFaithful N h
  exact SmoothTorsors.nontrivialTorsor_no_section
    ⟨SheafTorsor.sectionOfArrow recovery.hom.torsorArrow⟩

def baseObject : switchedChart.Object SmoothTorsors.point :=
  ⟨negativeTarget SmoothTorsors.point⟩

def labelledLoop (g : C4) :
    SheafActionPresentation.Object.mk (a := restrictedAction) (negativeTarget SmoothTorsors.point) ⟶
      SheafActionPresentation.Object.mk (a := restrictedAction) (negativeTarget SmoothTorsors.point) :=
  ⟨constantSection _ g, by ext U z; exact restricted_action_trivial U _ _⟩

def branchLoop (g : C4) : baseObject ⟶ baseObject :=
  switchedChart.fullyFaithful.preimage
    ((SheafGroupoidCompletion.toPresentationFullyFaithful restrictedAction restrictedArrowIso).preimage
      (labelledLoop g))

@[simp] theorem branchLoop_recovery (g : C4) :
    (SheafGroupoidCompletion.toPresentation restrictedAction restrictedArrowIso).map
      (switchedChart.toGroupoid.map (branchLoop g)) = labelledLoop g := by
  rw [branchLoop, switchedChart.fullyFaithful.map_preimage]
  exact (SheafGroupoidCompletion.toPresentationFullyFaithful restrictedAction restrictedArrowIso).map_preimage _

theorem branchLoop_distinct : branchLoop quarterTurn ≠ branchLoop 1 := by
  intro h
  have hh := congrArg (fun k =>
    (SheafGroupoidCompletion.toPresentation restrictedAction restrictedArrowIso).map
      (switchedChart.toGroupoid.map k)) h
  rw [branchLoop_recovery, branchLoop_recovery] at hh
  have he := congrArg (fun k => k.label) hh
  exact SmoothTorsors.nonidentity_loop (congrArg SheafTorsor.regularArrow he)

/-- The selected branch completion unit retains ineffective automorphisms. -/
theorem completed_branchLoop_distinct :
    (SheafGroupoidCompletion.chartQuotient restrictedAction restrictedArrowIso switchedChart).map
        (branchLoop quarterTurn) ≠
      (SheafGroupoidCompletion.chartQuotient restrictedAction restrictedArrowIso switchedChart).map
        (branchLoop 1) := by
  intro h
  exact branchLoop_distinct
    ((SheafGroupoidCompletion.chartFullyFaithful restrictedAction restrictedArrowIso switchedChart).map_injective h)

/-- Common smaller rectangles commute with the same assembly used by completion. -/
theorem partial_change_assembly :
    branchRestriction fixed source_smooth source_smooth window negativeWindow le_rfl negativeWindow_le ≫
        (comparisonIso fixed switched).hom ≫ switchedChart.assembly =
      (comparisonIso partialFixed partialSwitched).hom ≫
        branchRestriction switched source_smooth source_smooth window negativeWindow le_rfl negativeWindow_le ≫
          switchedChart.assembly := by
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ switchedChart.assembly) partial_comparison.symm

variable (T : Pseudofunctor (LocallyDiscrete (Sheaf topology Type)ᵒᵖ) Cat.{0,1})
  [T.IsStack (SheafCover.topology (J := topology))]

/-- The independently indexed branch presentation has the constructed quotient as completion. -/
def fixedUniversal : (output ⟶ T) ≌ (fixedChart.pseudofunctor ⟶ T) :=
  SheafGroupoidCompletion.chartUniversalEquivalence restrictedAction restrictedArrowIso fixedChart T

def switchedUniversal : (output ⟶ T) ≌ (switchedChart.pseudofunctor ⟶ T) :=
  SheafGroupoidCompletion.chartUniversalEquivalence restrictedAction restrictedArrowIso switchedChart T

/-- The full mapping-category equivalences respect the independently defined branch change. -/
def universalComparison :
    (switchedUniversal T).functor ⋙
        StackLocalGeneration.restriction (fixedChart.changeTransformation switchedChart) T ≅
      (fixedUniversal T).functor :=
  SheafGroupoidCompletion.changeChartRestrictionComparison
    restrictedAction restrictedArrowIso fixedChart T switchedChart

/-- The universal equivalence is restriction along the concrete branch completion unit. -/
example : (switchedUniversal T).functor = StackLocalGeneration.restriction switchedUnit T := rfl

/-- Natural transformations, including arbitrary modifications, recover through branch coordinates. -/
def switchedModifications (Φ Ψ : output ⟶ T) :
    (Φ ⟶ Ψ) ≃ (switchedUnit ≫ Φ ⟶ switchedUnit ≫ Ψ) :=
  SheafGroupoidCompletion.chartModificationEquiv restrictedAction restrictedArrowIso switchedChart T Φ Ψ

/-- The extension comparison includes covering refinements and arbitrary substitution. -/
def switchedRecovery (θ : switchedChart.pseudofunctor ⟶ T) :=
  SheafGroupoidCompletion.chartExtensionRecovery restrictedAction restrictedArrowIso switchedChart T θ

end Examples.IndependentBranchCompletion
