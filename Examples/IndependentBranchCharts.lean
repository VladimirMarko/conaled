import Examples.ProperLocalBranches
import Examples.SmoothManifoldAction
import SquareKit.SmoothBranchActionComparison
import SquareKit.SmoothLocalDiffeomorphModel
import SquareKit.SmoothBranchComparison
import SquareKit.SmoothBranchGroupoid
import SquareKit.SmoothActionGroupoid

/-! Independent source charts can change branch indices on disconnected regions. -/
noncomputable section
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace Set Filter
open scoped Manifold ContDiff Topology Orbifolds.FiniteActionPresentation
namespace Examples.IndependentBranchCharts
open SquareKit SquareKit.ManifoldRealization Orbifolds.LocalBranches
open Orbifolds.FiniteActionPresentation Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
attribute [local instance] SmoothManifoldAction.trivial

abbrev Line := Space 1
abbrev I := modelWithCorners 1

def window : Opens Line := ⟨{x | x 0 ≠ 0}, isOpen_ne.preimage (continuous_apply 0)⟩

def switchedLabel (g : C4) (x : Line) : C4 := if x 0 < 0 then g else g * quarterTurn

theorem switchedLabel_injective (x : Line) : Function.Injective (fun g => switchedLabel g x) := by
  intro g h he
  by_cases hx : x 0 < 0
  · simpa [switchedLabel, hx] using he
  · simpa [switchedLabel, hx] using he

def switchedPiece (g : C4) : Opens (C4 × Line) := ⟨
  {a | a.2 ∈ window ∧ a.1 = switchedLabel g a.2}, by
    have he : {a : C4 × Line | a.2 ∈ window ∧ a.1 = switchedLabel g a.2} =
        ({a | a.2 0 < 0} ∩ {a | a.1 = g}) ∪
        ({a | 0 < a.2 0} ∩ {a | a.1 = g * quarterTurn}) := by
      ext a
      change (a.2 0 ≠ 0 ∧ a.1 = switchedLabel g a.2) ↔ _
      by_cases h : a.2 0 < 0
      · simp [switchedLabel, h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
      · constructor
        · intro ha
          exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt h) (Ne.symm ha.1), by simpa [switchedLabel, h] using ha.2⟩
        · rintro (ha | ha)
          · exact (h ha.1).elim
          · exact ⟨ne_of_gt ha.1, by simpa [switchedLabel, h] using ha.2⟩
    rw [he]
    exact ((isOpen_lt ((continuous_apply 0).comp continuous_snd) continuous_const).inter
      ((isOpen_discrete {g}).preimage continuous_fst)).union
      ((isOpen_lt continuous_const ((continuous_apply 0).comp continuous_snd)).inter
        ((isOpen_discrete {g * quarterTurn}).preimage continuous_fst))⟩

theorem switchedLabel_smooth (g : C4) :
    ContMDiff I 𝓘(ℝ, Fin 0 → ℝ) ∞ (fun x : window => switchedLabel g x.val) := by
  intro x
  by_cases hx : x.val 0 < 0
  · apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt ((continuous_apply 0).comp continuous_subtype_val)
      continuous_const).mem_nhds hx] with y hy
    exact ite_eq_left hy
  · have hp : 0 < x.val 0 := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm x.property)
    apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const
      ((continuous_apply 0).comp continuous_subtype_val)).mem_nhds hp] with y hy
    exact ite_eq_right (not_lt_of_ge (le_of_lt hy))

def switchedSource (g : C4) : Diffeomorph (arrowModel I) I (switchedPiece g) window ∞ where
  toFun a := ⟨a.val.2, a.property.1⟩
  invFun x := ⟨(switchedLabel g x.val, x.val), x.property, rfl⟩
  left_inv a := Subtype.ext (Prod.ext a.property.2.symm rfl)
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    (contMDiff_snd.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((switchedLabel_smooth g).prodMk contMDiff_subtype_val)

def switchedNative : Diagram (arrowModel I) I
    (source (G := C4) (M := Line)) target window window C4 where
  piece := switchedPiece
  domain _ := window
  sourceEquiv := switchedSource
  source_eq _ _ := rfl
  domain_le _ := le_rfl
  target_mem _ a := a.property.1
  disjoint := by
    intro g h hgh
    apply Opens.coe_disjoint.mp
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact hgh (switchedLabel_injective a.2 (ha.2.symm.trans hb.2))
  covers a := by
    change (a.2 ∈ window ∧ a.2 ∈ window) ↔ ∃ g, a.2 ∈ window ∧ a.1 = switchedLabel g a.2
    constructor
    · intro ha
      by_cases hx : a.2 0 < 0
      · exact ⟨a.1, ha.1, by simp [switchedLabel, hx]⟩
      · exact ⟨a.1 * quarterTurn⁻¹, ha.1, by simp [switchedLabel, hx, mul_assoc]⟩
    · rintro ⟨g,ha,_⟩
      exact ⟨ha,ha⟩

def fixedNative := ProperLocalBranches.finiteActionDiagram (G := C4) I
  (SmoothManifoldAction.smooth C4) window window

def switched := SmoothLocalDiffeomorphModel.diagram
  (source (G := C4) (M := Line)) (source_etale I) switchedNative

def fixed := SmoothLocalDiffeomorphModel.diagram
  (source (G := C4) (M := Line)) (source_etale I) fixedNative


@[simp] theorem switched_assemble (g : C4) (x : switched.domain g) :
    (switched.assemble g x).val = (switchedLabel g x.val, x.val) := rfl

@[simp] theorem fixed_assemble (g : C4) (x : fixed.domain g) :
    (fixed.assemble g x).val = (g, x.val) := rfl

theorem fixed_index (a : fixed.region) : (fixed.decompose a).1 = a.val.1 := by
  have h := fixed.mem_index a
  exact h.1.symm

theorem switched_index (a : switched.region) :
    a.val.1 = switchedLabel (switched.decompose a).1 a.val.2 :=
  (switched.mem_index a).2

theorem quarterTurn_ne_identity : quarterTurn ≠ (1 : C4) := by
  intro h
  have hi := congrArg (fun g : C4 => (g.val : ℂ).im) h
  norm_num [quarterTurn] at hi

def negativeArrow (g : C4) : fixed.region := ⟨(g, fun _ => -1), by
  constructor <;> change (-1 : ℝ) ≠ 0 <;> norm_num⟩
def positiveArrow (g : C4) : fixed.region := ⟨(g, fun _ => 1), by
  constructor <;> change (1 : ℝ) ≠ 0 <;> norm_num⟩

/-- No fixed relabelling recovers the independently selected branch indices. -/
theorem no_global_index_function : ¬ ∃ f : C4 → C4,
    ∀ a : fixed.region, (switched.decompose a).1 = f ((fixed.decompose a).1) := by
  rintro ⟨f,hf⟩
  have hn := switched_index (negativeArrow 1)
  have hp := switched_index (positiveArrow 1)
  rw [hf, fixed_index] at hn hp
  change 1 = switchedLabel (f 1) (fun _ => -1) at hn
  change 1 = switchedLabel (f 1) (fun _ => 1) at hp
  norm_num [switchedLabel] at hn hp
  rw [← hn, one_mul] at hp
  exact quarterTurn_ne_identity hp.symm

/-- The positive-component transition changes the identity-labelled index. -/
theorem positive_index_changes :
    (switched.decompose (positiveArrow 1)).1 ≠ (fixed.decompose (positiveArrow 1)).1 := by
  intro h
  have hp := switched_index (positiveArrow 1)
  rw [h, fixed_index] at hp
  change 1 = switchedLabel 1 (fun _ => 1) at hp
  norm_num [switchedLabel] at hp
  exact quarterTurn_ne_identity hp.symm

/-- Distinct ineffective arrows have the same endpoints and retain different branches. -/
theorem ineffective_arrows :
    fixed.source (positiveArrow quarterTurn) = fixed.source (positiveArrow 1) ∧
    fixed.target (positiveArrow quarterTurn) = fixed.target (positiveArrow 1) ∧
    switched.decompose (positiveArrow quarterTurn) ≠ switched.decompose (positiveArrow 1) := by
  refine ⟨rfl,rfl,?_⟩
  intro h
  have he := switched.equiv.injective h
  exact quarterTurn_ne_identity (congrArg (fun a : switched.region => a.val.1) he)


open SquareKit.SmoothBranchActionComparison SquareKit.SmoothManifoldAction
open SquareKit.EuclideanOpen SquareKit.SmoothOpenSite

/-- A constant actual arrow label over a disconnected test has varying chart indices. -/
def arrowFamily (g : C4) : External.SmoothMap SmoothClutching.punctured 1 switched.region := ⟨
  fun x => ⟨(g, x.val), by
    have hx : x.val 0 ≠ 0 := by
      have h := x.property
      change (1 : ℝ) * x.val 0 ≠ 0 at h
      simpa using h
    exact ⟨hx,hx⟩⟩,
  (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((SmoothLocalDiffeomorphModel.toModel_smooth
      (source (G := C4) (M := Line)) (source_etale I)).comp
      (contMDiff_const.prodMk contMDiff_subtype_val))⟩

def switchedSection := principalBranchEquiv switched SmoothClutching.punctured (arrowFamily 1)
def fixedSection := principalBranchEquiv fixed SmoothClutching.punctured (arrowFamily 1)

/-- A globally fixed actual arrow does not select one switched-chart summand. -/
theorem switchedSection_no_summand (i : C4) :
    ¬ ∃ b : embedding.obj SmoothClutching.punctured ⟶ object 1 (switched.domain i),
      b ≫ SheafCoproductLocal.inclusion (fun j => object 1 (switched.domain j)) i = switchedSection := by
  intro hb
  obtain ⟨f,hf⟩ := (principalBranchEquiv_factors_iff switched (arrowFamily 1) i).mp hb
  have hn := congrArg (fun a : switched.region => a.val.1) (hf SmoothOrdinaryComparison.negativePoint)
  have hp := congrArg (fun a : switched.region => a.val.1) (hf SmoothOrdinaryComparison.positivePoint)
  have xn := congrArg (fun a : switched.region => a.val.2) (hf SmoothOrdinaryComparison.negativePoint)
  have xp := congrArg (fun a : switched.region => a.val.2) (hf SmoothOrdinaryComparison.positivePoint)
  change switchedLabel i (f.val SmoothOrdinaryComparison.negativePoint).val = 1 at hn
  change switchedLabel i (f.val SmoothOrdinaryComparison.positivePoint).val = 1 at hp
  change (f.val SmoothOrdinaryComparison.negativePoint).val = (fun _ => -1) at xn
  change (f.val SmoothOrdinaryComparison.positivePoint).val = (fun _ => 1) at xp
  rw [xn] at hn
  rw [xp] at hp
  norm_num [switchedLabel] at hn hp
  rw [hn, one_mul] at hp
  exact quarterTurn_ne_identity hp


open SquareKit.SmoothBranchComparison SquareKit.SmoothBranchRealization

theorem comparison_section :
    fixedSection ≫ (comparisonIso fixed switched).hom = switchedSection := by
  apply (cancel_mono (assemblyIso switched).hom).mp
  rw [assemblyIso_hom]
  rw [Category.assoc, comparison_assembly]
  exact (principalBranchEquiv_assembly fixed _ (arrowFamily 1)).trans
    (principalBranchEquiv_assembly switched _ (arrowFamily 1)).symm

/-- The public independent comparison produces a section without a global branch. -/
theorem comparison_section_no_summand (i : C4) :
    ¬ ∃ b : embedding.obj SmoothClutching.punctured ⟶ object 1 (switched.domain i),
      b ≫ SheafCoproductLocal.inclusion (fun j => object 1 (switched.domain j)) i =
        fixedSection ≫ (comparisonIso fixed switched).hom := by
  rw [comparison_section]
  exact switchedSection_no_summand i

theorem fixed_domain (g : C4) : fixed.domain g = window := by
  ext x
  change (x ∈ (sourceChart I g).target ∧
    (sourceChart I g).invFun x ∈ arrowRegion
      (source_etale I).contMDiff (target_etale I (Examples.SmoothManifoldAction.smooth C4)).contMDiff
      window window) ↔ x ∈ window
  change (True ∧ x ∈ window ∧ x ∈ window) ↔ x ∈ window
  simp


/-- The original section uses a single fixed branch before independent comparison. -/
theorem fixedSection_factors :
    ∃ b : embedding.obj SmoothClutching.punctured ⟶ object 1 (fixed.domain 1),
      b ≫ SheafCoproductLocal.inclusion (fun j => object 1 (fixed.domain j)) 1 = fixedSection := by
  apply (principalBranchEquiv_factors_iff fixed (arrowFamily 1) 1).mpr
  refine ⟨⟨fun x => ⟨x.val, ?_⟩, ?_⟩, fun _ => rfl⟩
  · rw [fixed_domain]
    have h := x.property
    change (1 : ℝ) * x.val 0 ≠ 0 at h
    change x.val 0 ≠ 0
    simpa using h
  · exact (ContMDiff.subtypeVal_comp_iff _ _).mp contMDiff_subtype_val

/-- The comparison retains distinct ineffective arrows on the whole test stage. -/
theorem comparison_ineffective_distinct :
    principalBranchEquiv fixed SmoothClutching.punctured (arrowFamily quarterTurn) ≫
      (comparisonIso fixed switched).hom ≠
    fixedSection ≫ (comparisonIso fixed switched).hom := by
  intro h
  have hf := (cancel_mono (comparisonIso fixed switched).hom).mp h
  have ha := (principalBranchEquiv fixed SmoothClutching.punctured).injective hf
  exact quarterTurn_ne_identity (congrArg
    (fun f : External.SmoothMap SmoothClutching.punctured 1 fixed.region =>
      (f.val SmoothOrdinaryComparison.positivePoint).val.1) ha)

abbrev Arrow := SmoothLocalDiffeomorphModel.Model
  (Orbifolds.FiniteActionPresentation.source (G := C4) (M := Line)) (source_etale I)

theorem source_smooth : ContMDiff I I ∞ (fun a : Arrow => a.2) :=
  SmoothLocalDiffeomorphModel.projection_smooth
    (Orbifolds.FiniteActionPresentation.source (G := C4) (M := Line)) (source_etale I)

def negativeWindow : Opens Line := ⟨{x | x 0 < 0}, isOpen_lt (continuous_apply 0) continuous_const⟩
theorem negativeWindow_le : negativeWindow ≤ window := fun _ hx => ne_of_lt hx

def partialFixed := fixed.restrict source_smooth source_smooth window negativeWindow le_rfl negativeWindow_le
def partialSwitched := switched.restrict source_smooth source_smooth window negativeWindow le_rfl negativeWindow_le

theorem partial_domain (g : C4) : partialSwitched.domain g = negativeWindow := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha.2.2
  · intro hx
    exact ⟨(switchedLabel g x,x), ⟨⟨negativeWindow_le hx,rfl⟩,negativeWindow_le hx,hx⟩,rfl⟩

theorem partial_domain_nonempty (g : C4) : Set.Nonempty (partialSwitched.domain g : Set Line) := by
  rw [partial_domain]
  exact ⟨fun _ => -1, by change (-1 : ℝ) < 0; norm_num⟩

theorem partial_domain_proper (g : C4) : partialSwitched.domain g < window := by
  rw [partial_domain]
  refine lt_of_le_of_ne negativeWindow_le ?_
  intro h
  have hp : (fun _ : Fin 1 => (1 : ℝ)) ∈ window := by change (1 : ℝ) ≠ 0; norm_num
  rw [← h] at hp
  change (1 : ℝ) < 0 at hp
  linarith

/-- Shrinking the target to a proper half-window commutes with chart comparison. -/
theorem partial_comparison :
    (comparisonIso partialFixed partialSwitched).hom ≫
      branchRestriction switched source_smooth source_smooth window negativeWindow le_rfl negativeWindow_le =
    branchRestriction fixed source_smooth source_smooth window negativeWindow le_rfl negativeWindow_le ≫
      (comparisonIso fixed switched).hom :=
  comparison_restriction fixed switched source_smooth source_smooth window negativeWindow le_rfl negativeWindow_le

def emptyFixed := fixed.restrict source_smooth source_smooth window ⊥ le_rfl bot_le
def emptySwitched := switched.restrict source_smooth source_smooth window ⊥ le_rfl bot_le

theorem empty_domain (g : C4) : emptySwitched.domain g = ⊥ := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha.2.2
  · exact False.elim

/-- The public comparison also applies when all restricted domains are empty. -/
theorem empty_comparison :
    (comparisonIso emptyFixed emptySwitched).hom ≫
      branchRestriction switched source_smooth source_smooth window ⊥ le_rfl bot_le =
    branchRestriction fixed source_smooth source_smooth window ⊥ le_rfl bot_le ≫
      (comparisonIso fixed switched).hom :=
  comparison_restriction fixed switched source_smooth source_smooth window ⊥ le_rfl bot_le


/-- No function on indices, even with arbitrary component maps, describes the comparison. -/
theorem comparison_not_global_reindex : ¬ ∃ f : C4 → C4,
    ∀ g, ∃ k : object 1 (fixed.domain g) ⟶ object 1 (switched.domain (f g)),
      SheafCoproductLocal.inclusion (fun j => object 1 (fixed.domain j)) g ≫
        (comparisonIso fixed switched).hom =
      k ≫ SheafCoproductLocal.inclusion (fun j => object 1 (switched.domain j)) (f g) := by
  rintro ⟨f,hf⟩
  obtain ⟨b,hb⟩ := fixedSection_factors
  obtain ⟨k,hk⟩ := hf 1
  apply comparison_section_no_summand (f 1)
  refine ⟨b ≫ k, ?_⟩
  rw [Category.assoc, ← hk, ← Category.assoc, hb]

/-- Restricting the disconnected section commutes with its independent chart transition. -/
theorem comparison_section_restrict {Q : Domain} (r : Q ⟶ SmoothClutching.punctured) :
    embedding.map r ≫ fixedSection ≫ (comparisonIso fixed switched).hom =
      principalBranchEquiv switched Q ((arrowFamily 1).restrict r) := by
  rw [comparison_section]
  exact (principalBranchEquiv_restrict switched r (arrowFamily 1)).symm


/-- One branch meets the same named switched branch on precisely the negative component. -/
theorem identity_overlap : overlapDomain fixed switched 1 1 = negativeWindow := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    have hlabel : a.1 = (1 : C4) := ha.1.1
    have hswitch : a.1 = switchedLabel 1 a.2 := ha.2.2
    by_contra hn
    change ¬ a.2 0 < 0 at hn
    rw [hlabel] at hswitch
    have hq : (1 : C4) = quarterTurn := by simpa [switchedLabel, hn] using hswitch
    exact quarterTurn_ne_identity hq.symm
  · intro hx
    refine ⟨(1,x), ?_,rfl⟩
    refine ⟨⟨rfl,negativeWindow_le hx,negativeWindow_le hx⟩,negativeWindow_le hx,?_⟩
    exact (ite_eq_left hx).symm

/-- Independent overlap domains can be proper and nonempty. -/
theorem identity_overlap_proper :
    Set.Nonempty (overlapDomain fixed switched 1 1 : Set Line) ∧
    overlapDomain fixed switched 1 1 < window := by
  rw [identity_overlap]
  constructor
  · exact ⟨fun _ => -1, by change (-1 : ℝ) < 0; norm_num⟩
  · rw [← partial_domain 1]
    exact partial_domain_proper 1

/-- On the negative refinement, distinct named branches have an empty overlap. -/
theorem distinct_negative_overlap : overlapDomain partialFixed partialSwitched 1 quarterTurn = ⊥ := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    have hid : a.1 = (1 : C4) := ha.1.1.1
    have hneg : a.2 0 < 0 := ha.2.2.2
    have he : a.1 = switchedLabel quarterTurn a.2 := ha.2.1.2
    rw [hid] at he
    have hq : (1 : C4) = quarterTurn := by simpa [switchedLabel,hneg] using he
    exact (quarterTurn_ne_identity hq.symm).elim
  · exact False.elim

/-- The selected groupoid has the original smooth action arrows. -/
abbrev selectedGroupoid := SquareKit.SmoothActionGroupoid.groupoid
  (Examples.SmoothManifoldAction.smooth C4)

/-- Any independently constructed diagram for this action supplies an operation chart. -/
def operationChart (D : Diagram I I (fun a : Arrow => a.2) (fun a => a.2)
    window window C4) :=
  SmoothBranchGroupoid.chart D source_smooth source_smooth selectedGroupoid.toOperations
    (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom]
        exact (SquareKit.SmoothActionGroupoid.groupoid_source
          (Examples.SmoothManifoldAction.smooth C4)).symm)
    (by simp only [Iso.refl_hom]
        exact (SquareKit.SmoothActionGroupoid.groupoid_target
          (Examples.SmoothManifoldAction.smooth C4)).symm)

abbrev fixedChart := operationChart fixed
abbrev switchedChart := operationChart switched

/-- Generic recovery gives precisely the already checked independent-chart transition. -/
theorem operation_comparison {T : Sheaf topology Type}
    (m n : T ⟶ object 1 window) (f : fixedChart.Arrow m n) :
    (fixedChart.comparison switchedChart m n f).val =
      f.val ≫ (comparisonIso fixed switched).hom :=
  SmoothBranchGroupoid.comparison_map fixed source_smooth source_smooth
    selectedGroupoid.toOperations (Iso.refl _) (Iso.refl _) _ _ switched m n f

/-- The actual unit changes coordinates through the independent comparison. -/
theorem operation_unit_comparison {T : Sheaf topology Type} (m : T ⟶ object 1 window) :
    (SheafGroupoid.Chart.ident fixedChart m).val ≫ (comparisonIso fixed switched).hom =
      (SheafGroupoid.Chart.ident switchedChart m).val := by
  rw [← operation_comparison]
  exact congrArg Subtype.val (SheafGroupoid.Chart.comparison_ident fixedChart switchedChart m)

/-- Inversion in the independently chosen output chart uses the same actual inverse. -/
theorem operation_inverse_comparison {T : Sheaf topology Type}
    {m n : T ⟶ object 1 window} (f : fixedChart.Arrow m n) :
    (fixedChart.inverse fixedChart f).val ≫ (comparisonIso fixed switched).hom =
      (switchedChart.inverse switchedChart (fixedChart.comparison switchedChart m n f)).val := by
  rw [← operation_comparison]
  exact congrArg Subtype.val
    (fixedChart.comparison_inverse switchedChart fixedChart switchedChart f)

/-- Both input charts and the output chart may change independently of the multiplication. -/
theorem operation_composition_comparison {T : Sheaf topology Type}
    {m n p : T ⟶ object 1 window} (f : fixedChart.Arrow m n) (g : fixedChart.Arrow n p) :
    (fixedChart.comp fixedChart fixedChart f g).val ≫ (comparisonIso fixed switched).hom =
      (switchedChart.comp switchedChart switchedChart
        (fixedChart.comparison switchedChart m n f)
        (fixedChart.comparison switchedChart n p g)).val := by
  rw [← operation_comparison]
  exact congrArg Subtype.val
    (fixedChart.comparison_comp switchedChart fixedChart switchedChart fixedChart switchedChart f g)

/-- The endpoint map of the family of actual units on the disconnected test. -/
def unitParameter : embedding.obj SmoothClutching.punctured ⟶ object 1 window :=
  hat (fixed.source ∘ (arrowFamily 1).val)
    ((fixed.source_smooth source_smooth).comp (arrowFamily 1).property)

/-- The concrete family retains the common endpoint lift. -/
def fixedUnitCoordinate : fixedChart.Arrow unitParameter unitParameter :=
  ⟨fixedSection, by
    constructor
    · change fixedSection ≫ branchSource fixed = unitParameter
      rw [← assembly_source fixed source_smooth, ← Category.assoc]
      rw [show fixedSection ≫ assembly fixed = hat (arrowFamily 1).val (arrowFamily 1).property from
        principalBranchEquiv_assembly fixed _ (arrowFamily 1)]
      exact hat_postcomp _ _ _ _
    · change fixedSection ≫ branchTarget fixed source_smooth = unitParameter
      rw [← assembly_target fixed source_smooth, ← Category.assoc]
      rw [show fixedSection ≫ assembly fixed = hat (arrowFamily 1).val (arrowFamily 1).property from
        principalBranchEquiv_assembly fixed _ (arrowFamily 1)]
      exact hat_postcomp _ _ _ _⟩

/-- Coordinate identity is proved by recovering the original geometric unit. -/
theorem fixedUnitCoordinate_ident :
    fixedUnitCoordinate = SheafGroupoid.Chart.ident fixedChart unitParameter := by
  apply (fixedChart.arrowEquiv unitParameter unitParameter).injective
  rw [SheafGroupoid.Chart.ident_recovery]
  apply SheafGroupoid.Operations.Arrow.ext
  change fixedSection ≫ (assembly fixed ≫
      map (Subtype.val : fixed.region → Arrow) contMDiff_subtype_val ≫ (Iso.refl _).hom) =
    (unitParameter ≫ (map (Subtype.val : window → Line) contMDiff_subtype_val ≫
      (Iso.refl _).hom)) ≫ selectedGroupoid.unit
  simp only [Iso.refl_hom, Category.comp_id]
  rw [← Category.assoc, show fixedSection ≫ assembly fixed = hat (arrowFamily 1).val (arrowFamily 1).property from
    principalBranchEquiv_assembly fixed _ (arrowFamily 1)]
  rw [SquareKit.SmoothActionGroupoid.groupoid_unit]
  unfold unitParameter SquareKit.SmoothActionGroupoid.unitMap
  rw [hat_postcomp, hat_postcomp, hat_postcomp]
  rfl

/-- Even the actual groupoid identity needs multiple independently named branches. -/
theorem switched_identity_section :
    (SheafGroupoid.Chart.ident switchedChart unitParameter).val = switchedSection := by
  rw [← operation_unit_comparison, ← fixedUnitCoordinate_ident]
  exact comparison_section

theorem switched_identity_no_summand (i : C4) :
    ¬ ∃ b : embedding.obj SmoothClutching.punctured ⟶ object 1 (switched.domain i),
      b ≫ SheafCoproductLocal.inclusion (fun j => object 1 (switched.domain j)) i =
        (SheafGroupoid.Chart.ident switchedChart unitParameter).val := by
  rw [switched_identity_section]
  exact switchedSection_no_summand i

end Examples.IndependentBranchCharts
