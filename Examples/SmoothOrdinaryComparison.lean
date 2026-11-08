import SquareKit.SmoothOrdinaryQuotient
import SquareKit.SmoothOrdinaryCoverRecovery
import Examples.SmoothTorsors
import Examples.SmoothOrdinaryIsotropy

/-! Checked ordinary-open comparison cases: disconnected labels, an explicit
refinement of the sign cover, and recovery of actual torsor quotient objects. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ContDiff
namespace Examples.SmoothOrdinaryComparison
open SquareKit SquareKit.SmoothAlgebra SquareKit.EuclideanOpen SquareKit.SmoothOpenSite
open SquareKit.SmoothClutching

/-- Independent point meaning of the clutching transition. -/
def signLabel (G : Type) [Group G] (c : G) : LocallyConstant (Points punctured) G where
  toFun x := if x.val 0 < 0 then 1 else c
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro x
    by_cases hx : x.val 0 < 0
    · refine ⟨{y | y.val 0 < 0}, isOpen_lt ((continuous_apply 0).comp continuous_subtype_val) continuous_const,
        hx, ?_⟩
      intro y hy
      change y.val 0 < 0 at hy
      simp only [ite_eq_left hx, ite_eq_left hy]
    · have hpos : 0 < x.val 0 := by
        have hn : x.val 0 ≠ 0 := by
          have h := x.property
          change (1 : ℝ) * x.val 0 ≠ 0 at h
          exact right_ne_zero_of_mul h
        exact lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hn)
      refine ⟨{y | 0 < y.val 0}, isOpen_lt continuous_const ((continuous_apply 0).comp continuous_subtype_val),
        hpos, ?_⟩
      intro y hy
      change 0 < y.val 0 at hy
      simp only [ite_eq_right hx, ite_eq_right (not_lt_of_ge (le_of_lt hy))]

theorem signLabel_on_component (G : Type) [Group G] (c : G) (b : Bool)
    (x : Points (subdomain punctured (signDefining b))) :
    signLabel G c ((show Map _ _ from subInclusion punctured (signDefining b)) x) = if b then c else 1 := by
  have hx := (signDefining_iff b x.val).mp (right_ne_zero_of_mul x.property)
  cases b <;> simp only [signOpen, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at hx ⊢
  · exact ite_eq_left hx
  · exact ite_eq_right (not_lt_of_ge (le_of_lt hx))

/-- The new inverse recovers the independently constructed sheaf gluing. -/
theorem signLabel_inverse (G : Type) [Group G] (c : G) :
    (ordinaryHomLabelEquiv G punctured).symm (signLabel G c) = transition G c := by
  apply cover_jointly_epic punctured signDefining sign_covers (locallyConstantGroupSheaf G)
  intro b
  rw [transition_restrict]
  apply (ordinaryHomLabelEquiv G _).injective
  apply DFunLike.ext
  intro x
  rw [ordinaryHomLabelEquiv_natural, Equiv.apply_symm_apply]
  exact (signLabel_on_component G c b x).trans
    (ordinaryHomLabelEquiv_constant G _ (if b then c else 1) x).symm

/-- The old construction now computes through the new equivalence. -/
theorem transition_label (G : Type) [Group G] (c : G) :
    ordinaryHomLabelEquiv G punctured (transition G c) = signLabel G c := by
  rw [← signLabel_inverse]
  exact (ordinaryHomLabelEquiv G punctured).apply_symm_apply _

/-- Refine each sign component by removing either 1 or -1. These overlapping
principal opens cover each component, and neither test is a constant-only cover. -/
def radiusDefining (b : Bool) : Free 1 := if b then generator 0 - 1 else generator 0 + 1

def refinedSignDefining (i : Bool × Bool) : Free 1 := signDefining i.1 * radiusDefining i.2

theorem radius_covers (U : Domain) (hU : U.dimension = 1) :
    ∀ x : Points U, ∃ b, (radiusDefining b).val (hU ▸ x.val) ≠ 0 := by
  intro x
  by_cases h : (hU ▸ x.val) 0 = 1
  · refine ⟨false, ?_⟩
    change (hU ▸ x.val) 0 + 1 ≠ 0
    rw [h]
    norm_num
  · exact ⟨true, by change (hU ▸ x.val) 0 - 1 ≠ 0; exact sub_ne_zero.mpr h⟩

theorem refinedSign_covers : Covers punctured refinedSignDefining := by
  intro x
  obtain ⟨b, hb⟩ := sign_covers x
  obtain ⟨r, hr⟩ := radius_covers punctured rfl x
  exact ⟨(b, r), mul_ne_zero hb hr⟩

/-- The actual ordinary map from each refined member to its old member. -/
def signRefinement (i : Bool × Bool) :
    subdomain punctured (refinedSignDefining i) ⟶ subdomain punctured (signDefining i.1) where
  toFun x := ⟨x.val, mul_ne_zero (left_ne_zero_of_mul x.property)
    (left_ne_zero_of_mul (right_ne_zero_of_mul x.property))⟩
  smooth j := (OpenFunctions.representative_iff _ (fun x => x j) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) j).contDiffOn

theorem signRefinement_square (i : Bool × Bool) :
    signRefinement i ≫ subInclusion punctured (signDefining i.1) =
      subInclusion punctured (refinedSignDefining i) := OpenFunctions.Map.ext (fun _ => rfl)

/-- Refinement retains the actual constant-section restriction of the old gluing. -/
theorem transition_refined (G : Type) [Group G] (c : G) (i : Bool × Bool) :
    embedding.map (subInclusion punctured (refinedSignDefining i)) ≫ transition G c =
      constantSection _ (if i.1 then c else 1) := by
  rw [← signRefinement_square, embedding.map_comp, Category.assoc, transition_restrict]
  rfl

/-- The refined matching family has the same unique global arrow. -/
theorem refined_gluing_recovers (G : Type) [Group G] (c : G)
    (t : embedding.obj punctured ⟶ locallyConstantGroupSheaf G)
    (ht : ∀ i, embedding.map (subInclusion punctured (refinedSignDefining i)) ≫ t =
      constantSection _ (if i.1 then c else 1)) : t = transition G c := by
  apply cover_jointly_epic punctured refinedSignDefining refinedSign_covers _
  exact fun i => (ht i).trans (transition_refined G c i).symm

/-- The chosen refinement is a map of the actual covering objects. -/
def signCoverRefinement : (∐ fun i => embedding.obj (subdomain punctured (refinedSignDefining i))) ⟶
    (∐ fun b => embedding.obj (subdomain punctured (signDefining b))) :=
  Sigma.desc (fun i => embedding.map (signRefinement i) ≫
    Sigma.ι (fun b => embedding.obj (subdomain punctured (signDefining b))) i.1)

theorem signCoverRefinement_square :
    signCoverRefinement ≫ ordinaryCoverMap punctured signDefining =
      ordinaryCoverMap punctured refinedSignDefining := by
  apply Sigma.hom_ext
  intro i
  simp only [signCoverRefinement, ordinaryCoverMap, Sigma.ι_comp_desc_assoc,
    Sigma.ι_comp_desc, Category.assoc]
  rw [← embedding.map_comp, signRefinement_square]

theorem refinedLabels_compatible (G : Type) [Group G] (c : G) (i j : Bool × Bool) :
    embedding.map (overlapLeft punctured (refinedSignDefining i) (refinedSignDefining j)) ≫
        constantSection _ (if i.1 then c else 1) =
      embedding.map (overlapRight punctured (refinedSignDefining i) (refinedSignDefining j)) ≫
        constantSection _ (if j.1 then c else 1) := by
  rw [← transition_refined G c i, ← transition_refined G c j,
    ← Category.assoc, ← Category.assoc, ← embedding.map_comp, ← embedding.map_comp, overlap_square]

/-- The new matching family is constructed by restriction along the named refinement. -/
def refinedTransition (G : Type) [Group G] (c : G) :
    embedding.obj punctured ⟶ locallyConstantGroupSheaf G :=
  (sheaf_exists_unique punctured refinedSignDefining refinedSign_covers _
    (fun i => constantSection _ (if i.1 then c else 1)) (refinedLabels_compatible G c)).choose

theorem refinedTransition_recovers (G : Type) [Group G] (c : G) :
    refinedTransition G c = transition G c := by
  apply refined_gluing_recovers G c
  exact (sheaf_exists_unique punctured refinedSignDefining refinedSign_covers _
    (fun i => constantSection _ (if i.1 then c else 1)) (refinedLabels_compatible G c)).choose_spec.1

abbrev signFamily := ordinaryCoverFamily punctured signDefining
abbrev refinedSignFamily := ordinaryCoverFamily punctured refinedSignDefining
instance : Presheaf.IsLocallySurjective SquareKit.SmoothOpenSite.topology (SplitSheaf.p signFamily).hom :=
  ordinaryCoverFamily_locallySurjective punctured signDefining sign_covers
instance : Presheaf.IsLocallySurjective SquareKit.SmoothOpenSite.topology (SplitSheaf.p refinedSignFamily).hom :=
  ordinaryCoverFamily_locallySurjective punctured refinedSignDefining refinedSign_covers

/-- The refinement on the actual split cover displays. -/
def signSplitRefinement : SplitSheaf.Ext refinedSignFamily ⟶ SplitSheaf.Ext signFamily :=
  (SplitSheaf.displayIso (ordinaryCoverMap punctured refinedSignDefining)).hom ≫ signCoverRefinement ≫
    (SplitSheaf.displayIso (ordinaryCoverMap punctured signDefining)).inv

theorem signSplitRefinement_square : signSplitRefinement ≫ SplitSheaf.p signFamily =
    SplitSheaf.p refinedSignFamily := by
  change ((SplitSheaf.displayIso (ordinaryCoverMap punctured refinedSignDefining)).hom ≫
    signCoverRefinement ≫ (SplitSheaf.displayIso (ordinaryCoverMap punctured signDefining)).inv) ≫
      SplitSheaf.p (SplitSheaf.ofDisplay (ordinaryCoverMap punctured signDefining)) = _
  rw [← SplitSheaf.displayIso_projection (ordinaryCoverMap punctured signDefining)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [signCoverRefinement_square, SplitSheaf.displayIso_projection]
  rfl

open SheafActionQuotient

/-- This equality includes both object restriction and the actual restricted
arrows of the canonical data, along the chosen split refinement map. -/
theorem signRefinement_restriction {G : Sheaf SquareKit.SmoothOpenSite.topology GrpCat}
    {M : Sheaf SquareKit.SmoothOpenSite.topology Type} (a : Action G M) :
    restriction (a := a) (SplitSheaf.p signFamily) ⋙ restriction signSplitRefinement =
      restriction (SplitSheaf.p refinedSignFamily) := by
  rw [restriction_comp, signSplitRefinement_square]

/-- The named sign refinement compares canonical descent of every quotient object
over the punctured line, using the actual recovery arrows. -/
def signRefinementRecovery {G : Sheaf SquareKit.SmoothOpenSite.topology GrpCat}
    {M : Sheaf SquareKit.SmoothOpenSite.topology Type} {a : Action G M}
    (P : Object a (embedding.obj punctured)) :=
  Descent.recoveryComparison signFamily refinedSignFamily P

theorem signRefinementRecovery_commutes {G : Sheaf SquareKit.SmoothOpenSite.topology GrpCat}
    {M : Sheaf SquareKit.SmoothOpenSite.topology Type} {a : Action G M}
    (P : Object a (embedding.obj punctured)) :
    (signRefinementRecovery P).comp (Descent.canonicalRecovery refinedSignFamily P) =
      Descent.canonicalRecovery signFamily P :=
  Descent.recoveryComparison_commutes signFamily refinedSignFamily P

theorem signRefinement_arrows {G : Sheaf SquareKit.SmoothOpenSite.topology GrpCat}
    {M : Sheaf SquareKit.SmoothOpenSite.topology Type} {a : Action G M}
    (P Q : Object a (embedding.obj punctured))
    (f : Descent.Map (Descent.canonicalDatum signFamily P) (Descent.canonicalDatum signFamily Q)) :
    Descent.canonicalArrowEquiv refinedSignFamily P Q
      (Descent.recoveryArrowComparison signFamily refinedSignFamily P Q f) =
      Descent.canonicalArrowEquiv signFamily P Q f :=
  Descent.recoveryArrowComparison_commutes signFamily refinedSignFamily P Q f

theorem signRefinement_arrows_square {G : Sheaf SquareKit.SmoothOpenSite.topology GrpCat}
    {M : Sheaf SquareKit.SmoothOpenSite.topology Type} {a : Action G M}
    (P Q : Object a (embedding.obj punctured))
    (f : Descent.Map (Descent.canonicalDatum signFamily P) (Descent.canonicalDatum signFamily Q)) :
    (signRefinementRecovery P).comp
      (Descent.recoveryArrowComparison signFamily refinedSignFamily P Q f).arrow =
      f.arrow.comp (signRefinementRecovery Q) :=
  Descent.recoveryComparison_natural signFamily refinedSignFamily P Q f

open Orbifolds.QuarterTurn SmoothQuarterTurnQuotient

def zeroValue : base ⟶ scalar :=
  tuple (fun i : Fin 0 => Fin.elim0 i) ≫ operation (SmoothAlgebra.constant 0 0)

/-- The retained quotient object has the actual nontrivial clutching torsor. -/
def nontrivialObject : Object ineffectiveRepresentation.action base :=
  invariantObject Examples.SmoothTorsors.nontrivialTorsor zeroValue
    (fun x g => ineffectiveRepresentation.act_of_trivial (fun _ => rfl) x.obj g _)

theorem nontrivialObject_no_section : ¬ Nonempty (SplitSheaf.Tm nontrivialObject.torsor.family) :=
  Examples.SmoothTorsors.nontrivialTorsor_no_section

abbrev nontrivialRecovered := (Descent.canonicalDatum nontrivialObject.torsor.family nontrivialObject).object

/-- Recovering the nontrivial object does not turn it into a global chart. -/
theorem nontrivialRecovered_not_chart (m : base ⟶ scalar) :
    ¬ Nonempty (Arrow (chart ineffectiveRepresentation.action m) nontrivialRecovered) := by
  rintro ⟨f⟩
  exact not_chart_of_no_section nontrivialObject nontrivialObject_no_section m
    ⟨f.comp (Descent.canonicalRecovery nontrivialObject.torsor.family nontrivialObject)⟩

/-- The new inverse is the existing nontrivial torsor's transition; the recovered
object still has no global chart. Both conclusions consume the constructed APIs. -/
theorem nontrivial_comparison_control (m : base ⟶ scalar) :
    (ordinaryHomLabelEquiv C4 punctured).symm (signLabel C4 quarterTurn) = transition C4 quarterTurn ∧
      ¬ Nonempty (Arrow (chart ineffectiveRepresentation.action m) nontrivialRecovered) :=
  ⟨signLabel_inverse C4 quarterTurn, nontrivialRecovered_not_chart m⟩

def negativePoint : Points punctured := ⟨fun _ => -1, by change (1 : ℝ) * (-1) ≠ 0; norm_num⟩
def positivePoint : Points punctured := ⟨fun _ => 1, by change (1 : ℝ) * 1 ≠ 0; norm_num⟩

open SmoothOrdinaryQuotient SmoothQuarterTurnArcs

/-- A disconnected ordinary chart admits an arrow with different labels on its two components. -/
def varyingOriginArrow :
    Arrow (chart diskRepresentation.action (embedding.map (constantMap punctured diskDomain coordinateOrigin)))
      (chart diskRepresentation.action (embedding.map (constantMap punctured diskDomain coordinateOrigin))) :=
  (diskChartArrowEquiv punctured (constantMap punctured diskDomain coordinateOrigin)
    (constantMap punctured diskDomain coordinateOrigin)).symm
      ⟨signLabel C4 quarterTurn, fun _x => coordinateOrigin_fixed _⟩

theorem varyingOriginArrow_labels :
    ordinaryArrowLabel varyingOriginArrow negativePoint = 1 ∧
      ordinaryArrowLabel varyingOriginArrow positivePoint = quarterTurn := by
  have h := congrArg Subtype.val ((diskChartArrowEquiv punctured
    (constantMap punctured diskDomain coordinateOrigin) (constantMap punctured diskDomain coordinateOrigin)).apply_symm_apply
      ⟨signLabel C4 quarterTurn, fun _ => coordinateOrigin_fixed _⟩)
  change ordinaryArrowLabel varyingOriginArrow = signLabel C4 quarterTurn at h
  rw [h]
  constructor <;> norm_num [signLabel, negativePoint, positivePoint]

theorem varyingOriginArrow_not_constant (g : C4) :
    ordinaryArrowLabel varyingOriginArrow ≠ LocallyConstant.const _ g := by
  intro h
  have hn := congrArg (fun k => k negativePoint) h
  have hp := congrArg (fun k => k positivePoint) h
  exact quarterTurn_ne_one ((varyingOriginArrow_labels.2.symm.trans hp).trans
    (varyingOriginArrow_labels.1.symm.trans hn).symm)

abbrev emptyDomain : Domain := ⟨0, 0⟩
instance : IsEmpty (Points emptyDomain) := ⟨fun x => x.property rfl⟩

/-- Distinct constant labels coincide over the empty domain, as the sheaf law requires. -/
theorem empty_inverse_unique :
    (ordinaryLocallyConstantEquiv C4 emptyDomain).symm (LocallyConstant.const _ quarterTurn) =
      (ordinaryLocallyConstantEquiv C4 emptyDomain).symm (LocallyConstant.const _ 1) :=
  ordinary_empty_section_unique C4 emptyDomain _ _

/-- Constant fibers have elementary supplied descriptions, without openDefining. -/
def constantData (G : Type) [Group G] [DecidableEq G] (U : Domain) (g : G) :
    PrincipalLabelData G U (LocallyConstant.const _ g) where
  defining k := if g = k then 1 else 0
  fiber_iff k x := by
    by_cases h : g = k <;> simp [h]

theorem constant_supplied_label (G : Type) [Group G] [DecidableEq G]
    (U : Domain) (g : G) (x : Points U) :
    ordinaryLabel G U (constantData G U g).gluedSection x = g :=
  (constantData G U g).label_section x

/-- Squaring changes the supplied smooth functions while preserving their loci. -/
def squaredData {G : Type} [Group G] {U : Domain} {l : LocallyConstant (Points U) G}
    (d : PrincipalLabelData G U l) : PrincipalLabelData G U l where
  defining k := d.defining k * d.defining k
  fiber_iff k x := by
    change (d.defining k).val x.val * (d.defining k).val x.val ≠ 0 ↔ _
    rw [mul_ne_zero_iff, and_self]
    exact d.fiber_iff k x

/-- The supplied-data path preserves the disconnected label, including both values. -/
theorem supplied_sign_values :
    let d := squaredData (selectedPrincipalLabelData C4 punctured (signLabel C4 quarterTurn))
    ordinaryLabel C4 punctured d.gluedSection negativePoint = 1 ∧
      ordinaryLabel C4 punctured d.gluedSection positivePoint = quarterTurn := by
  dsimp only
  rw [PrincipalLabelData.label_section, PrincipalLabelData.label_section]
  constructor <;> norm_num [signLabel, negativePoint, positivePoint]

theorem supplied_sign_not_constant (g : C4) :
    let d := squaredData (selectedPrincipalLabelData C4 punctured (signLabel C4 quarterTurn))
    ordinaryLabel C4 punctured d.gluedSection ≠ fun _ => g := by
  intro d h
  have hn := congrFun h negativePoint
  have hp := congrFun h positivePoint
  exact quarterTurn_ne_one ((supplied_sign_values.2.symm.trans hp).trans
    (supplied_sign_values.1.symm.trans hn).symm)

theorem squared_data_independent {G : Type} [Group G] {U : Domain}
    {l : LocallyConstant (Points U) G} (d : PrincipalLabelData G U l) :
    (squaredData d).gluedSection = d.gluedSection :=
  (squaredData d).independent d

/-- On the empty domain any supplied functions describe every (empty) fiber. -/
def emptyData (q : C4 → Free emptyDomain.dimension)
    (l : LocallyConstant (Points emptyDomain) C4) : PrincipalLabelData C4 emptyDomain l :=
  ⟨q, fun _ x => isEmptyElim x⟩

theorem empty_supplied_independent :
    (emptyData (fun _ => 0) (LocallyConstant.const _ quarterTurn)).gluedSection =
      (emptyData (fun _ => 1) (LocallyConstant.const _ 1)).gluedSection :=
  ordinary_empty_section_unique C4 emptyDomain _ _

/-- Zero functions cannot describe the inhabited fiber at the negative point. -/
theorem zero_not_sign_data :
    ¬ ∀ k (x : Points punctured), (0 : Free punctured.dimension).val x.val ≠ 0 ↔
      signLabel C4 quarterTurn x = k := by
  intro h
  have bad := (h (signLabel C4 quarterTurn negativePoint) negativePoint).mpr rfl
  exact bad rfl

end Examples.SmoothOrdinaryComparison
