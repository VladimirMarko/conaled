import SquareKit.SheafActionRefinement
import SquareKit.SmoothPrincipalAtlas
import SquareKit.SmoothDiskPresentation

/-! A genuine open refinement of the quarter-turn disk action presentation.
The origin has distinct atlas lifts and every lift retains all four arrows. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.ActionMorita
open CategoryTheory Opposite
open SquareKit SquareKit.SmoothAlgebra SquareKit.SmoothOpenSite
open SquareKit.EuclideanOpen SquareKit.SmoothQuarterTurnArcs
open SquareKit.SmoothQuarterTurnQuotient Orbifolds.QuarterTurn

/-- Delete two different coordinate levels, leaving a cover with a nonempty overlap. -/
def defining (c : ℝ) : Bool → freeAlgebra 2
  | false => generator 0 - algebraMap ℝ (freeAlgebra 2) c
  | true => generator 0 + algebraMap ℝ (freeAlgebra 2) c

theorem covers (c : ℝ) (hc : c ≠ 0) : Covers diskDomain (defining c) := by
  intro x
  by_cases h : x.val (0 : Fin 2) = c
  · refine ⟨true, ?_⟩
    change x.val (0 : Fin 2) + c ≠ 0
    rw [h]
    intro he
    apply hc
    linarith
  · exact ⟨false, sub_ne_zero.mpr h⟩

def atlas := PrincipalAtlas.atlas diskDomain (defining (1/2)) (covers _ (by norm_num))
def otherAtlas := PrincipalAtlas.atlas diskDomain (defining (1/3)) (covers _ (by norm_num))
def commonAtlas := PrincipalAtlas.atlas diskDomain
  (PrincipalAtlas.commonFunctions diskDomain (defining (1/2)) (defining (1/3)))
  (PrincipalAtlas.common_covers _ _ _ (covers _ (by norm_num)) (covers _ (by norm_num)))
def commonLeft := PrincipalAtlas.commonLeft diskDomain (defining (1/2)) (defining (1/3))
  (covers _ (by norm_num)) (covers _ (by norm_num))
def commonRight := PrincipalAtlas.commonRight diskDomain (defining (1/2)) (defining (1/3))
  (covers _ (by norm_num)) (covers _ (by norm_num))

abbrev action := diskRepresentation.action
abbrev refined (X : Sheaf topology Type) := SheafActionRefinement.Object action atlas.cover X

/-- This is an actual locally generating atlas presentation of the full quotient. -/
theorem generates : StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := topology))
    (SheafActionRefinement.quotientTransformation action atlas.cover) :=
  SheafActionRefinement.quotientLocallyGenerating action atlas.cover

/-- The comparison preserves and recovers every compatible arrow. -/
def fullyFaithful (X : Sheaf topology Type) :
    (SheafActionRefinement.quotient (X := X) action atlas.cover).FullyFaithful :=
  SheafActionRefinement.quotientFullyFaithful action atlas.cover

theorem origin_coordinates : coordinateOrigin.val = 0 := by
  change complexCoordinates.symm (origin : ℂ) = 0
  exact map_zero _

def originInChart (i : Bool) : Points (atlas.domain i) :=
  ⟨coordinateOrigin.val, mul_ne_zero coordinateOrigin.property (by
    cases i
    · change coordinateOrigin.val (0 : Fin 2) - (1/2 : ℝ) ≠ 0
      rw [origin_coordinates]
      norm_num
    · change coordinateOrigin.val (0 : Fin 2) + (1/2 : ℝ) ≠ 0
      rw [origin_coordinates]
      norm_num)⟩

def originLift (i : Bool) : realBase ⟶ atlas.total :=
  topology.yoneda.map (ordinaryPoint (atlas.domain i) (originInChart i)) ≫ atlas.inclusion i

theorem originLift_projection (i : Bool) : originLift i ≫ atlas.cover = point coordinateOrigin := by
  rw [originLift, Category.assoc, SheafCoproductLocal.inclusion_desc]
  apply topology.yonedaEquiv.injective
  change (embedding.map (subInclusion diskDomain (defining (1/2) i))).hom.app _
    ((realSectionEquiv (atlas.domain i)).symm (originInChart i)) =
      (realSectionEquiv diskDomain).symm coordinateOrigin
  apply (realSectionEquiv diskDomain).injective
  rw [Equiv.apply_symm_apply]
  exact (realSectionEquiv_naturality (subInclusion diskDomain (defining (1/2) i)) _).trans
    (congrArg (fun z => (show EuclideanOpen.Map _ _ from
      subInclusion diskDomain (defining (1/2) i)).toFun z)
        ((realSectionEquiv (atlas.domain i)).apply_symm_apply (originInChart i)))

def originObject (i : Bool) : refined realBase := ⟨originLift i⟩

def tag : atlas.total ⟶ locallyConstantGroupSheaf C4 :=
  SheafCoproductLocal.desc atlas.family
    (fun i => constantSection _ (if i then quarterTurn else 1))

theorem originLift_tag (i : Bool) : originLift i ≫ tag =
    constantSection realBase (if i then quarterTurn else 1) := by
  rw [originLift, tag, Category.assoc, SheafCoproductLocal.inclusion_desc]
  rfl

/-- The two lifts are distinct objects even though their images are the same origin. -/
theorem originObjects_distinct : originObject false ≠ originObject true := by
  intro he
  have h := congrArg (fun m : refined realBase => m.map ≫ tag) he
  change originLift false ≫ tag = originLift true ≫ tag at h
  rw [originLift_tag, originLift_tag] at h
  have hh := congrArg realLabelEquiv h
  exact quarterTurn_ne_one (by simpa only [Bool.false_eq_true, ↓reduceIte, realLabelEquiv_constant] using hh.symm)

/-- Every pair of atlas lifts has the original complete origin hom group. -/
def originArrowEquiv (i j : Bool) : (originObject i ⟶ originObject j) ≃ C4 :=
  (SheafActionRefinement.arrowEquiv action atlas.cover _ _).trans
    ((Equiv.subtypeEquivRight (fun g => by
      rw [show (originObject j).map ≫ atlas.cover = point coordinateOrigin from originLift_projection j,
        show (originObject i).map ≫ atlas.cover = point coordinateOrigin from originLift_projection i])).trans
      ((SheafActionQuotient.chartArrowEquiv (a := action) (point coordinateOrigin)
        (point coordinateOrigin)).symm.trans SmoothQuarterTurnQuotient.originArrowEquiv))

theorem origin_arrow_count (i j : Bool) : Nat.card (originObject i ⟶ originObject j) = 4 :=
  (Nat.card_congr (originArrowEquiv i j)).trans card_C4

/-- The identity action label connects two different atlas objects. -/
def chartChange : originObject false ⟶ originObject true := (originArrowEquiv false true).symm 1

/-- Passing to endpoint equality alone would identify two genuinely different arrows. -/
theorem distinct_origin_labels :
    (originArrowEquiv false true).symm quarterTurn ≠ chartChange := by
  intro h
  exact quarterTurn_ne_one ((originArrowEquiv false true).symm.injective h)

/-- The quotient comparison also distinguishes those two overlap arrows. -/
theorem quotient_retains_origin_labels :
    (SheafActionRefinement.quotient action atlas.cover).map
        ((originArrowEquiv false true).symm quarterTurn) ≠
      (SheafActionRefinement.quotient action atlas.cover).map chartChange := by
  intro h
  exact distinct_origin_labels ((fullyFaithful realBase).map_injective h)

/-- Both maps of the common atlas induce actual label-preserving comparison functors. -/
def commonToFirst (X : Sheaf topology Type) :
    SheafActionRefinement.Object action commonAtlas.cover X ⥤ refined X :=
  SheafActionRefinement.map action atlas.cover commonAtlas.cover commonLeft.total
    (by simpa only [Category.comp_id, atlas, commonAtlas, diskSheaf] using commonLeft.total_cover)

def commonToSecond (X : Sheaf topology Type) :
    SheafActionRefinement.Object action commonAtlas.cover X ⥤
      SheafActionRefinement.Object action otherAtlas.cover X :=
  SheafActionRefinement.map action otherAtlas.cover commonAtlas.cover commonRight.total
    (by simpa only [Category.comp_id, otherAtlas, commonAtlas, diskSheaf] using commonRight.total_cover)

theorem common_target (X : Sheaf topology Type)
    (m : SheafActionRefinement.Object action commonAtlas.cover X) :
    ((SheafActionRefinement.toPresentation action atlas.cover).obj ((commonToFirst X).obj m)).map =
      ((SheafActionRefinement.toPresentation action otherAtlas.cover).obj ((commonToSecond X).obj m)).map := by
  exact (SheafActionRefinement.map_chart _ _ _ _ _ m).trans
    (SheafActionRefinement.map_chart _ _ _ _ _ m).symm

/-- Both common-refinement routes agree on the complete quotient functor. -/
theorem common_quotient (X : Sheaf topology Type) :
    commonToFirst X ⋙ SheafActionRefinement.quotient action atlas.cover =
      commonToSecond X ⋙ SheafActionRefinement.quotient action otherAtlas.cover :=
  (SheafActionRefinement.map_quotient _ _ _ _ _).trans
    (SheafActionRefinement.map_quotient _ _ _ _ _).symm

/-- Every orbit-valued discrete observation loses the distinct origin labels. -/
theorem orbit_observation_not_faithful
    (F : refined realBase ⥤ Discrete (Quotient (MulAction.orbitRel C4 Disk))) :
    ¬ F.Faithful := by
  intro hF
  exact distinct_origin_labels (F.map_injective (Subsingleton.elim _ _))

/-- Ineffective labels also survive in the independent action presentation. -/
def ineffectiveObject (m : realBase ⟶ scalar) :
    SheafActionPresentation.Object ineffectiveRepresentation.action realBase := ⟨m⟩

def ineffectiveArrow (m : realBase ⟶ scalar) (g : C4) :
    ineffectiveObject m ⟶ ineffectiveObject m :=
  ⟨constantSection realBase g, ineffective_constant_onMap g m⟩

theorem ineffective_arrows_distinct (m : realBase ⟶ scalar) :
    ineffectiveArrow m quarterTurn ≠ ineffectiveArrow m 1 := by
  intro h
  have hh := congrArg (fun k : ineffectiveObject m ⟶ ineffectiveObject m => realLabelEquiv k.label) h
  exact quarterTurn_ne_one (by simpa only [ineffectiveArrow, realLabelEquiv_constant] using hh)

theorem ineffective_quotient_retains (m : realBase ⟶ scalar) :
    (SheafActionPresentation.quotient ineffectiveRepresentation.action).map (ineffectiveArrow m quarterTurn) ≠
      (SheafActionPresentation.quotient ineffectiveRepresentation.action).map (ineffectiveArrow m 1) := by
  intro h
  exact ineffective_arrows_distinct m ((SheafActionPresentation.quotientFullyFaithful _).map_injective h)

/-- Each deleted coordinate level contains an actual point of the open disk. -/
def levelPoint (c : ℝ) (hc : |c| < 1) : Points diskDomain :=
  diskPoints.symm ⟨(c : ℂ), by
    change dist (c : ℂ) 0 < 1
    simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hc⟩

theorem levelPoint_coordinate (c : ℝ) (hc : |c| < 1) :
    (levelPoint c hc).val (0 : Fin 2) = c := rfl

/-- Neither open in the chosen atlas is the original whole disk. -/
theorem opens_proper (i : Bool) : ∃ x : Points diskDomain, ¬ x.val ∈ Points (atlas.domain i) := by
  cases i
  · refine ⟨levelPoint (1/2) (by norm_num), ?_⟩
    intro hx
    have hn : (defining (1/2) false).val (levelPoint (1/2) (by norm_num)).val ≠ 0 :=
      right_ne_zero_of_mul hx
    change (levelPoint (1/2) (by norm_num)).val (0 : Fin 2) - 1/2 ≠ 0 at hn
    rw [levelPoint_coordinate] at hn
    exact hn (sub_self _)
  · refine ⟨levelPoint (-1/2) (by norm_num), ?_⟩
    intro hx
    have hn : (defining (1/2) true).val (levelPoint (-1/2) (by norm_num)).val ≠ 0 :=
      right_ne_zero_of_mul hx
    change (levelPoint (-1/2) (by norm_num)).val (0 : Fin 2) + 1/2 ≠ 0 at hn
    rw [levelPoint_coordinate] at hn
    exact hn (by norm_num)

/-- The atlas cover is not an isomorphism or a renaming of its target. -/
theorem cover_not_mono : ¬ Mono atlas.cover := by
  intro h
  have he : originLift false = originLift true :=
    (cancel_mono atlas.cover).mp ((originLift_projection false).trans (originLift_projection true).symm)
  exact originObjects_distinct (congrArg (fun f => SheafActionRefinement.Object.mk (a := action)
    (p := atlas.cover) f) he)

/-- The old smooth-family interpretation is recovered for every pair of lifted
ordinary maps, using the complete new quotient comparison. -/
def smoothArrowEquiv (D : Domain) (m n : D ⟶ diskDomain)
    (r s : refined (embedding.obj D))
    (hr : r.map ≫ atlas.cover = embedding.map m)
    (hs : s.map ≫ atlas.cover = embedding.map n) :
    (r ⟶ s) ≃ SmoothDiskPresentation.Family D m n :=
  (fullyFaithful (embedding.obj D)).homEquiv.trans (by
    change (SheafActionQuotient.chart action (r.map ≫ atlas.cover) ⟶
      SheafActionQuotient.chart action (s.map ≫ atlas.cover)) ≃ _
    rw [hr, hs]
    exact SmoothDiskPresentation.chartEquiv D m n)

/-- Restriction of the complete atlas comparison is the original quotient restriction. -/
example {X Y : Sheaf topology Type} (f : Y ⟶ X) :
    SheafActionRefinement.restriction action atlas.cover f ⋙
      SheafActionRefinement.quotient action atlas.cover =
        SheafActionRefinement.quotient action atlas.cover ⋙ SheafActionQuotient.restriction f := rfl

open scoped CategoryTheory.Pseudofunctor.StrongTrans

variable (T : Pseudofunctor
  (LocallyDiscrete (Sheaf topology Type)ᵒᵖ) Cat.{0, 1})
  [T.IsStack (SheafCover.topology (J := topology))]

/-- The open atlas gives the same maps and modifications into any stack. -/
def atlasUniversal : (SheafActionQuotient.Stack.pseudofunctor action ⟶ T) ≌
    (SheafActionRefinement.pseudofunctor action atlas.cover ⟶ T) :=
  SheafActionRefinement.quotientUniversalEquivalence action atlas.cover T

/-- Refining the original action charts preserves their entire mapping category. -/
def chartRefinementUniversal : (SheafActionPresentation.pseudofunctor action ⟶ T) ≌
    (SheafActionRefinement.pseudofunctor action atlas.cover ⟶ T) :=
  SheafActionRefinement.refinementUniversalEquivalence action atlas.cover T

/-- Independently chosen open atlases have equivalent mapping categories. -/
def atlasIndependence : (SheafActionRefinement.pseudofunctor action atlas.cover ⟶ T) ≌
    (SheafActionRefinement.pseudofunctor action otherAtlas.cover ⟶ T) :=
  (atlasUniversal T).symm.trans
    (SheafActionRefinement.quotientUniversalEquivalence action otherAtlas.cover T)

/-- The comparison extends modifications, including those on overlap arrows. -/
def atlasModificationEquiv (Φ Ψ : SheafActionQuotient.Stack.pseudofunctor action ⟶ T) :
    (Φ ⟶ Ψ) ≃
      (SheafActionRefinement.quotientTransformation action atlas.cover ≫ Φ ⟶
        SheafActionRefinement.quotientTransformation action atlas.cover ≫ Ψ) :=
  (atlasUniversal T).fullyFaithfulFunctor.homEquiv

example : (atlasUniversal T).functor = StackLocalGeneration.restriction
    (SheafActionRefinement.quotientTransformation action atlas.cover) T := rfl

end Examples.ActionMorita
