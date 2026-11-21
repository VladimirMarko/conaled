import SquareKit.SubcanonicalTorsor
import Examples.SheafFamilyDescent
import SquareKit.SmoothClutchingRefinement

/-! Original-site restriction and slice comparisons of actual clutching charts.
The doubled-origin base remains a sheaf context, not an asserted representable. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace Examples.SubcanonicalTorsor
open CategoryTheory Limits Opposite SquareKit
open SmoothTorsors Orbifolds.QuarterTurn
open SmoothClutching EuclideanOpen SmoothOpenSite

abbrev J := SmoothOpenSite.topology
abbrev lineObject := toSite.obj line
abbrev overlapObject := toSite.obj punctured
abbrev sliceLine := SheafSliceTorsor.equivalence (G := group) J lineObject
abbrev sliceOverlap := SheafSliceTorsor.equivalence (G := group) J overlapObject

/-- These are restrictions of the genuinely nontrivial global torsor. -/
abbrev chartTorsor (b : Bool) := SheafTorsor.reindex nontrivialTorsor (Represented.chart b)
abbrev chartSlice (b : Bool) := sliceLine.functor.obj (chartTorsor b)

def chartComparison (b : Bool) :
    sliceLine.functor.obj (SheafTorsor.trivial group lineSheaf) ⟶ chartSlice b :=
  sliceLine.functor.map (Represented.localTrivialization C4 quarterTurn b)

/-- The slice comparison preserves the nonconstant clutching arrow, not only
its orbit or the cardinality of the fibers. -/
def clutchingArrow := SheafTorsor.regularArrow (transition C4 quarterTurn)
def constantArrow := SheafTorsor.regularArrow (SmoothOpenSite.constantSection puncturedSheaf (1 : C4))

theorem slice_clutching_distinct :
    sliceOverlap.functor.map clutchingArrow ≠ sliceOverlap.functor.map constantArrow := by
  intro h
  exact transition_not_constant C4 quarterTurn quarterTurn_ne_one 1
    (SheafTorsor.regularArrow_injective (sliceOverlap.functor.map_injective h))

theorem constantArrow_eq_identity : constantArrow = 𝟙 (SheafTorsor.trivial group puncturedSheaf) := by
  apply SheafTorsor.Arrow.ext
  ext x g
  change group.obj.obj x.obj at g
  change (g : group.obj.obj x.obj) * ((constantLabel C4).app x.obj).hom 1 = g
  rw [map_one, mul_one]

theorem slice_clutching_not_identity : sliceOverlap.functor.map clutchingArrow ≠
    𝟙 (sliceOverlap.functor.obj (SheafTorsor.trivial group puncturedSheaf)) := by
  intro h
  apply slice_clutching_distinct
  rw [constantArrow_eq_identity]
  exact h.trans (sliceOverlap.functor.map_id _).symm

/-- At the overlap slice object, the compared chart maps satisfy the original
nonidentity gluing equation. -/
theorem slice_chart_gluing (g : group.obj.obj (op overlapObject)) :
    ((chartComparison false).iso.hom.hom.app
      (op (Over.mk (toSite.map (subInclusion line (SmoothAlgebra.generator 0))))) g).val =
    ((chartComparison true).iso.hom.hom.app
      (op (Over.mk (toSite.map (subInclusion line (SmoothAlgebra.generator 0)))))
      (g * (show group.obj.obj (op overlapObject) from
        (transition C4 quarterTurn).hom.app (op overlapObject) (𝟙 overlapObject)))).val := by
  let x := lineSheaf.obj.elementsMk (op overlapObject)
    (toSite.map (subInclusion line (SmoothAlgebra.generator 0)))
  change ((Represented.localTrivialization C4 quarterTurn false).iso.hom.app x g).val =
    ((Represented.localTrivialization C4 quarterTurn true).iso.hom.app x _).val
  rw [Represented.localTrivialization_left_apply, Represented.localTrivialization_right_apply]
  exact Represented.chart_gluing C4 quarterTurn (op overlapObject) (𝟙 overlapObject) g

/-- Global family recovery is connected to the public slice comparison on each chart. -/
def gluedChartRecovery (b : Bool) :
    sliceLine.functor.obj (SheafTorsor.reindex SheafFamilyDescent.gluedTorsor (Represented.chart b)) ≅
      chartSlice b :=
  sliceLine.functor.mapIso
    (SheafTorsor.Arrow.toIso (SheafFamilyDescent.torsorRecovery.hom.reindex (Represented.chart b)))

example : ¬ Nonempty (SheafTorsor.Arrow (SheafTorsor.trivial group base)
    SheafFamilyDescent.gluedTorsor) := SheafFamilyDescent.glued_not_trivializable

abbrev genuineSlice := SheafSliceQuotient.equivalence ActionQuotientStack.targetAction lineObject

def gluedQuotientChartRecovery (b : Bool) :
    genuineSlice.functor.obj (SheafActionQuotient.reindex SheafFamilyDescent.gluedQuotient
      (Represented.chart b)) ≅
    genuineSlice.functor.obj (SheafActionQuotient.reindex ActionQuotientStack.genuine
      (Represented.chart b)) :=
  genuineSlice.functor.mapIso
    ((SheafActionQuotient.restriction (Represented.chart b)).mapIso SheafFamilyDescent.quotientRecovery)

/-- The actual target sheaf map survives global recovery followed by comparison. -/
example (b : Bool) :
    (gluedQuotientChartRecovery b).hom.torsorArrow.iso.hom ≫
      (genuineSlice.functor.obj (SheafActionQuotient.reindex ActionQuotientStack.genuine
        (Represented.chart b))).value =
      (genuineSlice.functor.obj (SheafActionQuotient.reindex SheafFamilyDescent.gluedQuotient
        (Represented.chart b))).value := (gluedQuotientChartRecovery b).hom.preserves

abbrev pointObject := op (SmoothPresentationSite.free 0)
abbrev stabilizerSlice := SheafSliceQuotient.equivalence ActionQuotientStack.ineffective pointObject

theorem slice_stabilizers_distinct :
    stabilizerSlice.functor.map (ActionQuotientStack.stabilizer quarterTurn) ≠
      stabilizerSlice.functor.map (ActionQuotientStack.stabilizer 1) := by
  intro h
  exact ActionQuotientStack.stabilizers_distinct (stabilizerSlice.functor.map_injective h)

abbrev scale (r : ℝ) : lineObject ⟶ lineObject := toSite.map (lineScale r)

theorem scale_not_identity (r : ℝ) (hr : r ≠ 1) : scale r ≠ 𝟙 lineObject := by
  intro h
  have he : lineScale r = 𝟙 line := toSiteFullyFaithful.map_injective (by
    rw [toSite.map_id]; exact h)
  have hp := congrArg (fun f : line ⟶ line =>
    ((show EuclideanOpen.Map line line from f) (realLinePoint 1)).val 0) he
  change r * 1 = 1 at hp
  exact hr (by simpa only [mul_one] using hp)

example : scale 2 ≠ 𝟙 lineObject := scale_not_identity 2 (by norm_num)
example : scale 3 ≠ 𝟙 lineObject := scale_not_identity 3 (by norm_num)

/-- Both nonidentity original-site substitutions act on the independent slice sheaf. -/
example : SheafSliceTorsor.restriction (G := group) J (scale 3 ≫ scale 2) ≅
    SheafSliceTorsor.restriction J (scale 2) ⋙ SheafSliceTorsor.restriction J (scale 3) :=
  SheafSliceTorsor.restrictionComp J (scale 2) (scale 3)

example : SheafSliceQuotient.restriction ActionQuotientStack.targetAction (scale 3 ≫ scale 2) ≅
    SheafSliceQuotient.restriction ActionQuotientStack.targetAction (scale 2) ⋙
      SheafSliceQuotient.restriction ActionQuotientStack.targetAction (scale 3) :=
  SheafSliceQuotient.restrictionComp _ (scale 2) (scale 3)

/-- Every represented map is retained under slice round-trip recovery. -/
example {P Q : SheafTorsor.Torsor group lineSheaf} (h : P ⟶ Q) :
    sliceLine.inverse.map (sliceLine.functor.map h) ≫ (sliceLine.unitIso.app Q).inv =
      (sliceLine.unitIso.app P).inv ≫ h := sliceLine.unitIso.inv.naturality h

example {P Q : SheafActionQuotient.Object ActionQuotientStack.targetAction lineSheaf} (h : P ⟶ Q) :
    genuineSlice.inverse.map (genuineSlice.functor.map h) ≫ (genuineSlice.unitIso.app Q).inv =
      (genuineSlice.unitIso.app P).inv ≫ h := genuineSlice.unitIso.inv.naturality h

/-- An original-site two-open cover of the represented real line. -/
abbrev punctureMap (b : Bool) := subInclusion line (Refined.punctures 1 b)
abbrev originalCover (b : Bool) := toSite.map (punctureMap b)

theorem original_covering : Sieve.ofArrows
    (fun b => toSite.obj (subdomain line (Refined.punctures 1 b))) originalCover ∈ J lineObject :=
  covering line (Refined.punctures 1) (Refined.punctures_cover 1 (by norm_num))

theorem puncture_no_retraction (b : Bool)
    (k : line ⟶ subdomain line (Refined.punctures 1 b)) : k ≫ punctureMap b ≠ 𝟙 line := by
  intro h
  let x := realLinePoint (if b then -1 else 1)
  have hv := congrArg (fun f : line ⟶ line => ((show EuclideanOpen.Map _ _ from f) x).val 0) h
  have hp := ((show EuclideanOpen.Map _ _ from k) x).property
  cases b
  · change (1 : ℝ) * (((show EuclideanOpen.Map _ _ from k) x).val 0 - 1) ≠ 0 at hp
    change ((show EuclideanOpen.Map _ _ from k) x).val 0 = 1 at hv
    rw [hv] at hp
    norm_num at hp
  · change (1 : ℝ) * (((show EuclideanOpen.Map _ _ from k) x).val 0 - (-1)) ≠ 0 at hp
    change ((show EuclideanOpen.Map _ _ from k) x).val 0 = -1 at hv
    rw [hv] at hp
    norm_num at hp

theorem original_cover_proper : Sieve.ofArrows
    (fun b => toSite.obj (subdomain line (Refined.punctures 1 b))) originalCover ≠ ⊤ := by
  intro h
  have hi : Sieve.ofArrows _ originalCover (𝟙 lineObject) := by rw [h]; trivial
  obtain ⟨b,k,hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hi
  apply puncture_no_retraction b (toSiteFullyFaithful.preimage k)
  apply toSiteFullyFaithful.map_injective
  rw [toSite.map_comp, toSiteFullyFaithful.map_preimage, toSite.map_id]
  exact hk.symm

/-- No member of this original two-open cover is locally surjective by itself. -/
theorem original_member_not_surjective (b : Bool) :
    ¬ Presheaf.IsLocallySurjective J (J.yoneda.map (originalCover b)).hom := by
  intro h
  have hm : Mono (embedding.map (punctureMap b)) := by
    apply (sheafToPresheaf J Type).mono_of_mono_map
    have : ∀ A, Mono (((sheafToPresheaf J Type).map (embedding.map (punctureMap b))).app A) := fun A => by
      apply (CategoryTheory.mono_iff_injective _).mpr
      intro a c hc
      apply Quiver.Hom.unop_inj
      apply SmoothAlgebra.Localization.sub_unique line.defining (Refined.punctures 1 b)
      rw [← nested_pullback]
      exact congrArg Quiver.Hom.unop hc
    exact NatTrans.mono_of_mono_app _
  have : Presheaf.IsLocallySurjective J (embedding.map (punctureMap b)).hom := h
  have he : Epi (embedding.map (punctureMap b)) := Sheaf.epi_of_isLocallySurjective _
  have := isIso_of_mono_of_epi (embedding.map (punctureMap b))
  apply puncture_no_retraction b (fullyFaithful.preimage (inv (embedding.map (punctureMap b))))
  apply fullyFaithful.map_injective
  rw [embedding.map_comp, fullyFaithful.map_preimage, embedding.map_id]
  exact IsIso.inv_hom_id _

/-- The original covering sieve and its actual sheaf-valued Yoneda family agree. -/
example : SheafFamilyCover.JointlyLocallySurjective (fun b => J.yoneda.map (originalCover b)) :=
  SubcanonicalSheafStack.yoneda_jointlyLocallySurjective originalCover original_covering

example : (SubcanonicalSheafStack.torsorPseudofunctor group).IsStack J := inferInstance
example : (SubcanonicalSheafStack.quotientPseudofunctor ActionQuotientStack.targetAction).IsStack J :=
  inferInstance

/-- Descent for the proper original cover starts from the independent slice category. -/
def originalTorsorDescent : SheafSliceTorsor.Torsor J lineObject group ≌
    (SubcanonicalSheafStack.torsorPseudofunctor group).DescentData originalCover := by
  let F := SubcanonicalSheafStack.torsorPseudofunctor group
  have : (F.toDescentData originalCover).IsEquivalence :=
    F.isEquivalence_toDescentData originalCover original_covering
  exact sliceLine.symm.trans (F.toDescentData originalCover).asEquivalence

def originalQuotientDescent : SheafSliceQuotient.Object ActionQuotientStack.targetAction lineObject ≌
    (SubcanonicalSheafStack.quotientPseudofunctor ActionQuotientStack.targetAction).DescentData originalCover := by
  let F := SubcanonicalSheafStack.quotientPseudofunctor ActionQuotientStack.targetAction
  have : (F.toDescentData originalCover).IsEquivalence :=
    F.isEquivalence_toDescentData originalCover original_covering
  exact genuineSlice.symm.trans (F.toDescentData originalCover).asEquivalence

/-- Actual chart objects recover through original-site family descent. -/
example (b : Bool) : chartSlice b ≅
    originalTorsorDescent.inverse.obj (originalTorsorDescent.functor.obj (chartSlice b)) :=
  originalTorsorDescent.unitIso.app _

/-- The proper-cover recovery is natural on all compatible arrows. -/
example {P Q : SheafSliceQuotient.Object ActionQuotientStack.targetAction lineObject} (h : P ⟶ Q) :
    originalQuotientDescent.inverse.map (originalQuotientDescent.functor.map h) ≫
        (originalQuotientDescent.unitIso.app Q).inv =
      (originalQuotientDescent.unitIso.app P).inv ≫ h :=
  originalQuotientDescent.unitIso.inv.naturality h

example (P : SheafTorsor.Torsor group lineSheaf) :
    (SheafSliceTorsor.forward J lineObject).map
        (SubcanonicalSheafStack.TorsorExtension.compositionIso P (scale 2) (scale 3)).hom ≫
      (SheafSliceTorsor.restrictionComparison J (scale 3)).hom.app
        (SheafTorsor.reindex P (J.yoneda.map (scale 2))) ≫
      (SheafSliceTorsor.restriction J (scale 3)).map
        ((SheafSliceTorsor.restrictionComparison J (scale 2)).hom.app P) =
    (SheafSliceTorsor.restrictionComparison J (scale 3 ≫ scale 2)).hom.app P ≫
      (SheafSliceTorsor.restrictionComp J (scale 2) (scale 3)).hom.app
        ((SheafSliceTorsor.forward J lineObject).obj P) :=
  SubcanonicalTorsor.torsor_composition_coherence (scale 2) (scale 3) P

example (P : SheafActionQuotient.Object ActionQuotientStack.targetAction lineSheaf) :
    (SheafSliceQuotient.forward ActionQuotientStack.targetAction lineObject).map
        (SubcanonicalTorsor.quotientCompositionIso P (scale 2) (scale 3)).hom ≫
      (SheafSliceQuotient.restrictionComparison ActionQuotientStack.targetAction (scale 3)).hom.app
        (SheafActionQuotient.reindex P (J.yoneda.map (scale 2))) ≫
      (SheafSliceQuotient.restriction ActionQuotientStack.targetAction (scale 3)).map
        ((SheafSliceQuotient.restrictionComparison ActionQuotientStack.targetAction (scale 2)).hom.app P) =
    (SheafSliceQuotient.restrictionComparison ActionQuotientStack.targetAction (scale 3 ≫ scale 2)).hom.app P ≫
      (SheafSliceQuotient.restrictionComp ActionQuotientStack.targetAction (scale 2) (scale 3)).hom.app
        ((SheafSliceQuotient.forward ActionQuotientStack.targetAction lineObject).obj P) :=
  SubcanonicalTorsor.quotient_composition_coherence (scale 2) (scale 3) P

end Examples.SubcanonicalTorsor
