import SquareKit.SheafifiedQuotientStack
import SquareKit.SheafifiedSliceQuotient
import SquareKit.SheafifiedSubcanonical
import Examples.SubcanonicalTorsor
import Mathlib.CategoryTheory.Discrete.Basic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafifiedYoneda.Control
open CategoryTheory Opposite

abbrev site : GrothendieckTopology (Discrete Bool) := ⊤

theorem raw_not_sheaf : ¬ Presheaf.IsSheaf site (yoneda.obj (Discrete.mk true)) := by
  intro h
  have h' := (isSheaf_iff_isSheaf_of_type _ _).mp h
  let x : Presieve.FamilyOfElements (yoneda.obj (Discrete.mk true))
      (⊥ : Sieve (Discrete.mk false)).arrows := fun _ _ hf => False.elim hf
  have hx : x.Compatible := by
    intro Y Z W f g h₁ h₂ hf hg
    exact False.elim hg
  obtain ⟨a, _, _⟩ := h' (⊥ : Sieve (Discrete.mk false)) (by trivial) x hx
  have he := Discrete.eq_of_hom a
  cases he

theorem not_subcanonical : ¬ site.Subcanonical := by
  intro h
  let := h
  exact raw_not_sheaf (site.yoneda.obj (Discrete.mk true)).property

theorem replacement_isSheaf : Presheaf.IsSheaf site
    ((SheafifiedYoneda.functor site).obj (Discrete.mk true)).obj :=
  ((SheafifiedYoneda.functor site).obj (Discrete.mk true)).property

/-- The empty original cover remains a cover of the replacement on this site. -/
theorem replacement_empty_cover :
    SheafFamilyCover.JointlyLocallySurjective
      (fun i : Empty => (SheafifiedYoneda.functor site).map
        (show (Empty.elim i : Discrete Bool) ⟶ Discrete.mk true from Empty.elim i)) :=
  SheafifiedYoneda.jointlyLocallySurjective site _ (by trivial)

/-- Evaluation still represents sections although the raw representable is not a sheaf. -/
example (X : Sheaf site (Type 0)) :
    ((SheafifiedYoneda.functor site).obj (Discrete.mk true) ⟶ X) ≃
      X.obj.obj (op (Discrete.mk true)) := SheafifiedYoneda.evaluation site

open Limits

abbrev controlGroup : Sheaf site GrpCat.{0} := ⊤_ (Sheaf site GrpCat.{0})

def regularAction : SheafActionQuotient.Action controlGroup (SheafTorsor.groupSheaf controlGroup) where
  act U g m := g * (show controlGroup.obj.obj U from m)
  one_act U m := one_mul (show controlGroup.obj.obj U from m)
  mul_act U g h m := mul_assoc g h (show controlGroup.obj.obj U from m)
  natural {U _} f g m := (controlGroup.obj.map f).hom.map_mul g (show controlGroup.obj.obj U from m)

example : (SheafifiedSheafStack.torsorPseudofunctor controlGroup).IsStack site := inferInstance
example : (SheafifiedSheafStack.quotientPseudofunctor regularAction).IsStack site := inferInstance

/-- The non-subcanonical site admits the independently defined ordinary slice torsors. -/
def sliceTorsors : SheafTorsor.Torsor controlGroup
    ((SheafifiedYoneda.functor site).obj (Discrete.mk true)) ≌
      SheafSliceTorsor.Torsor site (Discrete.mk true) controlGroup :=
  SheafifiedSliceTorsor.equivalence site _

def sliceQuotients : SheafActionQuotient.Object regularAction
    ((SheafifiedYoneda.functor site).obj (Discrete.mk true)) ≌
      SheafSliceQuotient.Object regularAction (Discrete.mk true) :=
  SheafifiedSliceQuotient.equivalence regularAction _

/-- Actual objects exist on both sides of the non-subcanonical comparison. -/
def sliceTrivial := sliceTorsors.functor.obj
  (SheafTorsor.trivial controlGroup ((SheafifiedYoneda.functor site).obj (Discrete.mk true)))

example : sliceTrivial ≅ sliceTorsors.functor.obj (sliceTorsors.inverse.obj sliceTrivial) :=
  (sliceTorsors.counitIso.app sliceTrivial).symm

def oneLabel : (SheafifiedYoneda.functor site).obj (Discrete.mk true) ⟶
    SheafTorsor.groupSheaf controlGroup := ⟨{
  app U := ↾fun _ => (1 : controlGroup.obj.obj U)
  naturality {U V} f := by
    ext x
    exact (controlGroup.obj.map f).hom.map_one.symm }⟩

def sliceRegular := sliceQuotients.functor.obj (SheafActionQuotient.chart regularAction oneLabel)

example : sliceRegular ≅ sliceQuotients.functor.obj (sliceQuotients.inverse.obj sliceRegular) :=
  (sliceQuotients.counitIso.app sliceRegular).symm

abbrev emptyFamily : ∀ i : Empty, (Empty.elim i : Discrete Bool) ⟶ Discrete.mk true :=
  fun i => Empty.elim i

/-- Empty covers are accepted exactly where the original topology accepts them. -/
example : ((SheafifiedSheafStack.torsorPseudofunctor controlGroup).toDescentData
    emptyFamily).IsEquivalence :=
  SheafifiedSheafStack.torsor_isEquivalence_toDescentData controlGroup emptyFamily (by trivial)

example : ((SheafifiedSheafStack.quotientPseudofunctor regularAction).toDescentData
    emptyFamily).IsEquivalence :=
  SheafifiedSheafStack.quotient_isEquivalence_toDescentData regularAction emptyFamily (by trivial)

end SquareKit.SheafifiedYoneda.Control

namespace Examples.SheafifiedTorsor
open CategoryTheory Opposite SquareKit
open SubcanonicalTorsor

/-- The proper two-open cover is processed through sheafified representables. -/
example : SheafFamilyCover.JointlyLocallySurjective
    (fun b => (SheafifiedYoneda.functor J).map (originalCover b)) :=
  SheafifiedYoneda.jointlyLocallySurjective J originalCover original_covering

/-- Sheafification does not turn either proper-cover member into a covering map. -/
example (b : Bool) : ¬ Presheaf.IsLocallySurjective J
    ((SheafifiedYoneda.functor J).map (originalCover b)).hom := by
  intro h
  have hc := SheafifiedYoneda.covering_of_jointlyLocallySurjective J
    (fun _ : PUnit => originalCover b) ((SheafFamilyCover.singleton_iff _).mpr h)
  have hj := SubcanonicalSheafStack.yoneda_jointlyLocallySurjective
    (fun _ : PUnit => originalCover b) hc
  exact original_member_not_surjective b ((SheafFamilyCover.singleton_iff _).mp hj)

def originalTorsorDescent : SheafSliceTorsor.Torsor J lineObject SmoothTorsors.group ≌
    (SheafifiedSheafStack.torsorPseudofunctor SmoothTorsors.group).DescentData originalCover := by
  let F := SheafifiedSheafStack.torsorPseudofunctor SmoothTorsors.group
  letI := SheafifiedSheafStack.torsor_isEquivalence_toDescentData
    SmoothTorsors.group originalCover original_covering
  exact (SheafifiedSliceTorsor.equivalence J lineObject).symm.trans
    (F.toDescentData originalCover).asEquivalence

def originalQuotientDescent : SheafSliceQuotient.Object ActionQuotientStack.targetAction lineObject ≌
    (SheafifiedSheafStack.quotientPseudofunctor ActionQuotientStack.targetAction).DescentData originalCover :=
  (SheafifiedSliceQuotient.equivalence ActionQuotientStack.targetAction lineObject).symm.trans
    (SheafifiedSheafStack.quotientDescentEquivalence ActionQuotientStack.targetAction
      originalCover original_covering)

/-- The same nontrivial clutching charts recover through the arbitrary-site route. -/
def chartRecovery (b : Bool) : chartSlice b ≅
    originalTorsorDescent.inverse.obj (originalTorsorDescent.functor.obj (chartSlice b)) :=
  originalTorsorDescent.unitIso.app _

/-- Recovery retains every compatible map, including automorphisms. -/
example {P Q : SheafSliceQuotient.Object ActionQuotientStack.targetAction lineObject} (h : P ⟶ Q) :
    originalQuotientDescent.inverse.map (originalQuotientDescent.functor.map h) ≫
        (originalQuotientDescent.unitIso.app Q).inv =
      (originalQuotientDescent.unitIso.app P).inv ≫ h :=
  originalQuotientDescent.unitIso.inv.naturality h

abbrev overlapComparison := SheafifiedSliceTorsor.equivalence
  (G := SmoothTorsors.group) J overlapObject

/-- Nonconstant clutching remains distinct after ordinary-slice recovery. -/
theorem recovered_clutching_distinct :
    overlapComparison.inverse.map (sliceOverlap.functor.map clutchingArrow) ≠
      overlapComparison.inverse.map (sliceOverlap.functor.map constantArrow) := by
  intro h
  exact slice_clutching_distinct (overlapComparison.inverse.map_injective h)

theorem recovered_clutching_not_identity :
    overlapComparison.inverse.map (sliceOverlap.functor.map clutchingArrow) ≠
      𝟙 (overlapComparison.inverse.obj
        (sliceOverlap.functor.obj (SheafTorsor.trivial SmoothTorsors.group SmoothClutching.puncturedSheaf))) := by
  intro h
  apply slice_clutching_not_identity
  apply overlapComparison.inverse.map_injective
  exact h.trans (overlapComparison.inverse.map_id _).symm

abbrev stabilizerComparison := SheafifiedSliceQuotient.equivalence
  ActionQuotientStack.ineffective pointObject

/-- The arbitrary-site route retains the original ineffective stabilizer labels. -/
theorem recovered_stabilizers_distinct :
    stabilizerComparison.inverse.map
      (stabilizerSlice.functor.map (ActionQuotientStack.stabilizer Orbifolds.QuarterTurn.quarterTurn)) ≠
    stabilizerComparison.inverse.map
      (stabilizerSlice.functor.map (ActionQuotientStack.stabilizer 1)) := by
  intro h
  exact slice_stabilizers_distinct (stabilizerComparison.inverse.map_injective h)

/-- On the smooth overlap, an empty family still loses distinct torsor arrows. -/
example : ¬ ((SheafifiedSheafStack.torsorPseudofunctor SmoothTorsors.group).toDescentData
    (fun i : Empty => (show Empty.elim i ⟶ overlapObject from Empty.elim i))).Faithful := by
  intro h
  let := h
  apply recovered_clutching_distinct
  apply ((SheafifiedSheafStack.torsorPseudofunctor SmoothTorsors.group).toDescentData
    (fun i : Empty => (show Empty.elim i ⟶ overlapObject from Empty.elim i))).map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  exact i.elim

/-- Empty descent cannot erase the ineffective stabilizers on a nonempty smooth point. -/
example : ¬ ((SheafifiedSheafStack.quotientPseudofunctor ActionQuotientStack.ineffective).toDescentData
    (fun i : Empty => (show Empty.elim i ⟶ pointObject from Empty.elim i))).Faithful := by
  intro h
  let := h
  apply recovered_stabilizers_distinct
  apply ((SheafifiedSheafStack.quotientPseudofunctor ActionQuotientStack.ineffective).toDescentData
    (fun i : Empty => (show Empty.elim i ⟶ pointObject from Empty.elim i))).map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  exact i.elim

abbrev swappedOriginalCover (b : Bool) := originalCover (!b)

private theorem swap_cover_eq {C : Type*} [Category C] {X : C} {Y : Bool → C}
    (f : ∀ b, Y b ⟶ X) :
    Sieve.ofArrows (fun b => Y (!b)) (fun b => f (!b)) = Sieve.ofArrows Y f := by
  ext U g
  rw [Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨b, k, hk⟩
    exact ⟨!b, k, hk⟩
  · rintro ⟨b, k, hk⟩
    cases b
    · exact ⟨true, k, hk⟩
    · exact ⟨false, k, hk⟩

theorem swapped_original_covering : Sieve.ofArrows _ swappedOriginalCover ∈ J lineObject := by
  rw [swap_cover_eq originalCover]
  exact original_covering

/-- Two nonidentity original-site substitutions commute with subcanonical recovery. -/
example :
    (SheafTorsor.Stack.functor SmoothTorsors.group).map ((SheafifiedYoneda.functor J).map (scale 2)).op ≫
      (SheafTorsor.Stack.functor SmoothTorsors.group).map ((SheafifiedYoneda.functor J).map (scale 3)).op ≫
      (SheafifiedSubcanonical.torsorComparison SmoothTorsors.group).hom.app (op lineObject) =
    (SheafifiedSubcanonical.torsorComparison SmoothTorsors.group).hom.app (op lineObject) ≫
      (SheafTorsor.Stack.functor SmoothTorsors.group).map (J.yoneda.map (scale 2)).op ≫
      (SheafTorsor.Stack.functor SmoothTorsors.group).map (J.yoneda.map (scale 3)).op :=
  SheafifiedSubcanonical.composition (SheafTorsor.Stack.functor SmoothTorsors.group) (scale 2) (scale 3)

example :
    (SheafActionQuotient.Stack.functor ActionQuotientStack.targetAction).map
        ((SheafifiedYoneda.functor J).map (scale 2)).op ≫
      (SheafActionQuotient.Stack.functor ActionQuotientStack.targetAction).map
        ((SheafifiedYoneda.functor J).map (scale 3)).op ≫
      (SheafifiedSubcanonical.quotientComparison ActionQuotientStack.targetAction).hom.app (op lineObject) =
    (SheafifiedSubcanonical.quotientComparison ActionQuotientStack.targetAction).hom.app (op lineObject) ≫
      (SheafActionQuotient.Stack.functor ActionQuotientStack.targetAction).map (J.yoneda.map (scale 2)).op ≫
      (SheafActionQuotient.Stack.functor ActionQuotientStack.targetAction).map (J.yoneda.map (scale 3)).op :=
  SheafifiedSubcanonical.composition (SheafActionQuotient.Stack.functor ActionQuotientStack.targetAction)
    (scale 2) (scale 3)

universe u' v'
variable (F : Pseudofunctor (LocallyDiscrete SmoothPresentationSite.Siteᵒᵖ) Cat.{v',u'})

def swapPull := Pseudofunctor.DescentData.pullFunctor F
  (f := originalCover) (f' := swappedOriginalCover) (α := Bool.not) (p := 𝟙 lineObject)
  (p' := fun _ => 𝟙 _) (by intro b; simp [swappedOriginalCover])

/-- Reindexing the proper original cover commutes with effective recovery on all maps. -/
def swapRecovery [F.IsStack J] :=
  letI := F.isEquivalence_toDescentData originalCover original_covering
  letI := F.isEquivalence_toDescentData swappedOriginalCover swapped_original_covering
  SheafFamilyDescent.recoveryNaturality F (f := originalCover) (g := swappedOriginalCover) Bool.not (𝟙 lineObject) (fun _ => 𝟙 _)
    (by intro b; simp [swappedOriginalCover]) ≪≫
      Functor.isoWhiskerLeft _ (Cat.Hom.toNatIso (F.mapId _)) ≪≫ Functor.rightUnitor _

def torsorSwapRecovery := swapRecovery (SheafifiedSheafStack.torsorPseudofunctor SmoothTorsors.group)
def quotientSwapRecovery := swapRecovery
  (SheafifiedSheafStack.quotientPseudofunctor ActionQuotientStack.targetAction)

end Examples.SheafifiedTorsor
