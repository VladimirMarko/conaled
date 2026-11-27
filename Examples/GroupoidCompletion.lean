import SquareKit.SheafGroupoidCompletion
import SquareKit.SmoothActionGroupoid
import Examples.SmoothManifoldAction
import Examples.SmoothTorsors

/-! Completion retains ineffective arrows and realizes local data with no global chart. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff
namespace Examples.GroupoidCompletion
open CategoryTheory Opposite SquareKit
open ManifoldRealization EuclideanOpen SmoothOpenSite
open Orbifolds.QuarterTurn
attribute [local instance] SmoothManifoldAction.trivial

abbrev line := object 1 (Space 1)
abbrev representation := SquareKit.SmoothManifoldAction.representation (SmoothManifoldAction.smooth C4)
abbrev action := representation.action

/-- Every locally varying group label acts trivially, not just constant labels. -/
theorem action_trivial (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup C4).obj.obj U) (x : line.obj.obj U) : action.act U g x = x := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp line.property)
    (Presheaf.imageSieve (constantLabel C4) g)
    (Presheaf.imageSieve_mem topology (constantLabel C4) g)).isSeparatedFor.ext
  intro V f hf
  obtain ⟨k, hk⟩ := hf
  rw [action.natural, ← hk]
  change representation.act _ ((constantLabel C4).app _ k) _ = _
  rw [representation.act_constant]
  change (ManifoldRealization.map (id : Space 1 → Space 1) contMDiff_id).hom.app _ _ = _
  rw [ManifoldRealization.map_id]
  rfl

/-- A constant smooth target over any parameter, constructed through the zero-dimensional test. -/
def zero (X : Sheaf topology Type) : X ⟶ line :=
  SmoothOpenSite.tuple (fun i : Fin 0 => Fin.elim0 i) ≫ (fullPowerIso 0).inv ≫
    SquareKit.SmoothManifoldAction.hat (fun _ : ordinaryOpen (full 0) => (0 : Space 1)) contMDiff_const

/-- An invariant target equips any torsor with an equivariant target map. -/
def invariantTarget {B M : Sheaf topology Type}
    (a : SheafActionQuotient.Action (locallyConstantGroup C4) M)
    (P : SheafTorsor.Torsor (locallyConstantGroup C4) B) (m : B ⟶ M)
    (hm : ∀ U g x, a.act U g (m.hom.app U x) = m.hom.app U x) :
    SheafActionQuotient.Object a B where
  torsor := P
  value x _ := m.hom.app x.obj x.val
  natural {x y} f _ := by
    exact (NatTrans.naturality_apply m.hom f.hom x.val).symm.trans
      (congrArg (m.hom.app y.obj) f.map_val)
  equivariant x g _ := (hm x.obj g _).symm

/-- The existing nontrivial clutching torsor has an invariant constant line target. -/
def genuine : SheafActionQuotient.Object action SmoothClutching.base :=
  invariantTarget action SmoothTorsors.nontrivialTorsor (zero SmoothClutching.base)
    (fun U g _ => action_trivial U g _)

variable {A : Sheaf topology Type} (e : A ≅ SheafGroupoidAction.arrows
  (G := locallyConstantGroup C4) (M := line))
abbrev input := SheafGroupoidCompletion.presentation action e
abbrev output := SheafGroupoidCompletion.completion action
abbrev unit := SheafGroupoidCompletion.unit action e

def fullyFaithful (X : Sheaf topology Type) :
    (StackDescentTransformation.component (unit e) X).FullyFaithful :=
  SheafGroupoidCompletion.quotientFullyFaithful action e

/-- This uses the actual total-space cover and the tautological local trivialization. -/
def localPresentation : StackificationUniversal.LocalPresentation
    (SheafCover.topology (J := topology)) (unit e) genuine := by
  let Q := SheafActionQuotient.reindex genuine (SplitSheaf.p genuine.torsor.family)
  let t := SheafTorsor.ofSection Q.torsor (SplitSheaf.q genuine.torsor.family)
  exact {
    domain := SplitSheaf.extension genuine.torsor.family
    cover := SplitSheaf.p genuine.torsor.family
    covering := ⟨_, _, inferInstance, Sieve.ofArrows_mk _ _ ()⟩
    object := ⟨Q.sectionMap (SheafTorsor.sectionOfArrow t)⟩
    comparison := (Q.chartOfTrivialization t).toIso }

def localData := (localPresentation e).sourceData (fullyFaithful e)

/-- Completing genuine local groupoid arrows adds an object with no global input chart. -/
theorem no_global_chart :
    ¬ ∃ N : (SheafGroupoidCompletion.operations action e).Object SmoothClutching.base,
      Nonempty (((input e).toDescentData (fun _ : Unit => (localPresentation e).cover)).obj N ≅
        localData e) := by
  rintro ⟨N, ⟨h⟩⟩
  let r := (localPresentation e).ambientRecovery (fullyFaithful e) N h
  exact SmoothTorsors.nontrivialTorsor_no_section
    ⟨SheafTorsor.sectionOfArrow r.hom.torsorArrow⟩

example : (input e).IsPrestack (SheafCover.topology (J := topology)) := inferInstance

def baseObject : (SheafGroupoidCompletion.operations action e).Object SmoothTorsors.point :=
  ⟨zero SmoothTorsors.point⟩

def labelledLoop (g : C4) :
    SheafActionPresentation.Object.mk (a := action) (zero SmoothTorsors.point) ⟶
      SheafActionPresentation.Object.mk (a := action) (zero SmoothTorsors.point) :=
  ⟨constantSection _ g, by ext U z; exact action_trivial U _ _⟩

def loop (g : C4) : baseObject e ⟶ baseObject e :=
  (SheafGroupoidCompletion.toPresentationFullyFaithful action e).preimage (labelledLoop g)

@[simp] theorem loop_recovery (g : C4) :
    (SheafGroupoidCompletion.toPresentation action e).map (loop e g) = labelledLoop g :=
  (SheafGroupoidCompletion.toPresentationFullyFaithful action e).map_preimage _

theorem loop_distinct : loop e quarterTurn ≠ loop e 1 := by
  intro h
  have hh := congrArg ((SheafGroupoidCompletion.toPresentation action e).map) h
  rw [loop_recovery, loop_recovery] at hh
  have he := congrArg (fun k => k.label) hh
  exact SmoothTorsors.nonidentity_loop (congrArg SheafTorsor.regularArrow he)

/-- The actual completion unit retains the ineffective automorphisms. -/
theorem completed_loops_distinct :
    (SheafGroupoidCompletion.quotient action e).map (loop e quarterTurn) ≠
      (SheafGroupoidCompletion.quotient action e).map (loop e 1) := by
  intro h
  exact loop_distinct e ((SheafGroupoidCompletion.quotientFullyFaithful action e).map_injective h)

include e in
/-- Every discrete observation, including an orbit set, loses these retained arrows. -/
theorem discrete_erasure_not_faithful {B : Type}
    (F : SheafActionQuotient.Object action SmoothTorsors.point ⥤ Discrete B) : ¬ F.Faithful := by
  intro hF
  let := hF
  apply completed_loops_distinct e
  apply F.map_injective
  exact Subsingleton.elim _ _

open scoped CategoryTheory.Pseudofunctor.StrongTrans
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf topology Type)ᵒᵖ) Cat.{0,1})
  [T.IsStack (SheafCover.topology (J := topology))]

def universal : (output ⟶ T) ≌ (input e ⟶ T) :=
  SheafGroupoidCompletion.universalEquivalence action e T

def modifications (Φ Ψ : output ⟶ T) : (Φ ⟶ Ψ) ≃ (unit e ≫ Φ ⟶ unit e ≫ Ψ) :=
  SheafGroupoidCompletion.modificationEquiv action e T Φ Ψ

example : (universal e T).functor = StackLocalGeneration.restriction (unit e) T := rfl

section Geometric
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩

/-- The selected actual smooth arrow manifold supplies the completion input. -/
def geometricArrowIso := SmoothActionGroupoid.arrowIso (d := 1) (G := C4) (M := Space 1)

/-- The non-effective descent control uses the geometric, all-stage arrow comparison. -/
theorem geometric_no_global_chart :
    ¬ ∃ N : (SheafGroupoidCompletion.operations action geometricArrowIso).Object SmoothClutching.base,
      Nonempty (((input geometricArrowIso).toDescentData
        (fun _ : Unit => (localPresentation geometricArrowIso).cover)).obj N ≅
          localData geometricArrowIso) := no_global_chart geometricArrowIso

theorem geometric_ineffective_retained :
    (SheafGroupoidCompletion.quotient action geometricArrowIso).map
        (loop geometricArrowIso quarterTurn) ≠
      (SheafGroupoidCompletion.quotient action geometricArrowIso).map
        (loop geometricArrowIso 1) := completed_loops_distinct geometricArrowIso

def geometricUniversal : (output ⟶ T) ≌ (input geometricArrowIso ⟶ T) :=
  universal geometricArrowIso T
end Geometric

namespace TrivialGroup

abbrev action := (SquareKit.SmoothManifoldAction.representation
  (SmoothManifoldAction.smooth PUnit)).action
abbrev arrowIso : SheafGroupoidAction.arrows (G := locallyConstantGroup PUnit) (M := line) ≅
    SheafGroupoidAction.arrows (G := locallyConstantGroup PUnit) (M := line) := Iso.refl _
abbrev input := SheafGroupoidCompletion.presentation action arrowIso
abbrev output := SheafGroupoidCompletion.completion action
abbrev unit := SheafGroupoidCompletion.unit action arrowIso

/-- Sheafification of the trivial group has no nonidentity generalized sections. -/
theorem label_eq_one (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup PUnit).obj.obj U) : g = 1 := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    (locallyConstantGroupSheaf PUnit).property)
    (Presheaf.imageSieve (constantLabel PUnit) g)
    (Presheaf.imageSieve_mem topology (constantLabel PUnit) g)).isSeparatedFor.ext
  intro V f hf
  obtain ⟨k, hk⟩ := hf
  change (locallyConstantGroup PUnit).obj.map f.op g =
    (locallyConstantGroup PUnit).obj.map f.op 1
  rw [map_one, ← hk]
  have h : k = 1 := @Subsingleton.elim PUnit inferInstance k 1
  rw [h, map_one]

/-- A trivial-group torsor's locally surjective display is also injective. -/
theorem display_isIso {X : Sheaf topology Type}
    (P : SheafTorsor.Torsor (locallyConstantGroup PUnit) X) :
    IsIso (SplitSheaf.p P.family) := by
  have hi : Sheaf.IsLocallyInjective (SplitSheaf.p P.family) := by
    apply (Sheaf.isLocallyInjective_iff_injective _).mpr
    intro U x y h
    rcases x with ⟨x, p⟩
    rcases y with ⟨y, q⟩
    change x = y at h
    subst y
    have hpq : p = q := by
      obtain ⟨g, hg, _⟩ := P.principal (X.obj.elementsMk U x) p q
      rw [label_eq_one U g, P.one_act] at hg
      exact hg
    cases hpq
    rfl
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi, inferInstance⟩

/-- Every trivial-group torsor has a global section, obtained from its display inverse. -/
def torsorSection {X : Sheaf topology Type}
    (P : SheafTorsor.Torsor (locallyConstantGroup PUnit) X) : SplitSheaf.Tm P.family := by
  letI := display_isIso P
  exact (SplitSheaf.terms P.family).symm
    ⟨inv (SplitSheaf.p P.family), IsIso.inv_hom_id _⟩

/-- The actual completion unit reaches every whole-fiber quotient object. -/
instance quotient_essSurj (X : Sheaf topology Type) :
    (SheafGroupoidCompletion.quotient (X := X) action arrowIso).EssSurj where
  mem_essImage P := by
    let t := SheafTorsor.ofSection P.torsor (torsorSection P.torsor)
    exact ⟨⟨P.sectionMap (SheafTorsor.sectionOfArrow t)⟩,
      ⟨(P.chartOfTrivialization t).toIso⟩⟩

/-- Effective descent transfers through the actual fully faithful quotient unit. -/
instance input_isStack : input.IsStack (SheafCover.topology (J := topology)) where
  toIsPrestack := inferInstance
  essSurj_of_sieve {S} R hR := by
    let f := fun k : R.arrows.category => k.obj.hom
    let E := StackificationUniversal.descentEquivalence output
      (show Sieve.ofArrows _ f ∈ SheafCover.topology (J := topology) S by
        simpa only [f, Sieve.ofArrows_category] using hR)
    refine ⟨fun D => ?_⟩
    let K := (StackDescentTransformation.map unit f).obj D
    let P := E.inverse.obj K
    obtain ⟨m, ⟨hm⟩⟩ :=
      Functor.EssSurj.mem_essImage
        (SheafGroupoidCompletion.quotient (X := S) action arrowIso) P
    refine ⟨m, ⟨?_⟩⟩
    apply (StackDescentTransformation.mapFullyFaithful unit
      (fun _ => SheafGroupoidCompletion.quotientFullyFaithful action arrowIso)).preimageIso
    exact StackDescentTransformation.canonicalObjIso unit f m ≪≫
      (output.toDescentData f).mapIso hm ≪≫ E.counitIso.app K

/-- Already-stack recovery now applies to the new presentation and its actual unit. -/
def alreadyStack (X : Sheaf topology Type) :
    input.obj (.mk (op X)) ≌ output.obj (.mk (op X)) :=
  StackificationUniversal.alreadyStackEquivalence (η := unit)
    (fun _ => SheafGroupoidCompletion.quotientFullyFaithful action arrowIso)
    (SheafGroupoidCompletion.locallyGenerating action arrowIso) X

/-- The forward equivalence is the actual-arrow quotient, not an identity control. -/
theorem alreadyStack_functor (X : Sheaf topology Type) :
    (alreadyStack X).functor = SheafGroupoidCompletion.quotient action arrowIso := rfl

end TrivialGroup

end Examples.GroupoidCompletion
