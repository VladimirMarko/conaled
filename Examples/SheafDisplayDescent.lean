import SquareKit.Internal.CoherentDisplayDescent
import SquareKit.SplitSheafConstant
import Examples.SheafFamilyCover

/-! Display descent retains noninvertible maps over a proper two-member cover. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace Examples.SheafDisplayDescent
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafFamilyCover

abbrev boolFamily := SplitSheaf.constant (constant Bool) (constant Bool)

def collapse : boolFamily ⟶ boolFamily where
  app _ := ↾fun _ => false

def flip : boolFamily ⟶ boolFamily where
  app _ := ↾Bool.not

abbrev point := (constant Bool).obj.elementsMk (op (Discrete.mk PUnit.unit)) false

theorem identity_ne_collapse : (𝟙 boolFamily) ≠ collapse := by
  intro h
  have he := congrArg (fun k : boolFamily ⟶ boolFamily => k.app point true) h
  cases he

theorem identity_ne_flip : (𝟙 boolFamily) ≠ flip := by
  intro h
  have he := congrArg (fun k : boolFamily ⟶ boolFamily => k.app point false) h
  cases he

/-- The category-valued consumer contains a genuinely noninvertible map. -/
theorem collapse_not_iso : ¬ IsIso collapse := by
  intro h
  have he : (𝟙 boolFamily) ≫ collapse = flip ≫ collapse := rfl
  exact identity_ne_flip ((cancel_mono collapse).mp he)

abbrev descentEquivalence := SheafDisplayFamilyDescent.equivalence inclusion inclusion_jointlyLocallySurjective
abbrev datum := descentEquivalence.functor.obj boolFamily
abbrev localCollapse := descentEquivalence.functor.map collapse

/-- The generic family theorem is used on a proper jointly covering family. -/
example : Sieve.ofArrows (fun _ : Bool => constant PUnit) inclusion ≠ ⊤ := family_sieve_proper
example (b : Bool) : ¬ Presheaf.IsLocallySurjective topology (inclusion b).hom :=
  member_not_surjective b

example : ¬ IsIso localCollapse := by
  intro h
  have : IsIso collapse := isIso_of_reflects_iso collapse descentEquivalence.functor
  exact collapse_not_iso this

/-- Recovery commutes with the noninvertible arrow, as an actual map. -/
example : collapse ≫ descentEquivalence.unitIso.hom.app boolFamily =
    descentEquivalence.unitIso.hom.app boolFamily ≫ descentEquivalence.inverse.map localCollapse := descentEquivalence.unitIso.hom.naturality collapse

example : descentEquivalence.inverse.obj datum ≅ boolFamily := (descentEquivalence.unitIso.app boolFamily).symm

/-- The empty cover of the empty context is effective without inhabited-index assumptions. -/
def emptyEquivalence := SheafDisplayFamilyDescent.equivalence emptyTargetFamily (by
  rw [SquareKit.SheafFamilyCover.empty_iff]
  intro U x
  exact x.elim)

/-- Dropping joint coverage loses maps: empty descent over a nonempty context
cannot distinguish the identity from a collapse. -/
theorem empty_not_faithful :
    ¬ ((SplitSheaf.pseudofunctor (J := topology)).toDescentData emptyFamily).Faithful := by
  intro hf
  apply identity_ne_collapse
  apply hf.map_injective
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  exact i.elim

abbrev displayPseudofunctor := SplitSheaf.pseudofunctor (J := topology)
local instance : (displayPseudofunctor.toDescentData inclusion).IsEquivalence := descentEquivalence.isEquivalence_functor

/-- Negating the base exchanges the two charts. -/
def swapPull := Pseudofunctor.DescentData.pullFunctor displayPseudofunctor
  (f := inclusion) (f' := inclusion) (α := Bool.not) (p := negation)
  (p' := fun _ => 𝟙 _) (by intro b; rfl)

def swapRecovery : swapPull ⋙ descentEquivalence.inverse ≅ descentEquivalence.inverse ⋙ SplitSheaf.restriction negation :=
  SheafFamilyDescent.recoveryNaturality displayPseudofunctor Bool.not negation (fun _ => 𝟙 _) (by intro b; rfl)

/-- Two successive nonidentity base changes recover the same actual display. -/
def repeatedRecovery (D : displayPseudofunctor.DescentData inclusion) :
    descentEquivalence.inverse.obj (swapPull.obj (swapPull.obj D)) ≅
      SplitSheaf.tySub (SplitSheaf.tySub (descentEquivalence.inverse.obj D) negation) negation :=
  swapRecovery.app _ ≪≫ (SplitSheaf.restriction negation).mapIso (swapRecovery.app D)

example (T : SplitSheaf.Ty (constant Bool)) :
    SplitSheaf.tySub (SplitSheaf.tySub T negation) negation =
      SplitSheaf.tySub T (negation ≫ negation) := rfl

example : negation ≠ 𝟙 (constant Bool) := by
  intro h
  have he := congrArg (fun k => k.hom.app (op (Discrete.mk PUnit.unit)) false) h
  cases he

/-- The two-step comparison also commutes with noninvertible arrows. -/
def repeatedRecoveryIso : (swapPull ⋙ swapPull) ⋙ descentEquivalence.inverse ≅
    (descentEquivalence.inverse ⋙ SplitSheaf.restriction negation) ⋙ SplitSheaf.restriction negation :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft swapPull swapRecovery ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight swapRecovery (SplitSheaf.restriction negation)

example :
    ((swapPull ⋙ swapPull) ⋙ descentEquivalence.inverse).map localCollapse ≫ repeatedRecoveryIso.hom.app datum =
      repeatedRecoveryIso.hom.app datum ≫
        ((descentEquivalence.inverse ⋙ SplitSheaf.restriction negation) ⋙
          SplitSheaf.restriction negation).map localCollapse :=
  repeatedRecoveryIso.hom.naturality localCollapse

/-- The same local collapse is recovered through coherent element-site codes. -/
abbrev coherentE := CoherentDisplayDescent.equivalence inclusion inclusion_jointlyLocallySurjective

example :
    coherentE.functor.map (coherentE.inverse.map localCollapse) ≫
        coherentE.counitIso.hom.app datum =
      coherentE.counitIso.hom.app datum ≫ localCollapse :=
  coherentE.counitIso.hom.naturality localCollapse

/-- Actual displays compare naturally with pullback on the same noninvertible map. -/
example :
    (SplitSheaf.restriction negation ⋙ SplitSheaf.toOver).map collapse ≫
        (SplitSheaf.displayReindex negation).hom.app boolFamily =
      (SplitSheaf.displayReindex negation).hom.app boolFamily ≫
        (SplitSheaf.toOver ⋙ Over.pullback negation).map collapse :=
  (SplitSheaf.displayReindex negation).hom.naturality collapse

/-- The direct total-space comparison uses the existing composition coherence. -/
example :
    (SplitSheaf.substitutionIso (SplitSheaf.tySub boolFamily negation) negation).hom ≫
      Family.map (SplitSheaf.p (SplitSheaf.tySub boolFamily negation))
        (Family.reindex (SplitSheaf.p boolFamily) negation) negation
        (SplitSheaf.substitutionIso boolFamily negation).hom
        (SplitSheaf.substitution_display boolFamily negation) ≫
      (Family.compositionIso (SplitSheaf.p boolFamily) negation negation).hom =
        (SplitSheaf.substitutionIso boolFamily (negation ≫ negation)).hom :=
  SplitSheaf.substitution_composition boolFamily negation negation

end Examples.SheafDisplayDescent
