import SquareKit.SheafFamily
import SquareKit.TypeFamily
import SquareKit.Internal.SheafFamilies
import Examples.SheafFunctions

/-! Experimental dependent families on the finite site. Fibers depend on the
Boolean base value; local witnesses still need not yield a global term. -/
noncomputable section
namespace Examples.SheafFamilies
open CategoryTheory Limits Opposite SquareKit.Family SquareKit.SheafFamily
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFunctions

/-- The sheaf family with one value over false and none over true. -/
def falsePoint : SheafImage.terminal ⟶ D := ⟨{ app _ := ↾fun _ => false }⟩
def truePoint : SheafImage.terminal ⟶ D := ⟨{ app _ := ↾fun _ => true }⟩

abbrev Fiber {A B : Sheaf topology Type} (p : A ⟶ B) (U : Diamondᵒᵖ) (b : B.obj.obj U) :=
  {a : A.obj.obj U // p.hom.app U a = b}

theorem false_fiber (U : Diamondᵒᵖ) : Nonempty (Fiber falsePoint U false) := ⟨⟨(), rfl⟩⟩
theorem true_fiber_empty (U : Diamondᵒᵖ) : IsEmpty (Fiber falsePoint U true) :=
  ⟨fun x => Bool.noConfusion x.property⟩

abbrev reversed := pullback falsePoint negation
abbrev reversedDisplay : reversed ⟶ D := reindex falsePoint negation

/-- The public stage comparison detects the reversal at every object. -/
theorem reversed_fiber (U : Diamondᵒᵖ) (b : Bool) :
    Nonempty (Fiber reversedDisplay U b) ↔ b = true := by
  constructor
  · rintro ⟨⟨x,hx⟩⟩
    have h := (sectionsEquiv falsePoint negation U x).property
    have hb := sectionsEquiv_snd falsePoint negation U x
    have hxb := hb.trans hx
    change false = !(sectionsEquiv falsePoint negation U x).val.2 at h
    rw [hxb] at h
    cases b
    · exact Bool.noConfusion h
    · rfl
  · intro hb
    subst b
    let z : Types.PullbackObj (falsePoint.hom.app U) (negation.hom.app U) := ⟨((),true), rfl⟩
    refine ⟨⟨(sectionsEquiv falsePoint negation U).symm z, ?_⟩⟩
    have h := sectionsEquiv_snd falsePoint negation U ((sectionsEquiv falsePoint negation U).symm z)
    simpa only [Equiv.apply_symm_apply] using h.symm

/-- Pair the true base point with the sole value of the original family. -/
def trueLift : SheafImage.terminal ⟶ reversed :=
  SquareKit.Family.pair falsePoint negation (𝟙 SheafImage.terminal) truePoint rfl

theorem trueLift_display : trueLift ≫ reversedDisplay = truePoint :=
  pair_reindex falsePoint negation (𝟙 SheafImage.terminal) truePoint rfl

theorem trueLift_value : trueLift ≫ comparison falsePoint negation = 𝟙 SheafImage.terminal :=
  pair_comparison falsePoint negation (𝟙 SheafImage.terminal) truePoint rfl

/-- A dependent term exists after restricting the reversed family to true. -/
def trueTerm : Term (reindex reversedDisplay truePoint) :=
  (termEquiv reversedDisplay truePoint).symm ⟨trueLift, trueLift_display⟩

theorem trueTerm_value : trueTerm.val ≫ comparison reversedDisplay truePoint = trueLift :=
  congrArg Subtype.val ((termEquiv reversedDisplay truePoint).apply_symm_apply
    ⟨trueLift, trueLift_display⟩)

/-- Chosen pullbacks transport this dependent term under identity. -/
theorem trueTerm_identity :
    (termSub (reindex reversedDisplay truePoint) (𝟙 _) trueTerm).val ≫
      (identityIso (reindex reversedDisplay truePoint)).hom = trueTerm.val :=
  termSub_identity _ _

/-- Substitution through Bool parameters and negation composes by comparison. -/
theorem trueTerm_composition :
    (termSub (reindex (reindex reversedDisplay truePoint) base) negation
      (termSub (reindex reversedDisplay truePoint) base trueTerm)).val ≫
        (compositionIso (reindex reversedDisplay truePoint) base negation).hom =
          (termSub (reindex reversedDisplay truePoint) (negation ≫ base) trueTerm).val :=
  termSub_composition _ _ _ _

/-- The original family has no section over all Bool values. -/
theorem no_total_term : ¬ Nonempty (Term falsePoint) := by
  rintro ⟨t⟩
  have h := congrArg (fun k : D ⟶ D => k.hom.app (op X) true) t.property
  exact Bool.noConfusion h

/-- Local existential truth cannot be promoted to a dependent term. -/
theorem locally_inhabited_without_term :
    SquareKit.SheafImage.localImage ⊤ toTerminal = ⊤ ∧ ¬ Nonempty (Term toTerminal) := by
  refine ⟨localImage_top, ?_⟩
  rintro ⟨t⟩
  exact nomatch t.val.hom.app (op X) ()
end Examples.SheafFamilies
