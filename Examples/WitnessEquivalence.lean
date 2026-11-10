import SquareKit.WitnessComma

namespace Examples.WitnessEquivalence
open SquareKit

def one : CategoryOps Unit where
  Hom _ _ := Unit
  ident := ()
  comp _ _ := ()

/-- NAND is deliberately not associative: Equivalent asks for operations only. -/
def witnesses : SquareKit.WitnessEquivalence one where
  Rel _ _ := Bool
  refl _ := false
  symm := Bool.not
  trans p q := !(p && q)

theorem witnesses_distinct : (false : witnesses.Rel (a := ()) (b := ()) () ()) ≠ true := by
  decide

theorem trans_not_associative :
    witnesses.trans (a := ()) (b := ()) (f := ()) (g := ()) (h := ())
      (witnesses.trans (g := ()) false false) true ≠
    witnesses.trans (g := ()) false (witnesses.trans (g := ()) false true) := by
  change false ≠ true
  decide

def congruence : witnesses.Congr := ⟨fun _ _ => false⟩
def laws : witnesses.Laws := ⟨fun _ => false, fun _ => false, fun _ _ _ => false⟩
def preserves : SquareKit.WitnessEquivalence.Preservation (RawMap.id one) witnesses witnesses :=
  ⟨fun h => h, false, fun _ _ => false⟩

def reflection (chosen : Bool) :
    SquareKit.WitnessEquivalence.Reflection (RawMap.id one) witnesses witnesses :=
  fun _ => chosen

def transported (chosen : Bool) : witnesses.Laws :=
  SquareKit.WitnessEquivalence.transportLaws preserves (reflection chosen) congruence laws

theorem transport_retains_choice :
    (transported false).id_comp (a := ()) (b := ()) () ≠ (transported true).id_comp (a := ()) (b := ()) () := by
  change false ≠ true
  decide

/-- The unchanged quotient construction consumes explicitly erased laws. -/
@[instance_reducible] def quotientCategory := HomQuotient.category congruence.erase laws.erase

def object : Comma.Obj (RawMap.id one) (RawMap.id one) := ⟨(), (), ()⟩
def square (chosen : Bool) : WitnessComma.Hom witnesses object object := ⟨(), (), chosen⟩

theorem squares_distinct : square false ≠ square true := by
  intro h
  exact Bool.false_ne_true (congrArg WitnessComma.Hom.commutes h)

theorem erased_squares_equal : (square false).erase = (square true).erase :=
  WitnessComma.Hom.erase_eq _ _ rfl rfl

theorem comma_identity_recovers :
    (WitnessComma.ident congruence laws preserves preserves object).erase =
      Comma.ident congruence.erase laws.erase preserves.erase preserves.erase object :=
  WitnessComma.erase_ident _ _ _ _ _

theorem comma_composition_recovers :
    (WitnessComma.comp congruence laws preserves preserves (square true) (square false)).erase =
      Comma.comp congruence.erase laws.erase preserves.erase preserves.erase
        (square true).erase (square false).erase :=
  WitnessComma.erase_comp _ _ _ _ _ _

theorem ordinary_relation_recovers (E : HomEquiv one) :
    (SquareKit.WitnessEquivalence.ofHomEquiv E).erase.Rel (a := ()) (b := ()) () () ↔ E.Rel (a := ()) (b := ()) () () :=
  SquareKit.WitnessEquivalence.erase_ofHomEquiv E () ()

end Examples.WitnessEquivalence
