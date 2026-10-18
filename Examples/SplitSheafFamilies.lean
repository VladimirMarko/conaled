import SquareKit.SplitSheafCoherence
import Examples.SheafSlices

/-! Experimental finite split-family consumers. A term is a natural section;
local inhabitants without compatible overlap data do not supply one. -/
noncomputable section
namespace Examples.SplitSheafFamilies
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies Examples.SheafFunctions

abbrev dependent := SplitSheaf.ofDisplay falsePoint
abbrev reversed := SplitSheaf.tySub dependent negation
abbrev Fiber (A : SplitSheaf.Ty D) (M : Diamond) (b : Bool) :=
  A.family.obj (D.obj.elementsMk (op M) b)

theorem false_fiber (M : Diamond) : Nonempty (Fiber dependent M false) := ⟨⟨(), rfl⟩⟩
theorem true_empty (M : Diamond) : IsEmpty (Fiber dependent M true) := ⟨fun a => Bool.noConfusion a.property⟩
theorem reversed_true (M : Diamond) : Nonempty (Fiber reversed M true) := ⟨⟨(), rfl⟩⟩
theorem reversed_false (M : Diamond) : IsEmpty (Fiber reversed M false) := ⟨fun a => Bool.noConfusion a.property⟩

/-- After restriction to the true point, the reversed family has a term. -/
def restrictedTerm : SplitSheaf.Tm (SplitSheaf.tySub reversed truePoint) where
  val _ := ⟨(), rfl⟩
  natural _ := Subtype.ext rfl

abbrev pairing := SplitSheaf.pair reversed truePoint restrictedTerm

theorem pairing_base : pairing ≫ SplitSheaf.p reversed = truePoint := SplitSheaf.pair_p _ _ _
theorem pairing_value : SplitSheaf.tmSub (SplitSheaf.q reversed) pairing = restrictedTerm := rfl

/-- Reconstructing the dependent value after pairing returns the original unit
section; this consumes the actual split/display comparison. -/
theorem pairing_reconstructed :
    pairing ≫ SplitSheaf.lift dependent negation ≫ (SplitSheaf.displayIso falsePoint).hom =
      𝟙 SheafImage.terminal := rfl

def repeatedTerm := SplitSheaf.tmSub (SplitSheaf.tmSub restrictedTerm base) negation

theorem repeated_composition : repeatedTerm = SplitSheaf.tmSub restrictedTerm (negation ≫ base) :=
  SplitSheaf.tmSub_comp restrictedTerm base negation

theorem repeated_pairing :
    SplitSheaf.pair (SplitSheaf.tySub reversed truePoint) (negation ≫ base) repeatedTerm =
      negation ≫ SplitSheaf.pair (SplitSheaf.tySub reversed truePoint) base
        (SplitSheaf.tmSub restrictedTerm base) := rfl

/-- Triple transport and actual chosen-pullback coherence both apply to this
inhabited restricted family. -/
abbrev repeated_transport := SplitSheaf.transport_triple restrictedTerm base negation negation
abbrev repeated_display := SplitSheaf.triple_composite (SplitSheaf.tySub reversed truePoint) base negation negation

theorem no_total_term : ¬ Nonempty (SplitSheaf.Tm dependent) := by
  rintro ⟨t⟩
  exact (true_empty X).false (t.val (D.obj.elementsMk (op X) true))

abbrev varying := SplitSheaf.ofDisplay SheafSlices.varyingDisplay

def varyingEquiv (M : Diamond) (b : Bool) : Fiber varying M b ≃ E.obj.obj (op M) :=
  SheafSlices.varyingEquiv M b

theorem varying_restrict {M N : Diamond} (f : N ⟶ M) (b : Bool) (a : Fiber varying M b) :
    varyingEquiv N b (varying.family.map (ElementFamilies.along D.obj f.op b) a) =
      E.obj.map f.op (varyingEquiv M b a) := rfl

theorem varying_wu (b : Bool) (a : Fiber varying U b) :
    varyingEquiv W b (varying.family.map (ElementFamilies.along D.obj (show W ⟶ U from Arrow.wu).op b) a) = false := rfl

theorem varying_wv (b : Bool) (a : Fiber varying V b) :
    varyingEquiv W b (varying.family.map (ElementFamilies.along D.obj (show W ⟶ V from Arrow.wv).op b) a) = true := rfl

theorem varying_empty (b : Bool) : IsEmpty (Fiber varying X b) := ⟨fun a => Empty.elim (varyingEquiv X b a)⟩
theorem varying_no_term : ¬ Nonempty (SplitSheaf.Tm varying) := by
  rintro ⟨t⟩
  exact (varying_empty false).false (t.val (D.obj.elementsMk (op X) false))

theorem varying_reconstruction (M : Diamondᵒᵖ) (a : (SplitSheaf.Ext varying).obj.obj M) :
    (SplitSheaf.displayIso SheafSlices.varyingDisplay).hom.hom.app M a = a.2.val := rfl

theorem varying_reconstruction_wu (a : (SplitSheaf.Ext varying).obj.obj (op U)) :
    ((SplitSheaf.displayIso SheafSlices.varyingDisplay).hom.hom.app (op W)
      ((SplitSheaf.Ext varying).obj.map (show W ⟶ U from Arrow.wu).op a)).1 = false := rfl

/-- Local inhabitants survive, but the actual sheaf condition still forbids
an incompatible family from supplying a section at X. -/
theorem varying_local (b : Bool) : Nonempty (Fiber varying U b) ∧ Nonempty (Fiber varying V b) :=
  SheafSlices.varying_local b

theorem varying_no_matching (b : Bool)
    (x : Presieve.FamilyOfElements (SplitSheaf.elementSheaf varying).obj (SheafSlices.liftedCover b).arrows) :
    ¬ x.Compatible := SheafSlices.varying_no_matching b x

/-- Compatible data still glue in the inhabited false fiber. -/
theorem false_matching :
    ∃ x : Presieve.FamilyOfElements (SplitSheaf.elementSheaf dependent).obj
      (SheafSlices.liftedCover false).arrows, x.Compatible ∧ ∃ a, x.IsAmalgamation a :=
  SheafSlices.false_matching

end Examples.SplitSheafFamilies
