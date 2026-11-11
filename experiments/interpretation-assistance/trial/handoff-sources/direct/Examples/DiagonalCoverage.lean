import SquareKit.DiagonalCoverage
import Examples.DiagonalConstruction

namespace Examples.DiagonalCoverage
open SquareKit.DiagonalConstruction
open Examples.DiagonalConstruction

/-- The unchanged omitted-code counterexample rejects the new certificate. -/
theorem omitted_extension_rejected : ¬ partialPresentation.Extension sourceSelected := by
  intro extra
  exact cannot_transfer_representation (partialPresentation.selectedExtension sourceSelected extra).represents

/-- Restriction is useful even when extension to all target inputs is false. -/
def restricted := partialPresentation.selectedImage sourceSelected
example : restricted.witness = true := rfl
example : restricted.code.val = false := rfl

/-- Extra codes need not obstruct representation when their rows agree. -/
def good : Map (fun _ _ : Unit => true) id (fun _ _ : Bool => true) id where
  code _ := false
  value := id
  evaluation _ _ := rfl
  step _ := rfl

theorem good_extra : good.Extension sourceSelected := fun _ _ => rfl
example : ¬ Function.Surjective good.code := by
  intro h
  obtain ⟨a, ha⟩ := h true
  contradiction
example : (good.selectedExtension sourceSelected good_extra).witness = true :=
  good.extension_witness sourceSelected good_extra

def larger : Map (fun _ _ : Bool => true) id (fun _ _ : Option Bool => true) id where
  code := some
  value := id
  evaluation _ _ := rfl
  step _ := rfl

theorem larger_extra : larger.Extension (good.selectedExtension sourceSelected good_extra) :=
  fun _ _ => rfl
example : (larger.comp good).Extension sourceSelected :=
  Map.extension_comp good larger sourceSelected good_extra larger_extra
example : ((larger.comp good).selectedExtension sourceSelected
    (Map.extension_comp good larger sourceSelected good_extra larger_extra)).code = some false := rfl

/-- A selected fixed value does not supply all-input diagonal representation.
The evaluator and step remain unchanged throughout this separating case. -/
def xorEval (a b : Bool) : Bool := xor a b
example : id (xorEval false false) = xorEval false false := rfl

theorem no_xor_representation : IsEmpty (Selected xorEval id) := by
  constructor
  intro s
  have hf := s.represents false
  have ht := s.represents true
  cases hc : s.code <;> simp [diagonal, xorEval, hc] at hf ht

end Examples.DiagonalCoverage
