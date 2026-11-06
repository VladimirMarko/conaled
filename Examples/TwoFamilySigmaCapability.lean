import SquareKit.Internal.PathTransport.TwoFamilySigmaCapability
import Examples.TwoFamilyStructuralModel
import Examples.TwoFamilySigmaProjection
/-! Source dependent-pair elimination and reconstruction retain higher witnesses. -/
noncomputable section
namespace Examples.TwoFamilySigmaCapability
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoFamilyStructuralModel
open Examples.TwoFamilySigmaProjection
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
abbrev sums := sigmaCapability integerContext integerContext

example (E : model.Family (model.extend integerContext (sums.sigma integers later)))
    (d : model.Section (model.extend integers.total later)
      (model.subTy E (sums.pack integers later))) :
    HEq (model.subTm (sums.split integers later E d) (sums.pack integers later)) d :=
  sums.split_beta integers later E d

theorem retains_selected_cell (k m n : ℤ) :
    HEq (((model.compSub (sums.pack integers later) (sums.unpack integers later)).down.map₂
      (totalCell k m n)).fiber.fiber) (Multiplicative.ofAdd n) := by
  exact congr_arg_heq (fun f => (f.down.map₂ (totalCell k m n)).fiber.fiber)
    (sums.pack_unpack integers later)

example : (model.compSub (sums.pack integers later) (sums.unpack integers later)).down.map₂
    (totalCell 0 0 1) ≠
    (model.compSub (sums.pack integers later) (sums.unpack integers later)).down.map₂
    (totalCell 0 0 0) := by
  intro h
  have hh := congr_arg_heq (fun α => α.fiber.fiber) h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 :=
    eq_of_heq ((retains_selected_cell 0 0 1).symm.trans (hh.trans (retains_selected_cell 0 0 0)))
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)
end Examples.TwoFamilySigmaCapability
