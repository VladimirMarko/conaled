import SquareKit.SliceDependentProduct
import SquareKit.AdjointComparison
import Examples.TerminalProducts

/-! Experimental native Type consumer of the same generic slice construction.
The terminal slice's closure is transported from Type, and canonical uniqueness
recovers the previously checked dependent-function operations. -/
noncomputable section
namespace Examples.NativeSliceProducts
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SquareKit
open Examples.TerminalProducts.Native

abbrev unit : Type := MonoidalCategory.tensorUnit Type
local instance : CartesianMonoidalCategory (Over unit) := Over.cartesianMonoidalCategory unit
local instance : MonoidalClosed (Over unit) :=
  cartesianClosedOfEquiv (equivToOverUnit Type).symm

local instance : Closed (Over.mk (toUnit Nat)) :=
  (inferInstance : MonoidalClosed (Over unit)).closed _

abbrev newPi := SliceDependentProduct.pi (toUnit Nat)
abbrev adjunction := SliceDependentProduct.adjunction (toUnit Nat)

def comparison : newPi ≅ TerminalProduct.pi Nat :=
  adjunction.rightAdjointUniq (TerminalProduct.adjunction Nat)

abbrev input := TypeTerminalProduct.family values
abbrev result := (newPi.obj input).left

def valuesEquiv : result ≃ TypeTerminalProduct.object values :=
  ((Over.forget unit).mapIso (comparison.app input)).toEquiv

def last : result := valuesEquiv.symm Examples.TerminalProducts.Native.last

/-- The new construction recovers the existing source-native dependent lambda. -/
theorem last_native :
    TypeTerminalProduct.piTyEquiv values (valuesEquiv last) = DependentSquares.lam body PUnit.unit := by
  rw [last, Equiv.apply_symm_apply]
  exact Examples.TerminalProducts.Native.last_native

theorem last_component (n : Nat) :
    (TypeTerminalProduct.evaluate values (valuesEquiv last) n).val = n := by
  rw [last, Equiv.apply_symm_apply]
  exact Examples.TerminalProducts.Native.last_component n

/-- All transposes, not just the selected lambda, commute with the comparison. -/
theorem curry_compare {X : Over unit}
    (k : (Over.pullback (toUnit Nat)).obj X ⟶ input) :
    adjunction.homEquiv X input k ≫ comparison.hom.app input =
      (TerminalProduct.adjunction Nat).homEquiv X input k :=
  AdjointComparison.curry adjunction (TerminalProduct.adjunction Nat) k

/-- The actual dependent evaluation is transported by the same comparison. -/
theorem counit_compare :
    (Over.pullback (toUnit Nat)).map (comparison.hom.app input) ≫
      (TerminalProduct.adjunction Nat).counit.app input = adjunction.counit.app input :=
  Adjunction.rightAdjointUniq_hom_app_counit adjunction (TerminalProduct.adjunction Nat) input

end Examples.NativeSliceProducts
