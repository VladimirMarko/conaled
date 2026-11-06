import SquareKit.Internal.PathTransport.TwoFamilyModelData
import Examples.TwoFamilySigmaProjection

/-! The admitted model families include the existing integer-cell example. -/
namespace Examples.TwoFamilyModelData
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
open HigherInterpretation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g,h,k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g,h,k⟩⟩

def integerContext : Context where
  carrier := B
  bicategory := inferInstance
  strict := inferInstance
  groupoid := inferInstance
  locallyGroupoid := inferInstance

def integers : Family integerContext := Family.constant integerContext integerContext

theorem existing_integer_family : integers.data = integerFamily :=
  StrictTwoTransformation.functor_ext rfl

def later : Family integers.total := integers.reindex (TwoFamily.projectionHigher integers.data)

theorem existing_dependent_pair : (integers.sigma later).data =
    TwoFamily.sigmaFamily integerFamily laterFamily := by
  rfl

open Examples.TwoFamilySigmaProjection
example : totalCell 0 0 1 ≠ totalCell 0 0 0 := by
  intro h
  have hh := congr_arg_heq (fun α => α.fiber.fiber) h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 := eq_of_heq hh
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)

example (Γ Δ Θ : Context) (A : Family Γ)
    (σ : StrictPseudofunctor Δ Γ) (τ : StrictPseudofunctor Θ Δ) :
    (A.reindex σ).reindex τ = A.reindex (τ.comp σ) := Family.reindex_comp A σ τ
end Examples.TwoFamilyModelData
