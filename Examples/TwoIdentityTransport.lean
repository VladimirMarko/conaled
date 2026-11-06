import SquareKit.Internal.PathTransport.TwoIdentityTransport
import SquareKit.DoubleDelooping
import Mathlib.Algebra.Group.Int.Defs

/-! Identity transport retains genuine fiber 2-cells and the difference
between two endpoint comparison cells. -/
namespace Examples.TwoIdentityTransport
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
abbrev B := DoubleDelooping.Space (Multiplicative ℤ)
abbrev point : B := DoubleDelooping.point _
abbrev arrow : point ⟶ point := DoubleDelooping.arrow _

local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩

/-- Transport through identity endpoints still maps the original integer cell. -/
theorem retains_fiber_cell (n : ℤ) :
    (TwoIdentityTransport.homTransport (StrictPseudofunctor.id B) (a := point) (a' := point) arrow arrow).map (X := arrow) (Y := arrow)
      (Multiplicative.ofAdd n : arrow ⟶ arrow) = Multiplicative.ofAdd n := rfl

noncomputable def comparison (m n : ℤ) :=
  TwoIdentityTransport.homComparison
    (StrictTwoTransformation.Trans.id (StrictPseudofunctor.id B))
    (u := arrow) (u' := arrow) (v := arrow) (v' := arrow)
    (Multiplicative.ofAdd m) (Multiplicative.ofAdd n)

/-- Changing endpoint comparison cells is observable in the identity fiber. -/
theorem comparison_integer (m n : ℤ) :
    (comparison m n).app arrow = Multiplicative.ofAdd (n - m) := by
  simp [comparison, TwoIdentityTransport.homComparison, TwoIdentityTransport.inverseMate,
    TwoIdentityTransport.homNaturality, StrictTwoTransformation.Trans.id,
    ← Groupoid.inv_eq_inv, SingleObj.comp_as_mul, SingleObj.id_as_one,
    DoubleDelooping.instBicategorySpace]
  simp only [Bicategory.whiskerLeft, Bicategory.whiskerRight, Bicategory.associator,
    Iso.refl_hom, Iso.refl_inv]
  simp only [CategoryStruct.comp, CategoryStruct.id, Groupoid.inv, one_mul, mul_one]
  change (Multiplicative.ofAdd m)⁻¹ * Multiplicative.ofAdd n = _
  simp [div_eq_mul_inv, mul_comm]

/-- Embedding the identity fiber does not erase its integer comparison arrow. -/
theorem embedded_comparison (m n : ℤ) :
    ((TwoIdentityTransport.locallyDiscreteTrans (comparison m n)).app ⟨arrow⟩).as =
      Multiplicative.ofAdd (n - m) := comparison_integer m n

/-- The general mate-pasting law applies to arbitrary integer endpoint cells. -/
theorem inverse_mate_pasting (m n : ℤ) :
    TwoIdentityTransport.inverseMate (u := arrow) (u' := arrow) (h := arrow)
      ((Multiplicative.ofAdd m : arrow ⟶ arrow) ≫
        Bicategory.whiskerLeft arrow (g := arrow) (h := arrow ≫ arrow)
          (Multiplicative.ofAdd n) ≫
        eqToHom (Category.assoc arrow arrow arrow).symm) =
      eqToHom (Category.assoc (inv arrow) arrow arrow).symm ≫
        TwoIdentityTransport.inverseMate (u := arrow) (u' := arrow) (h := arrow)
          (Multiplicative.ofAdd m) ▷ arrow ≫
        TwoIdentityTransport.inverseMate (u := arrow) (u' := arrow) (h := arrow)
          (Multiplicative.ofAdd n) :=
  TwoIdentityTransport.inverseMate_comp _ _

/-- Two successive integer hom transports agree as whole functors. -/
theorem transport_composes :
    TwoIdentityTransport.homTransport
      ((StrictPseudofunctor.id B).comp (StrictPseudofunctor.id B))
      (a := point) (a' := point) (b := point) (b' := point)
      (arrow ≫ arrow) (arrow ≫ arrow) =
    TwoIdentityTransport.homTransport (StrictPseudofunctor.id B)
      (a := point) (a' := point) arrow arrow ⋙
    TwoIdentityTransport.homTransport (StrictPseudofunctor.id B)
      (a := point) (a' := point) arrow arrow :=
  TwoIdentityTransport.homTransport_comp (StrictPseudofunctor.id B)
    (StrictPseudofunctor.id B) (a := point) (a' := point)
    (b := point) (b' := point) arrow arrow arrow arrow

end Examples.TwoIdentityTransport
