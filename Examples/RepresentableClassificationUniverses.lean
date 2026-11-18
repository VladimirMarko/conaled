import SquareKit.Internal.PresheafFamilyClassification

/-! Independent large object/hom universes, including a base whose objects are
all types in Type 1 and whose morphisms themselves live in Type 1. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.RepresentableClassificationUniverses
open CategoryTheory SquareKit.RepresentableClassification
universe v w u

example {C : Type v} [Category.{w} C] (Γ : Context.{u} C) (A : Family Γ) :
    PresheafFamily.system.decode PresheafFamily.universalDecode
      (PresheafFamily.system.code A) ≅ A := PresheafFamily.recovery A

abbrev Large := ULift.{1} Bool

def flip : Large ⟶ Large := TypeCat.ofHom (fun x => ⟨!x.down⟩)

example : (representableMap (C := Type 1) flip).app (Opposite.op Large) ⟨𝟙 Large⟩ = ⟨flip⟩ := rfl
example : flip (⟨false⟩ : Large) = ⟨true⟩ := rfl

/-- This instance requires object universe 2 and morphism/fiber universe 1. -/
example (A : Family (representable.{0} Large)) :
    PresheafFamily.system.decode PresheafFamily.universalDecode
      (PresheafFamily.system.code A) ≅ A := PresheafFamily.recovery A

end Examples.RepresentableClassificationUniverses
