import SquareKit.AdjointModes.Resources
import SquareKit.AdjointComparison
import Mathlib.CategoryTheory.Types.Basic

/-! The small shift model exposes an ordinary Mathlib adjunction, allowing the
existing right-adjoint comparison machinery to be used without imposing a
maximal logic interface on resource clients. -/
namespace SquareKit.AdjointModes
open CategoryTheory

instance : Category Resource where
  Hom := Map
  id := Map.identity
  comp f g := g.comp f
  id_comp f := Map.comp_identity f
  comp_id f := Map.identity_comp f
  assoc f g h := (Map.comp_assoc h g f).symm

def downFunctor : Type ⥤ Resource where
  obj := down
  map f := downMap f

def upFunctor : Resource ⥤ Type where
  obj := up
  map f := TypeCat.ofHom (upMap f)

def shift : downFunctor ⊣ upFunctor := Adjunction.mkOfHomEquiv
  { homEquiv := fun X A => (shiftAdjunction X A).trans TypeCat.homEquiv.symm
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl }

/-- Existing comparison laws apply to any other chosen right adjoint. -/
theorem compare_right_adjoint {R : Resource ⥤ Type} (b : downFunctor ⊣ R)
    {X : Type} {A : Resource} (f : downFunctor.obj X ⟶ A) :
    shift.homEquiv X A f ≫ (shift.rightAdjointUniq b).hom.app A = b.homEquiv X A f :=
  SquareKit.AdjointComparison.curry shift b f

end SquareKit.AdjointModes
