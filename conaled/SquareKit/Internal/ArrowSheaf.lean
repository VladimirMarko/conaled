import SquareKit.Internal.ArrowPresheafPushout
import SquareKit.Internal.ArrowPushoutChange
import SquareKit.Internal.ArrowTransport
import SquareKit.SheafCartesianClosed
import Mathlib.CategoryTheory.Subobject.MonoOver

/-! The pushout interpretation is left exact for a subterminal sheaf.
The proof passes through presheaves and the left exact sheafification functor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowSheaf
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Sheaf J (Type (max u v)))

/-- Reflect the presheaf construction and use the sheafification counit. -/
def comparison : (sheafToPresheaf J (Type (max u v))).mapArrow ⋙ (ArrowPushout.interpretation P.obj ⋙ (presheafToSheaf J (Type (max u v)))) ≅
    ArrowPushout.interpretation P :=
  isoWhiskerLeft (sheafToPresheaf J (Type (max u v))).mapArrow (ArrowPushout.changeCategory (presheafToSheaf J (Type (max u v))) P.obj) ≪≫
    (Functor.associator (sheafToPresheaf J (Type (max u v))).mapArrow (presheafToSheaf J (Type (max u v))).mapArrow
      (ArrowPushout.interpretation ((presheafToSheaf J (Type (max u v))).obj P.obj))).symm ≪≫
    isoWhiskerRight ((Functor.mapArrowFunctor (Sheaf J (Type (max u v))) (Sheaf J (Type (max u v)))).mapIso
      (sheafificationNatIso J (Type (max u v))).symm)
      (ArrowPushout.interpretation ((presheafToSheaf J (Type (max u v))).obj P.obj)) ≪≫
    Functor.leftUnitor (ArrowPushout.interpretation ((presheafToSheaf J (Type (max u v))).obj P.obj)) ≪≫
    ArrowPushout.changeParameterIso _ (sheafificationIso P).symm

/-- Subterminal sections suffice for left exactness; no global complement is used. -/
instance [∀ X, Subsingleton (P.obj.obj X)] :
    PreservesFiniteLimits (ArrowPushout.interpretation P) := by
  let : PreservesFiniteLimits (sheafToPresheaf J (Type (max u v))).mapArrow := inferInstance
  exact preservesFiniteLimits_of_natIso (comparison J P)

/-- A subterminal sheaf determines an actual geometric morphism to the arrow category. -/
def geometric [∀ X, Subsingleton (P.obj.obj X)] : GeometricMorphism (Sheaf J (Type (max u v))) (Arrow (Sheaf J (Type (max u v)))) := by
  letI : Closed P := SquareKit.SheafCartesianClosed.closed P
  exact {
    inverseImage := ArrowPushout.interpretation P
    directImage := ArrowPushout.rightAdjoint P
    adjunction := ArrowPushout.adjunction P
    leftExact := inferInstance }

/-- An actual subterminal sheaf has subsingleton sections at every stage. -/
instance subterminalSections (Q : MonoOver (⊤_ (Sheaf J (Type (max u v))))) (X : Cᵒᵖ) :
    Subsingleton (Q.obj.left.obj.obj X) := by
  let E := sheafToPresheaf J (Type (max u v)) ⋙
    (evaluation Cᵒᵖ (Type (max u v))).obj X
  have ht := terminalIsTerminal.isTerminalObj E (⊤_ (Sheaf J (Type (max u v))))
  have hm : Mono (E.map Q.arrow) := inferInstance
  refine ⟨fun x y => ?_⟩
  apply (CategoryTheory.mono_iff_injective (E.map Q.arrow)).mp hm
  exact types_congr_hom (ht.hom_ext
    (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} => E.map Q.arrow x))
    (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} => E.map Q.arrow y))) PUnit.unit

/-- Every actual subterminal supplies the constructed geometric morphism. -/
def ofSubterminal (Q : MonoOver (⊤_ (Sheaf J (Type (max u v))))) :
    GeometricMorphism (Sheaf J (Type (max u v))) (Arrow (Sheaf J (Type (max u v)))) :=
  geometric J Q.obj.left

end SquareKit.Internal.ArrowSheaf

