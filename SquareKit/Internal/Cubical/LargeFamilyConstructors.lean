import SquareKit.Internal.Cubical.LargeFamilyClassification
import Mathlib.Logic.Small.Basic

/-! Constructor closure at a fixed small fiber universe over a larger context.
Smallness of dependent functions is established using represented restrictions;
it is not inferred from smallness of the context. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse
open CategoryTheory
universe u
namespace SmallPresentation.Data
variable {Ξ : Context.{u+1}} {A : Family Ξ} {B : Family (total A)}

noncomputable def ofSmall (C : Family Ξ) [∀ x, Small.{u} (C.obj x)] : SmallPresentation.Data C where
  fiber x := Shrink.{u} (C.obj x)
  equiv x := (equivShrink (C.obj x)).symm

def sigma (P : SmallPresentation.Data A) (Q : SmallPresentation.Data B) :
    SmallPresentation.Data (Presheaf.sigma A B) where
  fiber x := Σ a : P.fiber x, Q.fiber (extendObj A x (P.equiv x a))
  equiv x := Equiv.sigmaCongr (P.equiv x) (fun a => Q.equiv (extendObj A x (P.equiv x a)))

/-- Only cube restrictions and small arguments index this function space. -/
def FunctionValues (P : SmallPresentation.Data A) (Q : SmallPresentation.Data B)
    (x : Ξ.Elements) : Type u :=
  ∀ (J : Cubeᵒᵖ) (f : x.obj ⟶ J) (a : P.fiber (Ξ.elementsMk J (Ξ.map f x.val))),
    Q.fiber (extendObj A (Ξ.elementsMk J (Ξ.map f x.val))
      (P.equiv (Ξ.elementsMk J (Ξ.map f x.val)) a))

def functionValues (P : SmallPresentation.Data A) (Q : SmallPresentation.Data B)
    (x : Ξ.Elements) (p : PiElement A B x) : P.FunctionValues Q x :=
  fun _J f a => (Q.equiv _).symm (p.val (Functor.Elements.homMk f rfl) (P.equiv _ a))

theorem functionValues_injective (P : SmallPresentation.Data A) (Q : SmallPresentation.Data B)
    (x : Ξ.Elements) : Function.Injective (P.functionValues Q x) := by
  intro p q h
  apply PiElement.ext
  intro y f a
  rcases y with @⟨J,y⟩
  rcases f with ⟨f,hf⟩
  change x.obj ⟶ J at f
  change Ξ.map f x.val = y at hf
  subst y
  obtain ⟨a, rfl⟩ := (P.equiv _).surjective a
  have hv := congrFun (congrFun (congrFun h J) f) a
  exact (Q.equiv _).symm.injective hv

noncomputable def pi (P : SmallPresentation.Data A) (Q : SmallPresentation.Data B) :
    SmallPresentation.Data (Presheaf.pi A B) := by
  letI : ∀ x, Small.{u} ((Presheaf.pi A B).obj x) :=
    fun x => small_of_injective (P.functionValues_injective Q x)
  exact ofSmall _

def interval (Ξ : Context.{u+1}) : SmallPresentation.Data (Presheaf.interval Ξ) where
  fiber x := ULift.{u} (Cube.Hom x.obj.unop ⟨1⟩)
  equiv _ := Equiv.ulift.trans Equiv.ulift.symm

noncomputable def path (B : Family (total (Presheaf.interval Ξ))) (Q : SmallPresentation.Data B)
    (a₀ : Term (reindex B (endpointSub Ξ false)))
    (a₁ : Term (reindex B (endpointSub Ξ true))) : SmallPresentation.Data (Presheaf.path B a₀ a₁) := by
  let P := (interval Ξ).pi Q
  letI : ∀ x, Small.{u} (PiElement (Presheaf.interval Ξ) B x) :=
    fun x => Small.mk' (P.equiv x).symm
  letI : ∀ x, Small.{u} ((Presheaf.path B a₀ a₁).obj x) :=
    fun _ => small_of_injective Subtype.val_injective
  exact ofSmall _

end SmallPresentation.Data

/-- The existing universal decoder has explicitly small fibers. -/
def decodePresentation {Ξ : Context.{u+1}} (a : Ξ ⟶ smallFamilyCodes.{u}) : SmallPresentation.Data (liftedDecode a) where
  fiber x := (decode a).obj x
  equiv _ := Equiv.ulift.symm

namespace LargeConstructors
variable {Ξ : Context.{u+1}}

/-- Constructor output includes its actual decoder and chosen lawful filler. -/
structure Result (C : Family Ξ) where
  code : Ξ ⟶ smallFamilyCodes.{u}
  decoding : liftedDecode code ≅ C
  filling : Filling (liftedDecode code)
  lawful : filling.Lawful

noncomputable def construct {C : Family Ξ} (P : SmallPresentation.Data C)
    (F : Filling C) (hF : F.Lawful) : Result C where
  code := P.code F hF
  decoding := P.nativeIso F hF
  filling := F.transport (P.nativeIso F hF).symm
  lawful := F.transport_lawful _ hF

noncomputable def sigma (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) :
    Result (Presheaf.sigma (liftedDecode a) (liftedDecode b)) :=
  construct ((decodePresentation a).sigma (decodePresentation b))
    (sigmaFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
    (sigmaFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) (NativeDecode.filling_lawful b))

noncomputable def pi (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) :
    Result (Presheaf.pi (liftedDecode a) (liftedDecode b)) :=
  construct ((decodePresentation a).pi (decodePresentation b))
    (piFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
    (piFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) (NativeDecode.filling_lawful b))

noncomputable def path (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true))) :
    Result (Presheaf.path (liftedDecode b) a₀ a₁) :=
  construct (SmallPresentation.Data.path _ (decodePresentation b) a₀ a₁)
    (pathFilling (NativeDecode.filling b) (NativeDecode.filling_lawful b) a₀ a₁)
    (pathFilling_lawful (NativeDecode.filling b) (NativeDecode.filling_lawful b) a₀ a₁)

end LargeConstructors
end SquareKit.Cubical.Presheaf.SmallUniverse
