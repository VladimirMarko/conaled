import SquareKit.Internal.Cubical.NativeStructureDescriptions
import SquareKit.Internal.Cubical.CartesianNativeStructureDescriptions

/-! Native descriptions at universal and presented carriers in both cubical models.
The higher-order example applies a native function to another native function. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeStructureDescriptions
open CategoryTheory SquareKit.StructureIdentity

def pointedUnary : Description := .product .carrier (.function .carrier .carrier)
def higher : Description := .function (.function .carrier .carrier) .carrier

namespace Presheaf
open SquareKit.Cubical.Presheaf
open StructureIdentity.Native
universe u

noncomputable def genericPointed : SmallUniverse.LargeConstructors.Result
    (family pointedUnary (SmallUniverse.liftedDecode (𝟙 smallFamilyCodes.{0}))) :=
  universal pointedUnary
noncomputable def genericHigher := universal higher
noncomputable def totalStructures (Γ : Context.{1}) := objects pointedUnary Γ
example (Γ : Context.{1}) : (objectsFilling pointedUnary Γ).1.Lawful :=
  (objectsFilling pointedUnary Γ).2

variable {Γ : Context.{1}}
abbrev boolCarrier : Family Γ := constantFamily Γ (ULift.{1} Bool)
def pointedPresentation : family pointedUnary (boolCarrier (Γ := Γ)) ≅
    constantFamily Γ (ULift.{1} (pointedUnary.Data Bool)) := presentedIso pointedUnary (Iso.refl _)
def selected : Term (family pointedUnary (boolCarrier (Γ := Γ))) :=
  Term.map pointedPresentation.inv ⟨fun _ => ⟨(false, Bool.not)⟩, fun _ => rfl⟩

/-- This evaluates the native Pi field, not just its host readout. -/
example (x : Γ.Elements) : ((selected.val x).2.val (𝟙 x) (ULift.up false)).down = true := rfl
example (x : Γ.Elements) : (selected.val x).1.down = false := rfl

theorem read_selected : Term.map pointedPresentation.hom (selected (Γ := Γ)) =
    ⟨fun _ => ⟨(false, Bool.not)⟩, fun _ => rfl⟩ := by
  apply Term.ext
  intro x
  exact congrArg (fun k => k.app x (ULift.up (false, Bool.not) : ULift.{1} (pointedUnary.Data Bool)))
    pointedPresentation.inv_hom_id

/-- The function domain itself contains a function, testing negative occurrences. -/
def higherElement (x : Γ.Elements) : (family higher (boolCarrier (Γ := Γ))).obj x :=
  (presentedIso higher (Iso.refl (boolCarrier (Γ := Γ)))).inv.app x ⟨fun g => g false⟩
def nativeNegation (x : Γ.Elements) : (family (.function .carrier .carrier) (boolCarrier (Γ := Γ))).obj x :=
  (functionEquiv (Iso.refl (boolCarrier (Γ := Γ))) (Iso.refl _) x).symm (fun b => ⟨!b.down⟩)
example (x : Γ.Elements) : ((higherElement x).val (𝟙 x) (nativeNegation x)).down = true := rfl

/-- Every original host description is recovered on presented carriers. -/
def recover (D : Description.{u}) {Δ : Context.{u+1}} {A : Family Δ} {X : Type u}
    (i : A ≅ constantFamily Δ (ULift.{u+1} X)) :
    family D A ≅ constantFamily Δ (ULift.{u+1} (D.Data X)) := presentedIso D i

/-- A lawful structure family need not have any inhabitants. -/
example (Γ : Context.{1}) (x : Γ.Elements) :
    IsEmpty ((objects (.product .carrier (.fixed Empty)) Γ).obj x) :=
  ⟨fun z => Empty.elim z.2.2.down⟩

end Presheaf

namespace Cartesian
open SquareKit.Cubical.Cartesian
open StructureIdentity.Native
universe u

noncomputable def genericPointed : SmallUniverse.LargeConstructors.Result
    (family pointedUnary (SmallUniverse.liftedDecode (𝟙 smallFamilyCodes.{0}))) :=
  universal pointedUnary
noncomputable def genericHigher := universal higher
noncomputable def totalStructures (Γ : Context.{1}) := objects pointedUnary Γ
example (Γ : Context.{1}) : (objectsFilling pointedUnary Γ).1.Lawful :=
  (objectsFilling pointedUnary Γ).2

variable {Γ : Context.{1}}
abbrev boolCarrier : Family Γ := constantFamily Γ (ULift.{1} Bool)
def pointedPresentation : family pointedUnary (boolCarrier (Γ := Γ)) ≅
    constantFamily Γ (ULift.{1} (pointedUnary.Data Bool)) := presentedIso pointedUnary (Iso.refl _)
def selected : Term (family pointedUnary (boolCarrier (Γ := Γ))) :=
  Term.map pointedPresentation.inv ⟨fun _ => ⟨(false, Bool.not)⟩, fun _ => rfl⟩

/-- This evaluates the native Pi field, not just its host readout. -/
example (x : Γ.Elements) : ((selected.val x).2.val (𝟙 x) (ULift.up false)).down = true := rfl
example (x : Γ.Elements) : (selected.val x).1.down = false := rfl

theorem read_selected : Term.map pointedPresentation.hom (selected (Γ := Γ)) =
    ⟨fun _ => ⟨(false, Bool.not)⟩, fun _ => rfl⟩ := by
  apply Term.ext
  intro x
  exact congrArg (fun k => k.app x (ULift.up (false, Bool.not) : ULift.{1} (pointedUnary.Data Bool)))
    pointedPresentation.inv_hom_id

/-- The function domain itself contains a function, testing negative occurrences. -/
def higherElement (x : Γ.Elements) : (family higher (boolCarrier (Γ := Γ))).obj x :=
  (presentedIso higher (Iso.refl (boolCarrier (Γ := Γ)))).inv.app x ⟨fun g => g false⟩
def nativeNegation (x : Γ.Elements) : (family (.function .carrier .carrier) (boolCarrier (Γ := Γ))).obj x :=
  (functionEquiv (Iso.refl (boolCarrier (Γ := Γ))) (Iso.refl _) x).symm (fun b => ⟨!b.down⟩)
example (x : Γ.Elements) : ((higherElement x).val (𝟙 x) (nativeNegation x)).down = true := rfl

/-- Every original host description is recovered on presented carriers. -/
def recover (D : Description.{u}) {Δ : Context.{u+1}} {A : Family Δ} {X : Type u}
    (i : A ≅ constantFamily Δ (ULift.{u+1} X)) :
    family D A ≅ constantFamily Δ (ULift.{u+1} (D.Data X)) := presentedIso D i

example (Γ : Context.{1}) (x : Γ.Elements) :
    IsEmpty ((objects (.product .carrier (.fixed Empty)) Γ).obj x) :=
  ⟨fun z => Empty.elim z.2.2.down⟩

end Cartesian

end Examples.NativeStructureDescriptions
