import SquareKit.ExceptionalHomFamilies
import SquareKit.IndexedSumFamilies

/-! Selected dependent-pair evaluation and the exceptional-adjunction boundary. -/
set_option autoImplicit false
noncomputable section
namespace Examples.ExceptionalInternalHom
open CategoryTheory ExceptionalHomFamilies

/-- Both fibers are inhabited but they have different types. -/
def Coefficient : Bool → Type
  | false => Unit
  | true => Bool

/-- A function that observes both the base index and the selected fiber value. -/
def observe : Sigma Coefficient ⟶ Nat := ↾fun x => match x with
  | ⟨false, ()⟩ => 17
  | ⟨true, false⟩ => 23
  | ⟨true, true⟩ => 31

example : (((iso Coefficient).hom.app Nat observe) false).hom () = (17 : Nat) :=
  hom_apply Coefficient Nat observe false ()

example : (((iso Coefficient).hom.app Nat observe) true).hom false = (23 : Nat) :=
  hom_apply Coefficient Nat observe true false

example : (((iso Coefficient).hom.app Nat observe) true).hom true = (31 : Nat) :=
  hom_apply Coefficient Nat observe true true

/-- This is the existing selected-witness contract, not existential truth. -/
theorem selected_evaluation
    (s : SquareKit.IndexedSumFamilies.Selected (fun _ : Unit => Bool)
      (fun _ b => Coefficient b) ()) :
    (((iso Coefficient).hom.app Nat observe) s.1).hom s.2 = observe s :=
  hom_apply Coefficient Nat observe s.1 s.2

example : ((iso Coefficient).inv.app Nat ((iso Coefficient).hom.app Nat observe)) =
    observe := by
  exact congrArg (fun f => f.hom observe) ((iso Coefficient).hom_inv_id_app Nat)

example (k : ∀ b, Coefficient b ⟶ Nat) :
    ((iso Coefficient).inv.app Nat k).hom ⟨true, false⟩ = (k true).hom false :=
  inv_apply Coefficient Nat k true false

/-- The ordinary product cannot be substituted for the exceptional sum. -/
theorem no_product_exceptional : ¬ Nonempty (prod.{0} ⊣ pull.{0}) := by
  rintro ⟨adj⟩
  let A : Bool → Type := fun b => if b then Unit else Empty
  let h : prod.obj A ⟶ Empty := ↾fun x => (x false).elim
  have k := (adj.homEquiv A Empty) h
  exact (k true ()).elim

end Examples.ExceptionalInternalHom
