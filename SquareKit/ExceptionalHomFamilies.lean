import SquareKit.ExceptionalInternalHom
import Mathlib.CategoryTheory.Pi.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-! # Exceptional internal Hom for families over the terminal map

`Type u` represents families over the terminal base. Over `Bool`, use Mathlib's
pointwise category and its existing closed symmetric monoidal structure.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace CategoryTheory.ExceptionalHomFamilies

universe u

/-- Reindexing along `Bool → Unit`, with terminal families identified with sets. -/
def pull : Type u ⥤ (Bool → Type u) where
  obj B _ := B
  map h _ := h

/-- The exceptional direct image is the actual dependent sum. -/
def sum : (Bool → Type u) ⥤ Type u where
  obj A := Sigma A
  map h := ↾fun x => ⟨x.1, h x.1 x.2⟩

/-- The ordinary direct image is the actual dependent product. -/
def prod : (Bool → Type u) ⥤ Type u where
  obj A := ∀ b, A b
  map h := ↾fun x b => h b (x b)

/-- Dependent uncurrying and currying give the exceptional adjunction. -/
def exceptional : sum ⊣ pull := Adjunction.mkOfHomEquiv {
  homEquiv _A _B := {
    toFun h b := ↾fun a => h ⟨b, a⟩
    invFun k := ↾fun x => k x.1 x.2
    left_inv _ := rfl
    right_inv _ := rfl }
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

/-- Currying in the base index gives the ordinary adjunction. -/
def ordinary : pull ⊣ prod := Adjunction.mkOfHomEquiv {
  homEquiv _B _A := {
    toFun h := ↾fun t b => h b t
    invFun k b := ↾fun t => k t b
    left_inv _ := rfl
    right_inv _ := rfl }
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

/-- The sum PF retains the selected index and its dependent value. -/
noncomputable def projectionFormula : ExceptionalInternalHom.ProjectionFormula pull sum where
  iso A := NatIso.ofComponents (fun T => {
    hom := ↾fun x => (x.2.1, ⟨x.1, x.2.2⟩)
    inv := ↾fun x => ⟨x.2.1, (x.1, x.2.2)⟩ })
  naturality _ _ := rfl

/-- The generic local construction specialized to dependent sums and products. -/
noncomputable def iso (A : Bool → Type u) :=
  ExceptionalInternalHom.iso ordinary exceptional projectionFormula A

/-- The generic map evaluates a function at the actual selected dependent pair. -/
@[simp] theorem hom_apply (A : Bool → Type u) (B : Type u)
    (h : (ihom (sum.obj A)).obj B) (b : Bool) (a : A b) :
    (((iso A).hom.app B h) b).hom a = h.hom ⟨b, a⟩ := by
  have e := ExceptionalInternalHom.hom_eq_chain ordinary exceptional projectionFormula
    A B ((ihom (sum.obj A)).obj B) (𝟙 _)
  simp only [Category.id_comp] at e
  change (((ExceptionalInternalHom.iso ordinary exceptional projectionFormula A).hom.app B h) b).hom a = _
  rw [e]
  rfl

/-- The inverse reconstructs the function on the complete dependent pair. -/
@[simp] theorem inv_apply (A : Bool → Type u) (B : Type u)
    (k : ∀ b, A b ⟶ B) (b : Bool) (a : A b) :
    ((iso A).inv.app B k).hom ⟨b, a⟩ = (k b).hom a := by
  have e := congrArg (fun f => (f.hom k b).hom a) ((iso A).inv_hom_id_app B)
  change (((iso A).hom.app B ((iso A).inv.app B k)) b).hom a = (k b).hom a at e
  rw [hom_apply] at e
  exact e

end CategoryTheory.ExceptionalHomFamilies
