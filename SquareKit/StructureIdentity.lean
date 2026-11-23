import SquareKit.StructureIdentity.Laws

/-! Equivariant set-level structures used by the native family realizations.
Description and law syntax construct these data; callers need not prove a
structure identity principle.

The description grammar covers carrier occurrences, fixed types, products and
function types. The law grammar adds equations, proposition-valued relations,
conjunction, implication and universal quantification. Specifications currently
use small Lean types; descriptions and their transport are universe-polymorphic.
Preparing a specification requires writing its data shape and law syntax.
Preservation, law invariance and transport of formula solutions are then derived.
Direct functions and existing mathematical records remain usable through adapters.

The earlier realization in Internal.Cubical.StructureIdentity treats presented
discrete carriers and a supplied equivalence, with exact recovery of native path
sections. NativeStructureUaComparison and its Cartesian counterpart provide the
total internal correspondence for the admitted grammar using each model's own
univalence. They retain whole native recovery homotopies and law-bearing objects.
Presented-model comparisons do not identify independently selected ua paths.
No author-productivity or executable-transport claim follows from these proofs. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.StructureIdentity
universe u

structure Transport where
  Data : Type u → Type u
  map : {X Y : Type u} → (X ≃ Y) → (Data X ≃ Data Y)
  map_refl : ∀ X, map (Equiv.refl X) = Equiv.refl _
  map_trans : ∀ {X Y Z} (e : X ≃ Y) (f : Y ≃ Z), map (e.trans f) = (map e).trans (map f)

def Description.toTransport (D : Description.{u}) : Transport.{u} where
  Data := D.Data
  map := D.transport
  map_refl _ := D.transport_refl
  map_trans := D.transport_trans

def Specification.toTransport (T : Specification) : Transport.{0} where
  Data := T.Model
  map := T.transport
  map_refl _ := Equiv.ext T.transport_refl
  map_trans e f := Equiv.ext (T.transport_trans e f)

namespace Transport
theorem map_symm (F : Transport.{u}) {X Y : Type u} (e : X ≃ Y) :
    F.map e.symm = (F.map e).symm := by
  apply Equiv.ext
  intro x
  apply (F.map e).injective
  rw [Equiv.apply_symm_apply]
  have h := congrArg (fun k => k x) (F.map_trans e.symm e).symm
  simpa only [Equiv.symm_trans_self, F.map_refl, Equiv.refl_apply, Equiv.trans_apply] using h

structure Iso (F : Transport.{u}) {X Y : Type u} (s : F.Data X) (t : F.Data Y) where
  carrier : X ≃ Y
  preserves : F.map carrier s = t

def Iso.refl {F : Transport.{u}} {X : Type u} (s : F.Data X) : F.Iso s s :=
  ⟨Equiv.refl _, by rw [F.map_refl]; rfl⟩

def Iso.trans {F : Transport.{u}} {X Y Z : Type u} {s : F.Data X}
    {t : F.Data Y} {r : F.Data Z} (e : F.Iso s t) (f : F.Iso t r) : F.Iso s r :=
  ⟨e.carrier.trans f.carrier, by
    rw [F.map_trans]
    exact (congrArg (F.map f.carrier) e.preserves).trans f.preserves⟩

def Iso.symm {F : Transport.{u}} {X Y : Type u} {s : F.Data X}
    {t : F.Data Y} (e : F.Iso s t) : F.Iso t s :=
  ⟨e.carrier.symm, by
    rw [F.map_symm]
    exact (congrArg (F.map e.carrier).symm e.preserves.symm).trans
      ((F.map e.carrier).symm_apply_apply s)⟩

end Transport
end SquareKit.StructureIdentity
