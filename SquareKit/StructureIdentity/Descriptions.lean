import Mathlib.Logic.Equiv.Basic

/-! Descriptions of set-level data and their structure-preserving equivalences.
Function inputs transport backwards; outputs transport forwards. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.StructureIdentity

universe u

inductive Description : Type (u + 1)
  | carrier
  | fixed (A : Type u)
  | product (D E : Description)
  | function (D E : Description)

namespace Description

def Data : Description.{u} → Type u → Type u
  | .carrier, X => X
  | .fixed A, _ => A
  | .product D E, X => D.Data X × E.Data X
  | .function D E, X => D.Data X → E.Data X

def transport (D : Description.{u}) {X Y : Type u} (e : X ≃ Y) :
    D.Data X ≃ D.Data Y :=
  match D with
  | .carrier => e
  | .fixed _ => Equiv.refl _
  | .product D E => Equiv.prodCongr (D.transport e) (E.transport e)
  | .function D E => Equiv.arrowCongr (D.transport e) (E.transport e)

/-- Preservation is derived from fields, independently of transport equality. -/
def Preserves (D : Description.{u}) {X Y : Type u} (e : X ≃ Y) :
    D.Data X → D.Data Y → Prop :=
  match D with
  | .carrier => fun x y => e x = y
  | .fixed _ => fun x y => x = y
  | .product D E => fun x y => D.Preserves e x.1 y.1 ∧ E.Preserves e x.2 y.2
  | .function D E => fun f g =>
      ∀ x y, D.Preserves e x y → E.Preserves e (f x) (g y)

theorem preserves_iff (D : Description.{u}) {X Y : Type u} (e : X ≃ Y)
    (x : D.Data X) (y : D.Data Y) :
    D.Preserves e x y ↔ D.transport e x = y := by
  induction D with
  | carrier => rfl
  | fixed A => rfl
  | product D E hD hE =>
    change (D.Preserves e x.1 y.1 ∧ E.Preserves e x.2 y.2) ↔
      (D.transport e x.1, E.transport e x.2) = y
    constructor
    · intro h
      exact Prod.ext ((hD _ _).mp h.1) ((hE _ _).mp h.2)
    · intro h
      exact ⟨(hD _ _).mpr (congrArg Prod.fst h), (hE _ _).mpr (congrArg Prod.snd h)⟩
  | function D E hD hE =>
    constructor
    · intro h
      funext a
      exact (hE _ _).mp (h _ a ((hD _ _).mpr ((D.transport e).apply_symm_apply a)))
    · intro h a b hab
      apply (hE _ _).mpr
      have hb := (hD _ _).mp hab
      subst b
      have hf := congrFun h (D.transport e a)
      change E.transport e (x ((D.transport e).symm (D.transport e a))) =
        y (D.transport e a) at hf
      simpa only [Equiv.symm_apply_apply] using hf

@[simp] theorem transport_refl (D : Description.{u}) {X : Type u} :
    D.transport (Equiv.refl X) = Equiv.refl _ := by
  induction D with
  | carrier => rfl
  | fixed A => rfl
  | product D E hD hE => simp only [transport, hD, hE]; rfl
  | function D E hD hE => simp only [transport, hD, hE]; rfl

@[simp] theorem transport_trans (D : Description.{u}) {X Y Z : Type u}
    (e : X ≃ Y) (f : Y ≃ Z) :
    D.transport (e.trans f) = (D.transport e).trans (D.transport f) := by
  induction D with
  | carrier => rfl
  | fixed A => rfl
  | product D E hD hE => simp only [transport, hD, hE]; rfl
  | function D E hD hE => simp only [transport, hD, hE]; rfl

@[simp] theorem transport_symm (D : Description.{u}) {X Y : Type u} (e : X ≃ Y) :
    D.transport e.symm = (D.transport e).symm := by
  induction D with
  | carrier => rfl
  | fixed A => rfl
  | product D E hD hE => simp only [transport, hD, hE]; rfl
  | function D E hD hE => simp only [transport, hD, hE]; rfl

theorem preserves_refl (D : Description.{u}) {X : Type u} (x : D.Data X) :
    D.Preserves (Equiv.refl X) x x :=
  (D.preserves_iff _ _ _).mpr (by rw [transport_refl]; rfl)

theorem preserves_trans (D : Description.{u}) {X Y Z : Type u}
    {e : X ≃ Y} {f : Y ≃ Z} {x : D.Data X} {y : D.Data Y} {z : D.Data Z}
    (h : D.Preserves e x y) (k : D.Preserves f y z) : D.Preserves (e.trans f) x z := by
  apply (D.preserves_iff _ _ _).mpr
  rw [transport_trans]
  exact (congrArg (D.transport f) ((D.preserves_iff _ _ _).mp h)).trans
    ((D.preserves_iff _ _ _).mp k)

theorem preserves_symm (D : Description.{u}) {X Y : Type u}
    {e : X ≃ Y} {x : D.Data X} {y : D.Data Y}
    (h : D.Preserves e x y) : D.Preserves e.symm y x := by
  apply (D.preserves_iff _ _ _).mpr
  rw [transport_symm, ← (D.preserves_iff _ _ _).mp h]
  exact (D.transport e).symm_apply_apply x

end Description
end SquareKit.StructureIdentity
