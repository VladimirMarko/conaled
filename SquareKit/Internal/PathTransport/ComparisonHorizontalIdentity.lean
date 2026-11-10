import SquareKit.Internal.PathTransport.ComparisonHorizontal

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

private theorem transport_obj {C D : Grpd.{u,u}} (h : C = D) (x : C) :
    HEq ((eqToHom h).obj x) x := by cases h; rfl

private theorem discrete_mk_heq {α β : Type u} {x : α} {y : β} (h : HEq x y) :
    HEq (Discrete.mk x) (Discrete.mk y) := by cases h; rfl

private theorem identity_transport_as {C : Type u} [Category.{u} C]
    {x y x' y' : C} (hx : x = x') (hy : y = y')
    (h : @Grpd.of (Discrete (x ⟶ y)) Groupoid.ofIsGroupoid =
      @Grpd.of (Discrete (x' ⟶ y')) Groupoid.ofIsGroupoid)
    (p : Discrete (x ⟶ y)) : HEq (((eqToHom h).obj p).as) p.as := by
  cases hx; cases hy; rfl

private theorem map_heq {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) {x y x' y' : C} (hx : x = x') (hy : y = y')
    {p : x ⟶ y} {q : x' ⟶ y'} (hp : HEq p q) : HEq (F.map p) (F.map q) := by
  cases hx; cases hy; cases eq_of_heq hp; rfl

namespace Family
variable {Γ Δ : Context.{u}}

theorem horizontal_identity_middle (A : Family Γ) (B : Family Δ)
    (x y : Section A) (x' y' : Section B)
    (h : Γ.right = Δ.left) (hA : HEq A.right B.left)
    (hx : HEq x.right x'.left) (hy : HEq y.right y'.left) :
    HEq (A.identity x y).right (B.identity x' y').left := by
  cases Γ; cases Δ; dsimp at h; cases h
  cases A; cases B; dsimp at hA; cases eq_of_heq hA
  cases x; cases y; cases x'; cases y'
  dsimp at hx hy
  cases eq_of_heq hx; cases eq_of_heq hy
  rfl

theorem horizontal_identity (A : Family Γ) (B : Family Δ)
    (x y : Section A) (x' y' : Section B)
    (h : Γ.right = Δ.left) (hA : HEq A.right B.left)
    (hx : HEq x.right x'.left) (hy : HEq y.right y'.left) :
    (A.horizontal B h hA).identity (x.horizontal x' h hA hx) (y.horizontal y' h hA hy) =
      (A.identity x y).horizontal (B.identity x' y') h
        (horizontal_identity_middle A B x y x' y' h hA hx hy) := by
  cases Γ with | mk C D R =>
  cases Δ with | mk D' E S =>
  dsimp at h; cases h
  cases A with | mk A₀ A₁ α =>
  cases B with | mk B₀ B₁ β =>
  dsimp at hA; cases eq_of_heq hA
  cases x with | mk x₀ x₁ hc =>
  cases x' with | mk x₁' x₂ hd =>
  cases y with | mk y₀ y₁ he =>
  cases y' with | mk y₁' y₂ hf =>
  dsimp at hx hy; cases eq_of_heq hx; cases eq_of_heq hy
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext γ
  fapply CategoryTheory.Functor.ext
  · intro p
    dsimp [identity, horizontal, Section.horizontal, identityMap, directIdentityMap, discrete]
    simp only [eqToHom_app, Grpd.comp_eq_comp, CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.comp_map]
    apply eq_of_heq
    apply (transport_obj _ _).trans
    apply HEq.symm
    apply (transport_obj _ _).trans
    apply discrete_mk_heq
    have hxc : (α.app γ).obj (x₀.obj γ) = x₁.obj (R.obj γ) :=
      congrArg (fun s : GroupoidModel.Section (R ⋙ A₁) => s.obj γ) hc
    have hyc : (α.app γ).obj (y₀.obj γ) = y₁.obj (R.obj γ) :=
      congrArg (fun s : GroupoidModel.Section (R ⋙ A₁) => s.obj γ) he
    apply map_heq (β.app (R.obj γ)) hxc.symm hyc.symm
    exact identity_transport_as hxc hyc _ _
  · intro p q f
    exact congrArg Discrete.Hom.mk rfl

end Family
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
