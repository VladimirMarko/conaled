import SquareKit.SheafGroupoidBibundle

/-! The opposite bibundle from primitive left principality. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

structure LeftPrincipal : Prop where
  principal {U : Cᵒᵖ} (x y : G.Section U) (k : H.Section U)
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k) :
    ∃! g : x ⟶ y, P.left.act g k p = q
  locallySurjective : Presheaf.IsLocallySurjective J (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P.right).hom


def swap : Bundle.base G H.objects ⟶ Bundle.base H G.objects := ⟨{
  app U := ↾Prod.swap
  naturality := by intros; rfl }⟩

def oppositeFamily : SplitSheaf.Ty (Bundle.base G H.objects) := SplitSheaf.tySub P.right.family swap

def oppositeTotalIso : SplitSheaf.extension (oppositeFamily P) ≅ SplitSheaf.extension P.right.family where
  hom := ⟨{ app U := ↾fun t => ⟨t.1.swap,t.2⟩, naturality := by intros; rfl }⟩
  inv := ⟨{ app U := ↾fun t => ⟨t.1.swap,t.2⟩, naturality := by intros; rfl }⟩

theorem map_groupoid_inv {A B : Type*} [Groupoid A] [Groupoid B] (F : A ⥤ B)
    {x y : A} (f : x ⟶ y) : F.map (Groupoid.inv f) = Groupoid.inv (F.map f) := by
  simp [Groupoid.inv_eq_inv]

def oppositeAction : Bundle.Action G H.objects where
  family := oppositeFamily P
  act x {m n} g t := P.left.act (Groupoid.inv g) ⟨x.val⟩ t
  act_id x m t := by simpa using P.left.identity m ⟨x.val⟩ t
  act_comp x {m n q} g h t := by simpa using (P.left.comp (Groupoid.inv h) (Groupoid.inv g) ⟨x.val⟩ t).symm
  natural {x y} f {m n} g t := by
    rcases x with @⟨U,xx⟩
    rcases y with @⟨V,yy⟩
    rcases f with ⟨ff,hf⟩
    change U ⟶ V at ff
    change H.objects.obj.map ff xx = yy at hf
    subst yy
    have h := P.left.natural ff (Groupoid.inv g) ⟨xx⟩ t
    rw [map_groupoid_inv] at h
    exact h

def oppositeRight (hP : LeftPrincipal P) : Principal G H.objects where
  toAction := oppositeAction P
  principal x m n p q := by
    obtain ⟨g,hg,hu⟩ := hP.principal m n ⟨x.val⟩ p q
    refine ⟨Groupoid.inv g, ?_, ?_⟩
    · change P.left.act (Groupoid.inv (Groupoid.inv g)) ⟨x.val⟩ p = q
      simpa using hg
    · intro a ha
      have h := hu (Groupoid.inv a) ha
      simpa using congrArg Groupoid.inv h
  isLocallySurjective := by
    have : Presheaf.IsLocallySurjective J (oppositeTotalIso P).hom.hom := inferInstance
    have : Presheaf.IsLocallySurjective J (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P.right).hom :=
      hP.locallySurjective
    change Presheaf.IsLocallySurjective J
      ((oppositeTotalIso P).hom.hom ≫ (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P.right).hom)
    infer_instance

def oppositeLeft (hP : LeftPrincipal P) : LeftAction (oppositeRight P hP) where
  act {U m n} g k t := P.right.act (atSection k) (Groupoid.inv g) t
  identity {U} m k t := by simpa using P.right.act_id (atSection k) m t
  comp {U m n l} g h k t := by simpa using (P.right.act_comp (atSection k) (Groupoid.inv h) (Groupoid.inv g) t).symm
  natural {U V} f {m n} g k t := by
    have h := P.right.natural (ElementFamilies.along G.objects.obj f k.val) (Groupoid.inv g) t
    rw [map_groupoid_inv] at h
    exact h
  commute {U m n} g {k l} h t := (P.left.commute (Groupoid.inv h) (Groupoid.inv g) t).symm

def opposite (hP : LeftPrincipal P) : Bibundle H G where
  right := oppositeRight P hP
  left := oppositeLeft P hP

end SquareKit.SheafGroupoid.Bibundle
