import SquareKit.SheafGroupoidBalancedAction
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! Principal bibundles, all equivariant maps and the identity bibundle. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G H : Operations J) [G.Laws] [H.Laws]
structure Bibundle where
  right : Principal H G.objects
  left : LeftAction right
end SquareKit.SheafGroupoid

namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
structure Map (P Q : Bibundle G H) extends Bundle.Map P.right Q.right where
  left_equivariant {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y)
    (m : H.Section U) (p : Fiber H G.objects P.right.family (atSection x) m) :
    hom.app (point H G.objects (atSection y) m) (P.left.act g m p) =
      Q.left.act g m (hom.app (point H G.objects (atSection x) m) p)
@[ext] theorem Map.ext {P Q : Bibundle G H} (f g : Map P Q)
    (h : f.toMap = g.toMap) : f = g := by cases f; cases g; cases h; rfl

def Map.ident (P : Bibundle G H) : Map P P where
  toMap := Bundle.Map.ident P.right
  left_equivariant _ _ _ := rfl

def Map.comp {P Q R : Bibundle G H} (f : Map P Q) (g : Map Q R) : Map P R where
  toMap := f.toMap.comp g.toMap
  left_equivariant a m p := by
    change g.hom.app _ (f.hom.app _ (P.left.act a m p)) = _
    rw [f.left_equivariant, g.left_equivariant]
    rfl
instance : Category (Bibundle G H) where
  Hom := Map
  id := Map.ident
  comp := Map.comp
  id_comp f := by apply Map.ext; apply Bundle.Map.ext; exact Category.id_comp f.hom
  comp_id f := by apply Map.ext; apply Bundle.Map.ext; exact Category.comp_id f.hom
  assoc f g h := by apply Map.ext; apply Bundle.Map.ext; exact Category.assoc f.hom g.hom h.hom

namespace Map
variable {P Q : Bibundle G H} (f : Map P Q)
def inverse : Map Q P where
  toMap := f.toMap.inverse
  left_equivariant {U x y} g m p := by
    apply f.toMap.injective (atSection y) m
    have cancel (z : G.Section U) (q : Fiber H G.objects Q.right.family (atSection z) m) :
        f.hom.app (point H G.objects (atSection z) m)
          (f.toMap.inverse.hom.app (point H G.objects (atSection z) m) q) = q :=
      congrArg (fun h : Bundle.Map Q.right Q.right =>
        h.hom.app (point H G.objects (atSection z) m) q) f.toMap.inverse_comp
    rw [cancel, f.left_equivariant, cancel]
@[simp] theorem inverse_comp : f.inverse.comp f = Map.ident Q := by
  apply Map.ext
  exact f.toMap.inverse_comp
@[simp] theorem comp_inverse : f.comp f.inverse = Map.ident P := by
  apply Map.ext
  exact f.toMap.comp_inverse
end Map
instance : Groupoid (Bibundle G H) where
  inv := Map.inverse
  inv_comp := Map.inverse_comp
  comp_inv := Map.comp_inverse
end SquareKit.SheafGroupoid.Bibundle

namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) [G.Laws]
def identityObject : G.Object G.objects := ⟨𝟙 _⟩
def identityLeftAction : LeftAction (regular G (identityObject G)) where
  act {U m n} h k q := (regularFiberEquiv G (identityObject G) (atSection n) k).symm
    (regularFiberEquiv G (identityObject G) (atSection m) k q ≫ h)
  identity m k q := by
    change (regularFiberEquiv G (identityObject G) (atSection m) k).symm
      (regularFiberEquiv G (identityObject G) (atSection m) k q ≫
        𝟙 (value G (identityObject G) (atSection m))) = q
    simp
  comp h g k q := by simp [Category.assoc]
  natural {U V} f m n h k q := by
    apply (regularFiberEquiv G (identityObject G) (atSection (n.restrict G f))
      (k.restrict G f)).injective
    apply Operations.Arrow.ext
    dsimp only [regular, regularAction] at *
    erw [regularFiberEquiv_natural_map G (identityObject G)
      (ElementFamilies.along G.objects.obj f n.val)]
    simp only [Equiv.apply_symm_apply]
    dsimp only [Operations.sectionRestriction]
    simp only [Equiv.apply_symm_apply]
    change (sectionParameter J).map f.unop ≫
        ((regularFiberEquiv G (identityObject G) (atSection m) k q).comp G h).map =
      ((regularFiberEquiv G (identityObject G) (atSection (m.restrict G f)) (k.restrict G f)
        ((regularFamily G (identityObject G)).family.map (pointArrow G G.objects
          (ElementFamilies.along G.objects.obj f m.val) k) q)).comp G
        (Operations.SectionArrow.restrict G f h)).map
    simp only [Operations.Arrow.comp, Operations.SectionArrow.restrict_map]
    rw [← Category.assoc]
    congr 1
    apply CategoryTheory.Limits.pullback.hom_ext <;> simp
    exact (regularFiberEquiv_natural_map G (identityObject G)
      (ElementFamilies.along G.objects.obj f m.val) k q).symm
  commute h k l g q := by
    apply (regularFiberEquiv G (identityObject G) _ _).injective
    simp [regular, regularAction, Category.assoc]
def identity : Bibundle G G where
  right := regular G (identityObject G)
  left := identityLeftAction G
end SquareKit.SheafGroupoid.Bibundle
