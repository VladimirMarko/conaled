import SquareKit.SheafGroupoidBibundleTensor
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! Actual balanced-product unitors and their naturality. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

def identityPoint {U : Cᵒᵖ} (m : H.Section U) :
    Fiber H H.objects (identity H).right.family (atSection m) m :=
  regularIdentity H (identityObject H) (atSection m)

def rightUnitRaw : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ ordinarySource P.right (identity H).right :=
  (ordinary_pullback P.right (identity H).right).lift
    (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P.right ≫ regularIdentitySection H (identityObject H))
    (𝟙 _) (by rfl)

theorem rightUnitRaw_pair (x : G.objects.obj.Elements) (k : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x k) :
    (rightUnitRaw P).hom.app x.obj ⟨(x.val,k.val),p⟩ =
      pairPoint P.right (identity H).right x k p k (identityPoint k) := by
  apply Types.ext_of_isPullback
    (SheafImage.sections_isPullback (ordinary_pullback P.right (identity H).right) x.obj)
  · exact congrArg (fun a : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity H).right =>
      a.hom.app x.obj ⟨(x.val,k.val),p⟩)
        ((ordinary_pullback P.right (identity H).right).lift_fst _ _ _)
  · exact congrArg (fun a : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right =>
      a.hom.app x.obj ⟨(x.val,k.val),p⟩)
        ((ordinary_pullback P.right (identity H).right).lift_snd _ _ _)

def rightUnitTotal : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor P (identity H)).right :=
  rightUnitRaw P ≫ balancedMap P.right (identity H).right (identity H).left

theorem rightUnitTotal_pair (x : G.objects.obj.Elements) (k : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x k) :
    (rightUnitTotal P).hom.app x.obj ⟨(x.val,k.val),p⟩ =
      ⟨(x.val,k.val),tensorPoint P.right (identity H).right (identity H).left x k p k
        (identityPoint k)⟩ := by
  change (balancedMap P.right (identity H).right (identity H).left).hom.app x.obj
    ((rightUnitRaw P).hom.app x.obj _) = _
  rw [rightUnitRaw_pair, balancedMap_pair]

theorem rightUnitTotal_projection : rightUnitTotal P ≫
    SplitSheaf.p (tensor P (identity H)).right.family = SplitSheaf.p P.right.family := by
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨x,k⟩,p⟩
  exact congrArg Sigma.fst (rightUnitTotal_pair P (G.objects.obj.elementsMk U x) ⟨k⟩ p)

def rightUnitFamily : P.right.family.family ⟶ (tensor P (identity H)).right.family.family :=
  SplitSheaf.mapOfTotal (rightUnitTotal P) (rightUnitTotal_projection P)

theorem rightUnitFamily_pair (x : G.objects.obj.Elements) (k : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x k) :
    (rightUnitFamily P).app (point H G.objects x k) p =
    tensorPoint P.right (identity H).right (identity H).left x k p k (identityPoint k) := by
  have hf := SplitSheaf.totalMap_mapOfTotal (rightUnitTotal P) (rightUnitTotal_projection P)
  have he := congrArg (fun a : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor P (identity H)).right =>
    a.hom.app x.obj ⟨(x.val,k.val),p⟩) hf
  exact eq_of_heq (Sigma.mk.inj_iff.mp (he.trans (rightUnitTotal_pair P x k p))).2

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

theorem identityPoint_commute {U : Cᵒᵖ} {k l : H.Section U} (a : k ⟶ l) :
    (identity H).left.act a k (identityPoint k) =
    (identity H).right.act (atSection l) a (identityPoint l) := by
  apply (regularFiberEquiv H (identityObject H) (atSection l) k).injective
  simp only [identity, identityLeftAction, identityPoint, regular, regularAction, Equiv.apply_symm_apply]
  have hk : regularFiberEquiv H (identityObject H) (atSection k) k
      (regularIdentity H (identityObject H) (atSection k)) = 𝟙 k :=
    regularFiberEquiv_identity H (identityObject H) (atSection k)
  have hl : regularFiberEquiv H (identityObject H) (atSection l) l
      (regularIdentity H (identityObject H) (atSection l)) = 𝟙 l :=
    regularFiberEquiv_identity H (identityObject H) (atSection l)
  rw [hk, hl, Category.id_comp, Category.comp_id]

theorem rightUnitFamily_equivariant (x : G.objects.obj.Elements) {k l : H.Section x.obj}
    (a : k ⟶ l) (p : Fiber H G.objects P.right.family x l) :
    (rightUnitFamily P).app (point H G.objects x k) (P.right.act x a p) =
    (tensor P (identity H)).right.act x a ((rightUnitFamily P).app (point H G.objects x l) p) := by
  rw [rightUnitFamily_pair, rightUnitFamily_pair, tensorPoint_balancing, identityPoint_commute]
  exact tensorPoint_equivariant P.right (identity H).right (identity H).left x l p a (identityPoint l)

def rightUnitInverse : SquareKit.SheafGroupoid.Bibundle.Map P (tensor P (identity H)) where
  hom := rightUnitFamily P
  equivariant x _ _ a p := rightUnitFamily_equivariant P x a p
  left_equivariant a k p := by
    rw [rightUnitFamily_pair, rightUnitFamily_pair]
    exact (residualAct_tensorPoint (identity H).right (identity H).left P.right P.left a k p k
      (identityPoint k)).symm

def rightUnitor : tensor P (identity H) ≅ P :=
  (asIso (show P ⟶ tensor P (identity H) from rightUnitInverse P)).symm

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

def leftUnitRaw : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ ordinarySource (identity G).right P.right :=
  (ordinary_pullback (identity G).right P.right).lift (𝟙 _)
    (P.right.toAction.projection ≫ regularIdentitySection G (identityObject G)) (by rfl)

theorem leftUnitRaw_pair (x : G.objects.obj.Elements) (k : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x k) :
    (leftUnitRaw P).hom.app x.obj ⟨(x.val,k.val),p⟩ =
      pairPoint (identity G).right P.right x ⟨x.val⟩ (identityPoint (⟨x.val⟩ : G.Section x.obj)) k p := by
  apply Types.ext_of_isPullback
    (SheafImage.sections_isPullback (ordinary_pullback (identity G).right P.right) x.obj)
  · exact congrArg (fun a : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right =>
      a.hom.app x.obj ⟨(x.val,k.val),p⟩)
        ((ordinary_pullback (identity G).right P.right).lift_fst _ _ _)
  · exact congrArg (fun a : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right =>
      a.hom.app x.obj ⟨(x.val,k.val),p⟩)
        ((ordinary_pullback (identity G).right P.right).lift_snd _ _ _)

def leftUnitTotal : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor (identity G) P).right :=
  leftUnitRaw P ≫ balancedMap (identity G).right P.right P.left

theorem leftUnitTotal_pair (x : G.objects.obj.Elements) (k : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x k) :
    (leftUnitTotal P).hom.app x.obj ⟨(x.val,k.val),p⟩ =
      ⟨(x.val,k.val),tensorPoint (identity G).right P.right P.left x ⟨x.val⟩
        (identityPoint (⟨x.val⟩ : G.Section x.obj)) k p⟩ := by
  change (balancedMap (identity G).right P.right P.left).hom.app x.obj
    ((leftUnitRaw P).hom.app x.obj _) = _
  rw [leftUnitRaw_pair, balancedMap_pair]

theorem leftUnitTotal_projection : leftUnitTotal P ≫
    SplitSheaf.p (tensor (identity G) P).right.family = SplitSheaf.p P.right.family := by
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨x,k⟩,p⟩
  exact congrArg Sigma.fst (leftUnitTotal_pair P (G.objects.obj.elementsMk U x) ⟨k⟩ p)

def leftUnitFamily : P.right.family.family ⟶ (tensor (identity G) P).right.family.family :=
  SplitSheaf.mapOfTotal (leftUnitTotal P) (leftUnitTotal_projection P)

theorem leftUnitFamily_pair (x : G.objects.obj.Elements) (k : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x k) :
    (leftUnitFamily P).app (point H G.objects x k) p =
      tensorPoint (identity G).right P.right P.left x ⟨x.val⟩
        (identityPoint (⟨x.val⟩ : G.Section x.obj)) k p := by
  have hf := SplitSheaf.totalMap_mapOfTotal (leftUnitTotal P) (leftUnitTotal_projection P)
  have he := congrArg (fun a : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor (identity G) P).right =>
    a.hom.app x.obj ⟨(x.val,k.val),p⟩) hf
  exact eq_of_heq (Sigma.mk.inj_iff.mp (he.trans (leftUnitTotal_pair P x k p))).2

def leftUnitInverse : SquareKit.SheafGroupoid.Bibundle.Map P (tensor (identity G) P) where
  hom := leftUnitFamily P
  equivariant x _ _ a p := by
    rw [leftUnitFamily_pair, leftUnitFamily_pair]
    exact tensorPoint_equivariant (identity G).right P.right P.left x ⟨x.val⟩ _ a p
  left_equivariant {U x y} a k p := by
    rw [leftUnitFamily_pair, leftUnitFamily_pair]
    change tensorPoint (identity G).right P.right P.left (atSection y) y (identityPoint y) k
      (P.left.act a k p) = residualAct P.right P.left (identity G).right (identity G).left a k
        (tensorPoint (identity G).right P.right P.left (atSection x) x (identityPoint x) k p)
    rw [residualAct_tensorPoint, identityPoint_commute]
    exact (tensorPoint_balancing (identity G).right P.right P.left (atSection y) a
      (identityPoint y) k p).symm

def leftUnitor : tensor (identity G) P ≅ P :=
  (asIso (show P ⟶ tensor (identity G) P from leftUnitInverse P)).symm

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable {P Q : Bibundle G H} (f : SquareKit.SheafGroupoid.Bibundle.Map P Q)

theorem rightUnitInverse_natural : f.comp (rightUnitInverse Q) =
    (rightUnitInverse P).comp (SquareKit.SheafGroupoid.Bibundle.map f (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity H))) := by
  apply SquareKit.SheafGroupoid.Bibundle.Map.ext
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  rcases z with @⟨U,⟨x,k⟩⟩
  change (rightUnitFamily Q).app (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩)
      (f.hom.app (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩) p) =
    (mapFamily f (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity H))).app
      (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩)
      ((rightUnitFamily P).app (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩) p)
  rw [rightUnitFamily_pair, rightUnitFamily_pair, mapFamily_tensorPoint]
  rfl

theorem leftUnitInverse_natural : f.comp (leftUnitInverse Q) =
    (leftUnitInverse P).comp (SquareKit.SheafGroupoid.Bibundle.map (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity G)) f) := by
  apply SquareKit.SheafGroupoid.Bibundle.Map.ext
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  rcases z with @⟨U,⟨x,k⟩⟩
  change (leftUnitFamily Q).app (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩)
      (f.hom.app (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩) p) =
    (mapFamily (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity G)) f).app
      (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩)
      ((leftUnitFamily P).app (point H G.objects (G.objects.obj.elementsMk U x) ⟨k⟩) p)
  rw [leftUnitFamily_pair, leftUnitFamily_pair, mapFamily_tensorPoint]
  rfl

theorem rightUnitor_natural :
    SquareKit.SheafGroupoid.Bibundle.map f (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity H)) ≫ (rightUnitor Q).hom =
      (rightUnitor P).hom ≫ f := by
  apply (cancel_mono (rightUnitor Q).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h : f ≫ (rightUnitor Q).inv = (rightUnitor P).inv ≫
      SquareKit.SheafGroupoid.Bibundle.map f (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity H)) := rightUnitInverse_natural f
  rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem leftUnitor_natural :
    SquareKit.SheafGroupoid.Bibundle.map (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity G)) f ≫ (leftUnitor Q).hom =
      (leftUnitor P).hom ≫ f := by
  apply (cancel_mono (leftUnitor Q).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h : f ≫ (leftUnitor Q).inv = (leftUnitor P).inv ≫
      SquareKit.SheafGroupoid.Bibundle.map (SquareKit.SheafGroupoid.Bibundle.Map.ident (identity G)) f := leftUnitInverse_natural f
  rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SquareKit.SheafGroupoid.Bibundle
