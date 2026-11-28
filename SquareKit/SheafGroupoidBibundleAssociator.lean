import SquareKit.SheafGroupoidBibundleUnitors
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! The balanced-product associator, pentagon and triangle. -/
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
variable {G H K L : Operations J} [G.Laws] [H.Laws] [K.Laws] [L.Laws]
variable (P : Bibundle G H) (Q : Bibundle H K) (R : Bibundle K L)

abbrev leftAssociated := tensor (tensor P Q) R
abbrev rightAssociated := tensor P (tensor Q R)

def localInverse : Bundle.Map (localBundle P.right (tensor Q R).right)
    (Bundle.reindex (leftAssociated P Q R).right (SplitSheaf.p (cover P.right))) :=
  (((baseChangeIso Q.right R.right R.left (coverAnchorMap P.right)).inv).comp
    (SquareKit.SheafGroupoid.Bundle.BalancedAction.tensorMap R.right R.left
      (Descent.comparison (compositionDatum P.right Q.right Q.left)).inverse)).comp
    (baseChangeMap (tensor P Q).right R.right R.left (SplitSheaf.p (cover P.right)))

theorem comparison_inverse_tensorPoint (x : G.objects.obj.Elements)
    (a : (cover P.right).family.obj x) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.right.family (atSection (coverAnchor P.right x a)) k) :
    (Descent.comparison (compositionDatum P.right Q.right Q.left)).inverse.hom.app
      (point K (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x a) k) q =
    tensorPoint P.right Q.right Q.left x (coverAnchor P.right x a) (coverPoint P.right x a) k q := by
  apply (Descent.comparison (compositionDatum P.right Q.right Q.left)).injective
    (Descent.liftPoint (cover P.right) x a) k
  have hc := congrArg (fun f : Bundle.Map (localBundle P.right Q.right) (localBundle P.right Q.right) =>
    f.hom.app (point K (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x a) k) q)
    (Descent.comparison (compositionDatum P.right Q.right Q.left)).inverse_comp
  change _ = q at hc
  refine hc.trans ?_
  rcases x with @⟨U,x⟩
  rcases a with ⟨⟨⟨x',m⟩,p⟩,e⟩
  change x' = x at e
  subst x'
  exact (Equiv.apply_symm_apply _ q).symm

theorem localInverse_tensorPoint (x : G.objects.obj.Elements)
    (a : (cover P.right).family.obj x) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.right.family (atSection (coverAnchor P.right x a)) k)
    (l : L.Section x.obj) (r : Fiber L K.objects R.right.family (atSection k) l) :
    (localInverse P Q R).hom.app (point L (SplitSheaf.extension (cover P.right))
      (Descent.liftPoint (cover P.right) x a) l)
      (tensorPoint Q.right R.right R.left (atSection (coverAnchor P.right x a)) k q l r) =
    tensorPoint (tensor P Q).right R.right R.left x k
      (tensorPoint P.right Q.right Q.left x (coverAnchor P.right x a) (coverPoint P.right x a) k q) l r := by
  change (baseChangeFamily (tensor P Q).right R.right R.left (SplitSheaf.p (cover P.right))).app _
    ((tensorMapFamily R.right R.left (Descent.comparison (compositionDatum P.right Q.right Q.left)).inverse).app _
      ((baseChangeIso Q.right R.right R.left (coverAnchorMap P.right)).inv.hom.app _ _)) = _
  let z := Descent.liftPoint (cover P.right) x a
  have hb := baseChangeInv_tensorPoint Q.right R.right R.left (coverAnchorMap P.right) z k q l r
  have ht := tensorMapFamily_tensorPoint R.right R.left
    (Descent.comparison (compositionDatum P.right Q.right Q.left)).inverse z k q l r
  have hc := baseChangeFamily_tensorPoint (tensor P Q).right R.right R.left
    (SplitSheaf.p (cover P.right)) z k
      ((Descent.comparison (compositionDatum P.right Q.right Q.left)).inverse.hom.app
        (point K (SplitSheaf.extension (cover P.right)) z k) q) l r
  exact (congrArg (fun t => (baseChangeFamily (tensor P Q).right R.right R.left
      (SplitSheaf.p (cover P.right))).app (point L _ z l)
      ((tensorMapFamily R.right R.left (Descent.comparison (compositionDatum P.right Q.right Q.left)).inverse).app
        (point L _ z l) t)) hb).trans
    ((congrArg ((baseChangeFamily (tensor P Q).right R.right R.left
      (SplitSheaf.p (cover P.right))).app (point L _ z l)) ht).trans
      (hc.trans (congrArg (fun t => tensorPoint (tensor P Q).right R.right R.left x k t l r)
        (comparison_inverse_tensorPoint P Q x a k q))))

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L : Operations J} [G.Laws] [H.Laws] [K.Laws] [L.Laws]
variable (P : Bibundle G H) (Q : Bibundle H K) (R : Bibundle K L)

theorem localInverse_transport_pair (x : G.objects.obj.Elements)
    (a b : (cover P.right).family.obj x) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.right.family (atSection (coverAnchor P.right x a)) k)
    (l : L.Section x.obj) (r : Fiber L K.objects R.right.family (atSection k) l) :
    (localInverse P Q R).hom.app (point L _ (Descent.liftPoint (cover P.right) x b) l)
      ((compositionDatum P.right (tensor Q R).right (tensor Q R).left).transport x a b l
        (tensorPoint Q.right R.right R.left (atSection (coverAnchor P.right x a)) k q l r)) =
    (localInverse P Q R).hom.app (point L _ (Descent.liftPoint (cover P.right) x a) l)
      (tensorPoint Q.right R.right R.left (atSection (coverAnchor P.right x a)) k q l r) := by
  let h := connector P.right x (coverPoint P.right x b) (coverPoint P.right x a)
  change (localInverse P Q R).hom.app
    (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x b) l)
    (residualAct R.right R.left Q.right Q.left h l
      (tensorPoint Q.right R.right R.left (atSection (coverAnchor P.right x a)) k q l r)) = _
  have hr := residualAct_tensorPoint R.right R.left Q.right Q.left h k q l r
  have hb := localInverse_tensorPoint P Q R x b k (Q.left.act h k q) l r
  have ha := localInverse_tensorPoint P Q R x a k q l r
  have he := tensorPoint_balancing P.right Q.right Q.left x h (coverPoint P.right x b) k q
  have hc : P.right.act x h (coverPoint P.right x b) = coverPoint P.right x a :=
    connector_spec P.right x (coverPoint P.right x b) (coverPoint P.right x a)
  have hp := he.symm.trans (congrArg
    (fun p => tensorPoint P.right Q.right Q.left x (coverAnchor P.right x a) p k q) hc)
  exact (congrArg ((localInverse P Q R).hom.app
    (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x b) l)) hr).trans
    (hb.trans ((congrArg (fun t => tensorPoint (tensor P Q).right R.right R.left x k t l r) hp).trans ha.symm))

theorem localInverse_transport (x : G.objects.obj.Elements)
    (a b : (cover P.right).family.obj x) (l : L.Section x.obj)
    (t : Fiber L H.objects (tensor Q R).right.family (atSection (coverAnchor P.right x a)) l) :
    (localInverse P Q R).hom.app (point L _ (Descent.liftPoint (cover P.right) x b) l)
      ((compositionDatum P.right (tensor Q R).right (tensor Q R).left).transport x a b l t) =
    (localInverse P Q R).hom.app (point L _ (Descent.liftPoint (cover P.right) x a) l) t := by
  apply SplitSheafDescent.fiber_ext (leftAssociated P Q R).right.family (point L G.objects x l)
    (Presheaf.imageSieve Q.right.toAction.projection.hom (coverAnchor P.right x a).val)
    (Presheaf.imageSieve_mem J Q.right.toAction.projection.hom (coverAnchor P.right x a).val)
  rintro V j ⟨⟨⟨m,k⟩,q⟩,hq⟩
  change V ⟶ unop x.obj at j
  change m = H.objects.obj.map j.op (coverAnchor P.right x a).val at hq
  subst m
  let e := ElementFamilies.along G.objects.obj j.op x.val
  let x' := G.objects.obj.elementsMk (op V) (G.objects.obj.map j.op x.val)
  let a' := (cover P.right).family.map e a
  let b' := (cover P.right).family.map e b
  let l' := l.restrict L j.op
  let ea := SplitFunctionDiagram.pairArrow (cover P.right).family e a
  let eb := SplitFunctionDiagram.pairArrow (cover P.right).family e b
  let t' := (localBundle P.right (tensor Q R).right).family.family.map
    (pointArrow L (SplitSheaf.extension (cover P.right)) ea l) t
  have hn := (compositionDatum P.right (tensor Q R).right (tensor Q R).left).natural e a b l t
  have hna := NatTrans.naturality_apply (localInverse P Q R).hom (pointArrow L (SplitSheaf.extension (cover P.right)) ea l) t
  have hnb := NatTrans.naturality_apply (localInverse P Q R).hom (pointArrow L (SplitSheaf.extension (cover P.right)) eb l)
    ((compositionDatum P.right (tensor Q R).right (tensor Q R).left).transport x a b l t)
  let d : (cover Q.right).family.obj (atSection (coverAnchor P.right x' a')) :=
    ⟨⟨((coverAnchor P.right x' a').val,k),q⟩,rfl⟩
  let r := Descent.evaluationEquiv (compositionDatum Q.right R.right R.left)
    (atSection (coverAnchor P.right x' a')) d l' t'
  have ht : tensorPoint Q.right R.right R.left (atSection (coverAnchor P.right x' a')) ⟨k⟩ q l' r = t' :=
    Equiv.symm_apply_apply _ t'
  refine hnb.symm.trans ((congrArg ((localInverse P Q R).hom.app
    (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x' b') l')) hn).trans ?_)
  refine Eq.trans ?_ hna
  change (localInverse P Q R).hom.app
    (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x' b') l')
    ((compositionDatum P.right (tensor Q R).right (tensor Q R).left).transport x' a' b' l' t') =
    (localInverse P Q R).hom.app
      (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x' a') l') t'
  rw [← ht]
  exact localInverse_transport_pair P Q R x' a' b' ⟨k⟩ q l' r

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L : Operations J} [G.Laws] [H.Laws] [K.Laws] [L.Laws]
variable (P : Bibundle G H) (Q : Bibundle H K) (R : Bibundle K L)

def inverseDatumMap : Descent.Map
    (compositionDatum P.right (tensor Q R).right (tensor Q R).left)
    (Descent.canonicalDatum (cover P.right) (leftAssociated P Q R).right) where
  toMap := localInverse P Q R
  transport x a b l t := localInverse_transport P Q R x a b l t

def inverseRight : Bundle.Map (rightAssociated P Q R).right (leftAssociated P Q R).right :=
  (inverseDatumMap P Q R).descend.comp
    (Descent.canonicalRecovery (cover P.right) (leftAssociated P Q R).right)

theorem inverseRight_reindex : (inverseRight P Q R).reindex (SplitSheaf.p (cover P.right)) =
    (Descent.comparison (compositionDatum P.right (tensor Q R).right (tensor Q R).left)).comp
      (localInverse P Q R) := by
  have h := (inverseDatumMap P Q R).evaluation_comm
  rw [Descent.comparison_canonical] at h
  exact h

theorem inverseRight_tensorPoint (x : G.objects.obj.Elements)
    (m : H.Section x.obj) (p : Fiber H G.objects P.right.family x m)
    (k : K.Section x.obj) (q : Fiber K H.objects Q.right.family (atSection m) k)
    (l : L.Section x.obj) (r : Fiber L K.objects R.right.family (atSection k) l) :
    (inverseRight P Q R).hom.app (point L G.objects x l)
      (tensorPoint P.right (tensor Q R).right (tensor Q R).left x m p l
        (tensorPoint Q.right R.right R.left (atSection m) k q l r)) =
    tensorPoint (tensor P Q).right R.right R.left x k
      (tensorPoint P.right Q.right Q.left x m p k q) l r := by
  let a : (cover P.right).family.obj x := ⟨⟨(x.val,m.val),p⟩,rfl⟩
  let t := tensorPoint Q.right R.right R.left (atSection m) k q l r
  have he := congrArg (fun f : Bundle.Map
      (Bundle.reindex (rightAssociated P Q R).right (SplitSheaf.p (cover P.right)))
      (Bundle.reindex (leftAssociated P Q R).right (SplitSheaf.p (cover P.right))) =>
    f.hom.app (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x a) l)
      (tensorPoint P.right (tensor Q R).right (tensor Q R).left x m p l t))
    (inverseRight_reindex P Q R)
  have hc : (Descent.comparison (compositionDatum P.right (tensor Q R).right (tensor Q R).left)).hom.app
      (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x a) l)
      (tensorPoint P.right (tensor Q R).right (tensor Q R).left x m p l t) = t :=
    Equiv.apply_symm_apply _ t
  exact he.trans ((congrArg ((localInverse P Q R).hom.app
    (point L (SplitSheaf.extension (cover P.right)) (Descent.liftPoint (cover P.right) x a) l)) hc).trans
      (localInverse_tensorPoint P Q R x a k q l r))

end SquareKit.SheafGroupoid.Bibundle

namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X Y : Sheaf J (Type (max u v))}
variable (P : Principal H X) (Q : Principal K H.objects) (B : LeftAction Q)

def pairCoverMap : ordinarySource P Q ⟶ X :=
  balancedMap P Q B ≫ (compositionRightBundle P Q B).toAction.projection

instance pairCoverMap_surjective : Presheaf.IsLocallySurjective J (pairCoverMap P Q B).hom := by
  change Presheaf.IsLocallySurjective J
    ((balancedMap P Q B).hom ≫ (compositionRightBundle P Q B).toAction.projection.hom)
  infer_instance

include B in
theorem pairFiber_ext (T : SplitSheaf.Ty Y) {U : Cᵒᵖ} (x : X.obj.obj U) (y : Y.obj.obj U)
    (s t : T.family.obj (Y.obj.elementsMk U y))
    (h : ∀ (V : Cᵒᵖ) (f : U ⟶ V) (m : H.Section V)
      (_p : Fiber H X P.family (X.obj.elementsMk V (X.obj.map f x)) m)
      (k : K.Section V) (_q : Fiber K H.objects Q.family (atSection m) k),
      T.family.map (ElementFamilies.along Y.obj f y) s =
        T.family.map (ElementFamilies.along Y.obj f y) t) : s = t := by
  apply SplitSheafDescent.fiber_ext T (Y.obj.elementsMk U y)
    (Presheaf.imageSieve (pairCoverMap P Q B).hom x)
    (Presheaf.imageSieve_mem J (pairCoverMap P Q B).hom x)
  rintro V j ⟨⟨⟨⟨x',m⟩,p⟩,⟨⟨⟨m',k⟩,q⟩,e⟩⟩,hp⟩
  change m' = m at e
  subst m'
  change x' = X.obj.map j.op x at hp
  subst x'
  exact h (op V) j.op ⟨m⟩ p ⟨k⟩ q

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L : Operations J} [G.Laws] [H.Laws] [K.Laws] [L.Laws]
variable (P : Bibundle G H) (Q : Bibundle H K) (R : Bibundle K L)

theorem inverseRight_left_triple {U : Cᵒᵖ} {x y : G.Section U} (a : x ⟶ y)
    (m : H.Section U) (p : Fiber H G.objects P.right.family (atSection x) m)
    (k : K.Section U) (q : Fiber K H.objects Q.right.family (atSection m) k)
    (l : L.Section U) (r : Fiber L K.objects R.right.family (atSection k) l) :
    (inverseRight P Q R).hom.app (point L G.objects (atSection y) l)
      ((rightAssociated P Q R).left.act a l
        (tensorPoint P.right (tensor Q R).right (tensor Q R).left (atSection x) m p l
          (tensorPoint Q.right R.right R.left (atSection m) k q l r))) =
    (leftAssociated P Q R).left.act a l
      ((inverseRight P Q R).hom.app (point L G.objects (atSection x) l)
        (tensorPoint P.right (tensor Q R).right (tensor Q R).left (atSection x) m p l
          (tensorPoint Q.right R.right R.left (atSection m) k q l r))) := by
  change (inverseRight P Q R).hom.app _
    (residualAct (tensor Q R).right (tensor Q R).left P.right P.left a l _) =
    residualAct R.right R.left (tensor P Q).right (tensor P Q).left a l _
  rw [residualAct_tensorPoint, inverseRight_tensorPoint, inverseRight_tensorPoint,
    residualAct_tensorPoint]
  exact congrArg (fun t => tensorPoint (tensor P Q).right R.right R.left (atSection y) k t l r)
    (residualAct_tensorPoint Q.right Q.left P.right P.left a m p k q).symm

theorem inverseRight_left_equivariant {U : Cᵒᵖ} {x y : G.Section U} (a : x ⟶ y)
    (l : L.Section U) (t : Fiber L G.objects (rightAssociated P Q R).right.family (atSection x) l) :
    (inverseRight P Q R).hom.app (point L G.objects (atSection y) l)
      ((rightAssociated P Q R).left.act a l t) =
    (leftAssociated P Q R).left.act a l
      ((inverseRight P Q R).hom.app (point L G.objects (atSection x) l) t) := by
  apply pairFiber_ext P.right Q.right Q.left (leftAssociated P Q R).right.family x.val (y.val,l.val)
  intro V f m p k q
  change Fiber H G.objects P.right.family (atSection (x.restrict G f)) m at p
  have hy := NatTrans.naturality_apply (inverseRight P Q R).hom
    (pointArrow L G.objects (ElementFamilies.along G.objects.obj f y.val) l)
    ((rightAssociated P Q R).left.act a l t)
  have hx := NatTrans.naturality_apply (inverseRight P Q R).hom
    (pointArrow L G.objects (ElementFamilies.along G.objects.obj f x.val) l) t
  have hs := (rightAssociated P Q R).left.natural f a l t
  have ht := (leftAssociated P Q R).left.natural f a l
    ((inverseRight P Q R).hom.app (point L G.objects (atSection x) l) t)
  let a' := (G.sectionRestriction f).map a
  let l' := l.restrict L f
  let x' := atSection (x.restrict G f)
  let t' := (rightAssociated P Q R).right.family.family.map
    (pointArrow L G.objects (ElementFamilies.along G.objects.obj f x.val) l) t
  let bp : (cover P.right).family.obj x' := ⟨⟨(x'.val,m.val),p⟩,rfl⟩
  let tq := Descent.evaluationEquiv
    (compositionDatum P.right (tensor Q R).right (tensor Q R).left) x' bp l' t'
  let bq : (cover Q.right).family.obj (atSection m) := ⟨⟨(m.val,k.val),q⟩,rfl⟩
  let r := Descent.evaluationEquiv (compositionDatum Q.right R.right R.left) (atSection m) bq l' tq
  have hq : tensorPoint Q.right R.right R.left (atSection m) k q l' r = tq := Equiv.symm_apply_apply _ tq
  have hp : tensorPoint P.right (tensor Q R).right (tensor Q R).left x' m p l' tq = t' :=
    Equiv.symm_apply_apply _ t'
  have he := (congrArg (tensorPoint P.right (tensor Q R).right (tensor Q R).left x' m p l') hq).trans hp
  refine hy.symm.trans ((congrArg ((inverseRight P Q R).hom.app
    (point L G.objects (atSection (y.restrict G f)) l')) hs).trans ?_)
  refine Eq.trans ?_ ((congrArg ((leftAssociated P Q R).left.act a' l') hx).trans ht.symm)
  change (inverseRight P Q R).hom.app _ ((rightAssociated P Q R).left.act a' l' t') =
    (leftAssociated P Q R).left.act a' l' ((inverseRight P Q R).hom.app _ t')
  rw [← he]
  exact inverseRight_left_triple P Q R a' m p k q l' r

def inverseMap : SquareKit.SheafGroupoid.Bibundle.Map (rightAssociated P Q R) (leftAssociated P Q R) where
  toMap := inverseRight P Q R
  left_equivariant a l t := inverseRight_left_equivariant P Q R a l t

def associator : leftAssociated P Q R ≅ rightAssociated P Q R :=
  (asIso (show rightAssociated P Q R ⟶ leftAssociated P Q R from inverseMap P Q R)).symm

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))}
variable (P : Principal H X) (Q : Principal K H.objects) (B : LeftAction Q)

theorem tensorPoint_natural {U V : Cᵒᵖ} (f : U ⟶ V) (x : X.obj.obj U)
    (m : H.Section U) (p : Fiber H X P.family (X.obj.elementsMk U x) m)
    (k : K.Section U) (q : Fiber K H.objects Q.family (atSection m) k) :
    (compositionRightBundle P Q B).family.family.map
      (pointArrow K X (ElementFamilies.along X.obj f x) k)
      (tensorPoint P Q B (X.obj.elementsMk U x) m p k q) =
    tensorPoint P Q B (X.obj.elementsMk V (X.obj.map f x)) (m.restrict H f)
      (P.family.family.map (pointArrow H X (ElementFamilies.along X.obj f x) m) p)
      (k.restrict K f)
      (Q.family.family.map (pointArrow K H.objects (ElementFamilies.along H.objects.obj f m.val) k) q) := by
  have h := NatTrans.naturality_apply (balancedMap P Q B).hom f
    (pairPoint P Q (X.obj.elementsMk U x) m p k q)
  exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L : Operations J} [G.Laws] [H.Laws] [K.Laws] [L.Laws]
variable (P : Bibundle G H) (Q : Bibundle H K) (R : Bibundle K L)

theorem associator_tensorPoint (x : G.objects.obj.Elements)
    (m : H.Section x.obj) (p : Fiber H G.objects P.right.family x m)
    (k : K.Section x.obj) (q : Fiber K H.objects Q.right.family (atSection m) k)
    (l : L.Section x.obj) (r : Fiber L K.objects R.right.family (atSection k) l) :
    (associator P Q R).hom.hom.app (point L G.objects x l)
      (tensorPoint (tensor P Q).right R.right R.left x k
        (tensorPoint P.right Q.right Q.left x m p k q) l r) =
    tensorPoint P.right (tensor Q R).right (tensor Q R).left x m p l
      (tensorPoint Q.right R.right R.left (atSection m) k q l r) := by
  apply (inverseRight P Q R).injective x l
  have hc := congrArg (fun f : leftAssociated P Q R ⟶ leftAssociated P Q R =>
    f.hom.app (point L G.objects x l)
      (tensorPoint (tensor P Q).right R.right R.left x k
        (tensorPoint P.right Q.right Q.left x m p k q) l r)) (associator P Q R).hom_inv_id
  exact hc.trans (inverseRight_tensorPoint P Q R x m p k q l r).symm

def tripleCoverFamily : SplitSheaf.Ty (ordinarySource P.right Q.right) :=
  SplitSheaf.tySub (cover R.right) (ordinaryFirst P.right Q.right ≫ SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor Q.right)

def tripleCoverMap : SplitSheaf.extension (tripleCoverFamily P Q R) ⟶ G.objects :=
  SplitSheaf.p (tripleCoverFamily P Q R) ≫ pairCoverMap P.right Q.right Q.left

instance tripleCoverMap_surjective : Presheaf.IsLocallySurjective J (tripleCoverMap P Q R).hom := by
  change Presheaf.IsLocallySurjective J
    ((SplitSheaf.p (tripleCoverFamily P Q R)).hom ≫ (pairCoverMap P.right Q.right Q.left).hom)
  have : Presheaf.IsLocallySurjective J (SplitSheaf.p (tripleCoverFamily P Q R)).hom :=
    SheafCover.baseChangeCover_isLocallySurjective _
  infer_instance

theorem tripleFiber_ext {Y : Sheaf J (Type (max u v))} (T : SplitSheaf.Ty Y)
    {U : Cᵒᵖ} (x : G.objects.obj.obj U) (y : Y.obj.obj U)
    (s t : T.family.obj (Y.obj.elementsMk U y))
    (h : ∀ (V : Cᵒᵖ) (f : U ⟶ V) (m : H.Section V)
      (_p : Fiber H G.objects P.right.family (G.objects.obj.elementsMk V (G.objects.obj.map f x)) m)
      (k : K.Section V) (_q : Fiber K H.objects Q.right.family (atSection m) k)
      (l : L.Section V) (_r : Fiber L K.objects R.right.family (atSection k) l),
      T.family.map (ElementFamilies.along Y.obj f y) s =
        T.family.map (ElementFamilies.along Y.obj f y) t) : s = t := by
  apply SplitSheafDescent.fiber_ext T (Y.obj.elementsMk U y)
    (Presheaf.imageSieve (tripleCoverMap P Q R).hom x)
    (Presheaf.imageSieve_mem J (tripleCoverMap P Q R).hom x)
  rintro V j ⟨⟨⟨⟨⟨x',m⟩,p⟩,⟨⟨⟨m',k⟩,q⟩,e⟩⟩,⟨⟨⟨k',l⟩,r⟩,d⟩⟩,hp⟩
  change m' = m at e
  subst m'
  change k' = k at d
  subst k'
  change x' = G.objects.obj.map j.op x at hp
  subst x'
  exact h (op V) j.op ⟨m⟩ p ⟨k⟩ q ⟨l⟩ r

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L M : Operations J} [G.Laws] [H.Laws] [K.Laws] [L.Laws] [M.Laws]
variable (P : Bibundle G H) (Q : Bibundle H K) (R : Bibundle K L)

theorem triple_map_ext {T : Bibundle G L}
    (a b : SquareKit.SheafGroupoid.Bibundle.Map (leftAssociated P Q R) T)
    (h : ∀ (x : G.objects.obj.Elements) (m : H.Section x.obj)
      (p : Fiber H G.objects P.right.family x m) (k : K.Section x.obj)
      (q : Fiber K H.objects Q.right.family (atSection m) k) (l : L.Section x.obj)
      (r : Fiber L K.objects R.right.family (atSection k) l),
      a.hom.app (point L G.objects x l)
        (tensorPoint (tensor P Q).right R.right R.left x k
          (tensorPoint P.right Q.right Q.left x m p k q) l r) =
      b.hom.app (point L G.objects x l)
        (tensorPoint (tensor P Q).right R.right R.left x k
          (tensorPoint P.right Q.right Q.left x m p k q) l r)) : a = b := by
  apply SquareKit.SheafGroupoid.Bibundle.Map.ext
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro t
  rcases z with @⟨U,⟨x,l⟩⟩
  apply pairFiber_ext P.right Q.right Q.left T.right.family x (x,l)
  intro V f m p k q
  let x' := G.objects.obj.elementsMk V (G.objects.obj.map f x)
  let l' : L.Section V := ⟨L.objects.obj.map f l⟩
  let t' := (leftAssociated P Q R).right.family.family.map
    (ElementFamilies.along (base L G.objects).obj f (x,l)) t
  let pq := tensorPoint P.right Q.right Q.left x' m p k q
  let bpq : (cover (tensor P Q).right).family.obj x' := ⟨⟨(x'.val,k.val),pq⟩,rfl⟩
  let r := Descent.evaluationEquiv (compositionDatum (tensor P Q).right R.right R.left) x' bpq l' t'
  have ht : tensorPoint (tensor P Q).right R.right R.left x' k pq l' r = t' :=
    Equiv.symm_apply_apply _ t'
  have ha := NatTrans.naturality_apply a.hom (ElementFamilies.along (base L G.objects).obj f (x,l)) t
  have hb := NatTrans.naturality_apply b.hom (ElementFamilies.along (base L G.objects).obj f (x,l)) t
  refine ha.symm.trans (Eq.trans ?_ hb)
  exact (congrArg (a.hom.app (point L G.objects x' l')) ht.symm).trans
    ((h x' m p k q l' r).trans (congrArg (b.hom.app (point L G.objects x' l')) ht))

theorem quadruple_map_ext (S : Bibundle L M) {T : Bibundle G M}
    (a b : SquareKit.SheafGroupoid.Bibundle.Map (tensor (leftAssociated P Q R) S) T)
    (h : ∀ (x : G.objects.obj.Elements) (m : H.Section x.obj)
      (p : Fiber H G.objects P.right.family x m) (k : K.Section x.obj)
      (q : Fiber K H.objects Q.right.family (atSection m) k) (l : L.Section x.obj)
      (r : Fiber L K.objects R.right.family (atSection k) l) (n : M.Section x.obj)
      (s : Fiber M L.objects S.right.family (atSection l) n),
      a.hom.app (point M G.objects x n)
        (tensorPoint (leftAssociated P Q R).right S.right S.left x l
          (tensorPoint (tensor P Q).right R.right R.left x k
            (tensorPoint P.right Q.right Q.left x m p k q) l r) n s) =
      b.hom.app (point M G.objects x n)
        (tensorPoint (leftAssociated P Q R).right S.right S.left x l
          (tensorPoint (tensor P Q).right R.right R.left x k
            (tensorPoint P.right Q.right Q.left x m p k q) l r) n s)) : a = b := by
  apply SquareKit.SheafGroupoid.Bibundle.Map.ext
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro t
  rcases z with @⟨U,⟨x,n⟩⟩
  apply tripleFiber_ext P Q R T.right.family x (x,n)
  intro V f m p k q l r
  let x' := G.objects.obj.elementsMk V (G.objects.obj.map f x)
  let n' : M.Section V := ⟨M.objects.obj.map f n⟩
  let t' := (tensor (leftAssociated P Q R) S).right.family.family.map
    (ElementFamilies.along (base M G.objects).obj f (x,n)) t
  let pqr := tensorPoint (tensor P Q).right R.right R.left x' k
    (tensorPoint P.right Q.right Q.left x' m p k q) l r
  let bpqr : (cover (leftAssociated P Q R).right).family.obj x' := ⟨⟨(x'.val,l.val),pqr⟩,rfl⟩
  let s := Descent.evaluationEquiv (compositionDatum (leftAssociated P Q R).right S.right S.left) x' bpqr n' t'
  have ht : tensorPoint (leftAssociated P Q R).right S.right S.left x' l pqr n' s = t' :=
    Equiv.symm_apply_apply _ t'
  have ha := NatTrans.naturality_apply a.hom (ElementFamilies.along (base M G.objects).obj f (x,n)) t
  have hb := NatTrans.naturality_apply b.hom (ElementFamilies.along (base M G.objects).obj f (x,n)) t
  refine ha.symm.trans (Eq.trans ?_ hb)
  exact (congrArg (a.hom.app (point M G.objects x' n')) ht.symm).trans
    ((h x' m p k q l r n' s).trans (congrArg (b.hom.app (point M G.objects x' n')) ht))

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L M : Operations J} [G.Laws] [H.Laws] [K.Laws] [L.Laws] [M.Laws]
variable (P : Bibundle G H) (Q : Bibundle H K) (R : Bibundle K L)

theorem pentagon (S : Bibundle L M) :
    (associator (tensor P Q) R S).hom ≫ (associator P Q (tensor R S)).hom =
    SquareKit.SheafGroupoid.Bibundle.map (associator P Q R).hom (SquareKit.SheafGroupoid.Bibundle.Map.ident S) ≫
      (associator P (tensor Q R) S).hom ≫
        SquareKit.SheafGroupoid.Bibundle.map (SquareKit.SheafGroupoid.Bibundle.Map.ident P) (associator Q R S).hom := by
  apply quadruple_map_ext P Q R S
  intro x m p k q l r n s
  change (associator P Q (tensor R S)).hom.hom.app (point M G.objects x n)
      ((associator (tensor P Q) R S).hom.hom.app (point M G.objects x n) _) =
    (mapFamily (SquareKit.SheafGroupoid.Bibundle.Map.ident P) (associator Q R S).hom).app (point M G.objects x n)
      ((associator P (tensor Q R) S).hom.hom.app (point M G.objects x n)
        ((mapFamily (associator P Q R).hom (SquareKit.SheafGroupoid.Bibundle.Map.ident S)).app (point M G.objects x n) _))
  simp only [mapFamily_tensorPoint, associator_tensorPoint]
  rfl

variable {P Q R} {P' : Bibundle G H} {Q' : Bibundle H K} {R' : Bibundle K L}
theorem associator_natural (f : SquareKit.SheafGroupoid.Bibundle.Map P P') (g : SquareKit.SheafGroupoid.Bibundle.Map Q Q')
    (h : SquareKit.SheafGroupoid.Bibundle.Map R R') :
    SquareKit.SheafGroupoid.Bibundle.map (SquareKit.SheafGroupoid.Bibundle.map f g) h ≫ (associator P' Q' R').hom =
      (associator P Q R).hom ≫ SquareKit.SheafGroupoid.Bibundle.map f (SquareKit.SheafGroupoid.Bibundle.map g h) := by
  apply triple_map_ext P Q R
  intro x m p k q l r
  change (associator P' Q' R').hom.hom.app (point L G.objects x l)
      ((mapFamily (SquareKit.SheafGroupoid.Bibundle.map f g) h).app (point L G.objects x l) _) =
    (mapFamily f (SquareKit.SheafGroupoid.Bibundle.map g h)).app (point L G.objects x l)
      ((associator P Q R).hom.hom.app (point L G.objects x l) _)
  simp only [SquareKit.SheafGroupoid.Bibundle.map, mapFamily_tensorPoint, associator_tensorPoint]

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K : Operations J} [G.Laws] [H.Laws] [K.Laws]
variable (P : Bibundle G H)

theorem rightUnitor_identityPoint (x : G.objects.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x m) :
    (rightUnitor P).hom.hom.app (point H G.objects x m)
      (tensorPoint P.right (identity H).right (identity H).left x m p m (identityPoint m)) = p := by
  have he := congrArg (fun f : P ⟶ P => f.hom.app (point H G.objects x m) p)
    (rightUnitor P).inv_hom_id
  exact (congrArg ((rightUnitor P).hom.hom.app (point H G.objects x m))
    (rightUnitFamily_pair P x m p).symm).trans he

theorem leftUnitor_identityPoint (x : G.objects.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x m) :
    (leftUnitor P).hom.hom.app (point H G.objects x m)
      (tensorPoint (identity G).right P.right P.left x ⟨x.val⟩
        (identityPoint (⟨x.val⟩ : G.Section x.obj)) m p) = p := by
  have he := congrArg (fun f : P ⟶ P => f.hom.app (point H G.objects x m) p)
    (leftUnitor P).inv_hom_id
  exact (congrArg ((leftUnitor P).hom.hom.app (point H G.objects x m))
    (leftUnitFamily_pair P x m p).symm).trans he

theorem triangle (Q : Bibundle H K) :
    (associator P (identity H) Q).hom ≫
      SquareKit.SheafGroupoid.Bibundle.map (SquareKit.SheafGroupoid.Bibundle.Map.ident P) (leftUnitor Q).hom =
    SquareKit.SheafGroupoid.Bibundle.map (rightUnitor P).hom (SquareKit.SheafGroupoid.Bibundle.Map.ident Q) := by
  apply (cancel_epi (show tensor P Q ⟶ tensor (tensor P (identity H)) Q from
    SquareKit.SheafGroupoid.Bibundle.map (rightUnitInverse P) (SquareKit.SheafGroupoid.Bibundle.Map.ident Q))).mp
  apply tensor_map_ext
  intro x m p k q
  change (mapFamily (SquareKit.SheafGroupoid.Bibundle.Map.ident P) (leftUnitor Q).hom).app (point K G.objects x k)
      ((associator P (identity H) Q).hom.hom.app (point K G.objects x k)
        ((mapFamily (rightUnitInverse P) (SquareKit.SheafGroupoid.Bibundle.Map.ident Q)).app (point K G.objects x k) _)) =
    (mapFamily (rightUnitor P).hom (SquareKit.SheafGroupoid.Bibundle.Map.ident Q)).app (point K G.objects x k)
      ((mapFamily (rightUnitInverse P) (SquareKit.SheafGroupoid.Bibundle.Map.ident Q)).app (point K G.objects x k) _)
  simp only [mapFamily_tensorPoint, rightUnitInverse, rightUnitFamily_pair,
    associator_tensorPoint, rightUnitor_identityPoint]
  change tensorPoint P.right Q.right Q.left x m p k
    ((leftUnitor Q).hom.hom.app (point K H.objects (atSection m) k)
      (tensorPoint (identity H).right Q.right Q.left (atSection m) m (identityPoint m) k q)) =
    tensorPoint P.right Q.right Q.left x m p k q
  exact congrArg (tensorPoint P.right Q.right Q.left x m p k)
    (leftUnitor_identityPoint Q (atSection m) k q)

end SquareKit.SheafGroupoid.Bibundle
