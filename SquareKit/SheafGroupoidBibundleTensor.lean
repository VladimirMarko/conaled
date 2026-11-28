import SquareKit.SheafGroupoidBibundle
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! Balanced composition of principal bibundles and their maps. -/
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
variable {G H K : Operations J} [G.Laws] [H.Laws] [K.Laws]

def tensor (P : Bibundle G H) (Q : Bibundle H K) : Bibundle G K where
  right := compositionRightBundle P.right Q.right Q.left
  left := compositionLeftAction P.right P.left Q.right Q.left

variable {P P' P'' : Bibundle G H} {Q Q' Q'' : Bibundle H K}
variable (f : SquareKit.SheafGroupoid.Bibundle.Map P P') (g : SquareKit.SheafGroupoid.Bibundle.Map Q Q')

def rawBoth : ordinarySource P.right Q.right ⟶ ordinarySource P'.right Q'.right :=
  (ordinary_pullback P'.right Q'.right).lift
    (ordinaryFirst P.right Q.right ≫ g.toMap.totalMap)
    (ordinarySecond P.right Q.right ≫ f.toMap.totalMap) (by
      apply Sheaf.hom_ext
      ext U z
      rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
      change h' = h at e
      subst h'
      rfl)

theorem rawBoth_pair (x : G.objects.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.right.family (atSection m) k) :
    (rawBoth f g).hom.app x.obj (pairPoint P.right Q.right x m p k q) =
      pairPoint P'.right Q'.right x m (f.hom.app (point H G.objects x m) p) k
        (g.hom.app (point K H.objects (atSection m) k) q) := by
  apply Types.ext_of_isPullback
    (SheafImage.sections_isPullback (ordinary_pullback P'.right Q'.right) x.obj)
  · exact congrArg (fun a : ordinarySource P.right Q.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total Q'.right =>
      a.hom.app x.obj (pairPoint P.right Q.right x m p k q))
        ((ordinary_pullback P'.right Q'.right).lift_fst _ _ _)
  · exact congrArg (fun a : ordinarySource P.right Q.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P'.right =>
      a.hom.app x.obj (pairPoint P.right Q.right x m p k q))
        ((ordinary_pullback P'.right Q'.right).lift_snd _ _ _)

theorem rawBoth_balanced : IsBalanced P.right Q.right Q.left
    (rawBoth f g ≫ balancedMap P'.right Q'.right Q'.left) := by
  intro x m n h p k q
  change (balancedMap P'.right Q'.right Q'.left).hom.app x.obj
    ((rawBoth f g).hom.app x.obj _) =
    (balancedMap P'.right Q'.right Q'.left).hom.app x.obj ((rawBoth f g).hom.app x.obj _)
  rw [rawBoth_pair, rawBoth_pair, f.equivariant, g.left_equivariant]
  exact balancedMap_balancing P'.right Q'.right Q'.left x h _ k _

def mapTotal : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor P Q).right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor P' Q').right :=
  balancedDesc P.right Q.right Q.left
    (rawBoth f g ≫ balancedMap P'.right Q'.right Q'.left) (rawBoth_balanced f g)

theorem mapTotal_fac : balancedMap P.right Q.right Q.left ≫ mapTotal f g =
    rawBoth f g ≫ balancedMap P'.right Q'.right Q'.left := balancedDesc_fac _ _ _ _ _

theorem mapTotal_projection : mapTotal f g ≫ SplitSheaf.p (tensor P' Q').right.family =
    SplitSheaf.p (tensor P Q).right.family := by
  apply (cancel_epi (balancedMap P.right Q.right Q.left)).mp
  rw [← Category.assoc, mapTotal_fac]
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  exact congrArg Sigma.fst ((congrArg ((balancedMap P'.right Q'.right Q'.left).hom.app U)
    (rawBoth_pair f g (G.objects.obj.elementsMk U x) ⟨h⟩ p ⟨k⟩ q)).trans
      (balancedMap_pair P'.right Q'.right Q'.left (G.objects.obj.elementsMk U x) ⟨h⟩ _ ⟨k⟩ _))

def mapFamily : (tensor P Q).right.family.family ⟶ (tensor P' Q').right.family.family :=
  SplitSheaf.mapOfTotal (mapTotal f g) (mapTotal_projection f g)

theorem mapFamily_fac : balancedMap P.right Q.right Q.left ≫ SplitSheaf.totalMap (mapFamily f g) =
    rawBoth f g ≫ balancedMap P'.right Q'.right Q'.left := by
  unfold mapFamily
  rw [SplitSheaf.totalMap_mapOfTotal, mapTotal_fac]

theorem mapFamily_tensorPoint (x : G.objects.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H G.objects P.right.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.right.family (atSection m) k) :
    (mapFamily f g).app (point K G.objects x k)
      (tensorPoint P.right Q.right Q.left x m p k q) =
    tensorPoint P'.right Q'.right Q'.left x m (f.hom.app (point H G.objects x m) p) k
      (g.hom.app (point K H.objects (atSection m) k) q) := by
  have he := congrArg (fun a : ordinarySource P.right Q.right ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor P' Q').right =>
    a.hom.app x.obj (pairPoint P.right Q.right x m p k q)) (mapFamily_fac f g)
  have hp := (congrArg ((balancedMap P'.right Q'.right Q'.left).hom.app x.obj)
    (rawBoth_pair f g x m p k q)).trans
      (balancedMap_pair P'.right Q'.right Q'.left x m _ k _)
  exact eq_of_heq (Sigma.mk.inj_iff.mp (he.trans hp)).2

theorem mapFamily_equivariant (x : G.objects.obj.Elements) {k l : K.Section x.obj}
    (a : k ⟶ l) (t : Fiber K G.objects (tensor P Q).right.family x l) :
    (mapFamily f g).app (point K G.objects x k) ((tensor P Q).right.act x a t) =
    (tensor P' Q').right.act x a ((mapFamily f g).app (point K G.objects x l) t) := by
  apply equivariant_of_local_points (cover P.right) (tensor P Q).right.toAction
    (tensor P' Q').right.toAction (mapFamily f g) ?_ x a t
  intro z b k l a t
  let m := coverAnchor P.right z b
  let p := coverPoint P.right z b
  let b' : (cover P.right).family.obj z := ⟨⟨(z.val,m.val),p⟩,rfl⟩
  let q := Descent.evaluationEquiv (compositionDatum P.right Q.right Q.left) z b' l t
  have ht : tensorPoint P.right Q.right Q.left z m p l q = t := Equiv.symm_apply_apply _ t
  change (mapFamily f g).app _ ((compositionRightBundle P.right Q.right Q.left).act z a t) = _
  rw [← ht, ← tensorPoint_equivariant, mapFamily_tensorPoint, mapFamily_tensorPoint,
    g.equivariant]
  exact tensorPoint_equivariant P'.right Q'.right Q'.left z m _ a _

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K : Operations J} [G.Laws] [H.Laws] [K.Laws]
variable {P P' P'' : Bibundle G H} {Q Q' Q'' : Bibundle H K}
variable (f : SquareKit.SheafGroupoid.Bibundle.Map P P') (g : SquareKit.SheafGroupoid.Bibundle.Map Q Q')

theorem mapFamily_left_equivariant {U : Cᵒᵖ} {x y : G.Section U} (a : x ⟶ y)
    (k : K.Section U) (t : Fiber K G.objects (tensor P Q).right.family (atSection x) k) :
    (mapFamily f g).app (point K G.objects (atSection y) k) ((tensor P Q).left.act a k t) =
    (tensor P' Q').left.act a k ((mapFamily f g).app (point K G.objects (atSection x) k) t) := by
  apply SplitSheafDescent.fiber_ext (tensor P' Q').right.family
    (point K G.objects (atSection y) k)
    (Presheaf.imageSieve P.right.toAction.projection.hom x.val)
    (Presheaf.imageSieve_mem J P.right.toAction.projection.hom x.val)
  rintro V j ⟨⟨⟨z,m⟩,p⟩,hp⟩
  change V ⟶ unop U at j
  change z = G.objects.obj.map j.op x.val at hp
  subst z
  change Fiber H G.objects P.right.family (atSection (x.restrict G j.op)) ⟨m⟩ at p
  rw [← NatTrans.naturality_apply (mapFamily f g)]
  change (mapFamily f g).app _
    ((tensor P Q).right.family.family.map _ (residualAct Q.right Q.left P.right P.left a k t)) =
    (tensor P' Q').right.family.family.map _
      (residualAct Q'.right Q'.left P'.right P'.left a k ((mapFamily f g).app _ t))
  change (mapFamily f g).app _
    ((compositionRightBundle P.right Q.right Q.left).family.family.map (pointArrow K G.objects
      (ElementFamilies.along G.objects.obj j.op y.val) k)
        (residualAct Q.right Q.left P.right P.left a k t)) =
    (compositionRightBundle P'.right Q'.right Q'.left).family.family.map (pointArrow K G.objects
      (ElementFamilies.along G.objects.obj j.op y.val) k)
        (residualAct Q'.right Q'.left P'.right P'.left a k ((mapFamily f g).app _ t))
  rw [residualAct_natural, residualAct_natural]
  refine Eq.trans ?_ (congrArg
    (residualAct Q'.right Q'.left P'.right P'.left ((G.sectionRestriction j.op).map a)
      (k.restrict K j.op))
    (NatTrans.naturality_apply (mapFamily f g)
      (pointArrow K G.objects (ElementFamilies.along G.objects.obj j.op x.val) k) t))
  let x' := atSection (x.restrict G j.op)
  let k' := k.restrict K j.op
  let t' := (tensor P Q).right.family.family.map (pointArrow K G.objects
    (ElementFamilies.along G.objects.obj j.op x.val) k) t
  let b : (cover P.right).family.obj x' := ⟨⟨(x'.val,m),p⟩,rfl⟩
  let q : Fiber K H.objects Q.right.family (atSection (⟨m⟩ : H.Section (op V))) k' :=
    Descent.evaluationEquiv (compositionDatum P.right Q.right Q.left) x' b k' t'
  have ht : tensorPoint P.right Q.right Q.left x' ⟨m⟩ p k' q = t' := Equiv.symm_apply_apply _ t'
  change (mapFamily f g).app _
    (residualAct Q.right Q.left P.right P.left ((G.sectionRestriction j.op).map a) k' t') =
    residualAct Q'.right Q'.left P'.right P'.left ((G.sectionRestriction j.op).map a) k'
      ((mapFamily f g).app _ t')
  rw [← ht]
  let a' := (G.sectionRestriction j.op).map a
  calc
    _ = (mapFamily f g).app _
      (tensorPoint P.right Q.right Q.left (atSection (y.restrict G j.op)) ⟨m⟩
        (P.left.act a' ⟨m⟩ p) k' q) :=
      congrArg ((mapFamily f g).app _) (residualAct_tensorPoint Q.right Q.left P.right P.left a' ⟨m⟩ p k' q)
    _ = tensorPoint P'.right Q'.right Q'.left (atSection (y.restrict G j.op)) ⟨m⟩
      (f.hom.app _ (P.left.act a' ⟨m⟩ p)) k' (g.hom.app _ q) :=
      mapFamily_tensorPoint f g _ _ _ _ _
    _ = tensorPoint P'.right Q'.right Q'.left (atSection (y.restrict G j.op)) ⟨m⟩
      (P'.left.act a' ⟨m⟩ (f.hom.app _ p)) k' (g.hom.app _ q) :=
      congrArg (fun p => tensorPoint P'.right Q'.right Q'.left
        (atSection (y.restrict G j.op)) ⟨m⟩ p k'
        (g.hom.app (point K H.objects (atSection (⟨m⟩ : H.Section (op V))) k') q))
        (f.left_equivariant a' ⟨m⟩ p)
    _ = residualAct Q'.right Q'.left P'.right P'.left a' k'
      (tensorPoint P'.right Q'.right Q'.left x' ⟨m⟩ (f.hom.app _ p) k' (g.hom.app _ q)) :=
      (residualAct_tensorPoint Q'.right Q'.left P'.right P'.left a' ⟨m⟩ _ k' _).symm
    _ = _ := congrArg (residualAct Q'.right Q'.left P'.right P'.left a' k')
      (mapFamily_tensorPoint f g x' ⟨m⟩ p k' q).symm

def map : SquareKit.SheafGroupoid.Bibundle.Map (tensor P Q) (tensor P' Q') where
  hom := mapFamily f g
  equivariant x _ _ a t := mapFamily_equivariant f g x a t
  left_equivariant a k t := mapFamily_left_equivariant f g a k t

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K : Operations J} [G.Laws] [H.Laws] [K.Laws]
variable {P P' P'' : Bibundle G H} {Q Q' Q'' : Bibundle H K}

theorem tensor_map_ext {T : Bibundle G K} (a b : SquareKit.SheafGroupoid.Bibundle.Map (tensor P Q) T)
    (h : ∀ (x : G.objects.obj.Elements) (m : H.Section x.obj)
      (p : Fiber H G.objects P.right.family x m) (k : K.Section x.obj)
      (q : Fiber K H.objects Q.right.family (atSection m) k),
      a.hom.app (point K G.objects x k) (tensorPoint P.right Q.right Q.left x m p k q) =
      b.hom.app (point K G.objects x k) (tensorPoint P.right Q.right Q.left x m p k q)) : a = b := by
  apply SquareKit.SheafGroupoid.Bibundle.Map.ext
  apply Bundle.Map.ext
  apply SplitSheaf.totalMap_injective
  apply (cancel_epi (balancedMap P.right Q.right Q.left)).mp
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,m⟩,p⟩,⟨⟨⟨m',k⟩,q⟩,e⟩⟩
  change m' = m at e
  subst m'
  exact congrArg (Sigma.mk (x,k)) (h (G.objects.obj.elementsMk U x) ⟨m⟩ p ⟨k⟩ q)

theorem map_id (P : Bibundle G H) (Q : Bibundle H K) :
    map (SquareKit.SheafGroupoid.Bibundle.Map.ident P) (SquareKit.SheafGroupoid.Bibundle.Map.ident Q) =
      SquareKit.SheafGroupoid.Bibundle.Map.ident (tensor P Q) := by
  apply tensor_map_ext
  intro x m p k q
  exact mapFamily_tensorPoint (SquareKit.SheafGroupoid.Bibundle.Map.ident P) (SquareKit.SheafGroupoid.Bibundle.Map.ident Q) x m p k q

theorem map_comp (f : SquareKit.SheafGroupoid.Bibundle.Map P P') (f' : SquareKit.SheafGroupoid.Bibundle.Map P' P'')
    (g : SquareKit.SheafGroupoid.Bibundle.Map Q Q') (g' : SquareKit.SheafGroupoid.Bibundle.Map Q' Q'') :
    map (f.comp f') (g.comp g') = (map f g).comp (map f' g') := by
  apply tensor_map_ext
  intro x m p k q
  change (mapFamily (f.comp f') (g.comp g')).app _ _ =
    (mapFamily f' g').app _ ((mapFamily f g).app _ _)
  rw [mapFamily_tensorPoint, mapFamily_tensorPoint, mapFamily_tensorPoint]
  rfl

end SquareKit.SheafGroupoid.Bibundle
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory SquareKit.SheafGroupoid SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G H K : Operations J) [G.Laws] [H.Laws] [K.Laws]
def tensorFunctor : (Bibundle G H × Bibundle H K) ⥤ Bibundle G K where
  obj a := tensor a.1 a.2
  map f := map f.1 f.2
  map_id a := map_id a.1 a.2
  map_comp f g := map_comp f.1 g.1 f.2 g.2
end SquareKit.SheafGroupoid.Bibundle
