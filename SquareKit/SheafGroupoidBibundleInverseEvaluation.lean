import SquareKit.SheafGroupoidBibundleLeftPrincipal
import SquareKit.SheafGroupoidBibundleTensor

/-! Balanced evaluation into the identity bibundle. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bundle.BalancedFactorization SquareKit.SheafGroupoid.Bundle.BalancedAction SquareKit.SheafGroupoid.Bundle.BalancedProduct
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

variable (hP : LeftPrincipal P)

def identityFiber {U : Cᵒᵖ} {x y : G.Section U} (g : y ⟶ x) :
    Fiber G G.objects (identity G).right.family (atSection x) y :=
  (regularFiberEquiv G (identityObject G) (atSection x) y).symm g

theorem identityFiber_arrow {U : Cᵒᵖ} {x y : G.Section U} (g : y ⟶ x) :
    regularFiberEquiv G (identityObject G) (atSection x) y (identityFiber g) = g :=
  Equiv.apply_symm_apply _ g

theorem identityFiber_natural {U V : Cᵒᵖ} (f : U ⟶ V)
    {x y : G.Section U} (g : y ⟶ x) :
    (identity G).right.family.family.map
      (pointArrow G G.objects (ElementFamilies.along G.objects.obj f x.val) y) (identityFiber g) =
      identityFiber ((G.sectionRestriction f).map g) := by
  apply (regularFiberEquiv G (identityObject G) (atSection (x.restrict G f)) (y.restrict G f)).injective
  apply Operations.Arrow.ext
  exact ((regularFiberEquiv_natural_map G (identityObject G)
    (ElementFamilies.along G.objects.obj f x.val) y (identityFiber g)).trans
    (congrArg (fun a : y ⟶ x => (sectionParameter J).map f.unop ≫ a.map)
      (identityFiber_arrow g))).trans
    ((Operations.SectionArrow.restrict_map G f g).symm.trans
    (congrArg (fun a => a.map) (identityFiber_arrow ((G.sectionRestriction f).map g))).symm)

def evaluationRaw : ordinarySource P.right (opposite P hP).right ⟶
    SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right := ⟨{
  app U := ↾fun z => by
    rcases z with ⟨⟨⟨x,k⟩,p⟩,⟨⟨⟨k',y⟩,q⟩,e⟩⟩
    change k' = k at e
    subst k'
    exact ⟨(x,y), identityFiber (leftConnector P hP q p)⟩
  naturality := by
    intro U V f
    ext z
    rcases z with ⟨⟨⟨x,k⟩,p⟩,⟨⟨⟨k',y⟩,q⟩,e⟩⟩
    change k' = k at e
    subst k'
    change (⟨(G.objects.obj.map f x, G.objects.obj.map f y),
      identityFiber (leftConnector P hP
        (P.right.family.family.map (pointArrow H G.objects (ElementFamilies.along G.objects.obj f y) ⟨k⟩) q)
        (P.right.family.family.map (pointArrow H G.objects (ElementFamilies.along G.objects.obj f x) ⟨k⟩) p))⟩ :
      (SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right).obj.obj V) =
      ⟨(G.objects.obj.map f x, G.objects.obj.map f y),
        ((identity G).right.family.family.map
          (pointArrow G G.objects (ElementFamilies.along G.objects.obj f x) ⟨y⟩)
            (identityFiber (leftConnector P hP q p)))⟩
    exact congrArg (fun t => (⟨(G.objects.obj.map f x, G.objects.obj.map f y),t⟩ :
      (SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right).obj.obj V))
      ((identityFiber_natural f (leftConnector P hP q p)).trans
        (congrArg (fun a => identityFiber a) (leftConnector_natural P hP f q p))).symm }⟩

theorem evaluationRaw_pair {U : Cᵒᵖ} (x : G.Section U) (k : H.Section U)
    (p : Fiber H G.objects P.right.family (atSection x) k) (y : G.Section U)
    (q : Fiber H G.objects P.right.family (atSection y) k) :
    (evaluationRaw P hP).hom.app U (pairPoint P.right (opposite P hP).right (atSection x) k p y q) =
      ⟨(x.val,y.val),identityFiber (leftConnector P hP q p)⟩ := rfl

theorem leftConnector_balancing {U : Cᵒᵖ} {x y : G.Section U} {m n : H.Section U}
    (h : n ⟶ m) (p : Fiber H G.objects P.right.family (atSection x) m)
    (q : Fiber H G.objects P.right.family (atSection y) n) :
    leftConnector P hP q (P.right.act (atSection x) h p) =
      leftConnector P hP (P.right.act (atSection y) (Groupoid.inv h) q) p := by
  have hc : P.right.act (atSection y) h (P.right.act (atSection y) (Groupoid.inv h) q) = q := by
    rw [← P.right.act_comp, Groupoid.comp_inv, P.right.act_id]
  have he := leftConnector_rightAct P hP h (P.right.act (atSection y) (Groupoid.inv h) q) p
  rw [hc] at he
  exact he

theorem evaluationRaw_balanced : IsBalanced P.right (opposite P hP).right (opposite P hP).left
    (evaluationRaw P hP) := by
  intro x m n h p k q
  change (⟨(x.val,k.val),identityFiber (leftConnector P hP (x := k) (y := ⟨x.val⟩) q (P.right.act x h p))⟩ :
      (SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right).obj.obj x.obj) =
    ⟨(x.val,k.val),identityFiber (leftConnector P hP (x := k) (y := ⟨x.val⟩) (P.right.act (atSection k) (Groupoid.inv h) q) p)⟩
  exact congrArg (fun a => (⟨(x.val,k.val),identityFiber a⟩ :
    (SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right).obj.obj x.obj)) (leftConnector_balancing P hP (x := ⟨x.val⟩) (y := k) h p q)

def evaluationTotal : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (tensor P (opposite P hP)).right ⟶
    SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right :=
  balancedDesc P.right (opposite P hP).right (opposite P hP).left
    (evaluationRaw P hP) (evaluationRaw_balanced P hP)

theorem evaluationTotal_fac : balancedMap P.right (opposite P hP).right (opposite P hP).left ≫
    evaluationTotal P hP = evaluationRaw P hP := balancedDesc_fac _ _ _ _ _

theorem evaluationTotal_projection : evaluationTotal P hP ≫ SplitSheaf.p (identity G).right.family =
    SplitSheaf.p (tensor P (opposite P hP)).right.family := by
  apply (cancel_epi (balancedMap P.right (opposite P hP).right (opposite P hP).left)).mp
  rw [← Category.assoc, evaluationTotal_fac]
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,k⟩,p⟩,⟨⟨⟨k',y⟩,q⟩,e⟩⟩
  change k' = k at e
  subst k'
  exact (congrArg Sigma.fst (balancedMap_pair P.right (opposite P hP).right (opposite P hP).left
    (atSection (⟨x⟩ : G.Section U)) ⟨k⟩ p ⟨y⟩ q)).symm

def evaluationFamily : (tensor P (opposite P hP)).right.family.family ⟶ (identity G).right.family.family :=
  SplitSheaf.mapOfTotal (evaluationTotal P hP) (evaluationTotal_projection P hP)

theorem evaluationFamily_fac : balancedMap P.right (opposite P hP).right (opposite P hP).left ≫
    SplitSheaf.totalMap (evaluationFamily P hP) = evaluationRaw P hP := by
  unfold evaluationFamily
  rw [SplitSheaf.totalMap_mapOfTotal, evaluationTotal_fac]

theorem evaluationFamily_tensorPoint {U : Cᵒᵖ} (x : G.Section U) (k : H.Section U)
    (p : Fiber H G.objects P.right.family (atSection x) k) (y : G.Section U)
    (q : Fiber H G.objects P.right.family (atSection y) k) :
    (evaluationFamily P hP).app (point G G.objects (atSection x) y)
      (tensorPoint P.right (opposite P hP).right (opposite P hP).left (atSection x) k p y q) =
      identityFiber (leftConnector P hP q p) := by
  have he := congrArg (fun a : ordinarySource P.right (opposite P hP).right ⟶
      SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (identity G).right =>
    a.hom.app U (pairPoint P.right (opposite P hP).right (atSection x) k p y q))
    (evaluationFamily_fac P hP)
  exact eq_of_heq (Sigma.mk.inj_iff.mp (he.trans (evaluationRaw_pair P hP x k p y q))).2

end SquareKit.SheafGroupoid.Bibundle
