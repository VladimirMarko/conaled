import SquareKit.SheafGroupoidBibundleInverseEvaluation

/-! Equivariance of balanced evaluation and its derived inverse. -/
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

theorem left_equivariant_of_cover {R S : Bibundle G H}
    (A : SplitSheaf.Ty G.objects) [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (f : R.right.family.family ⟶ S.right.family.family)
    (hf : ∀ {U : Cᵒᵖ} (x : G.Section U), A.family.obj (atSection x) →
      ∀ {y : G.Section U} (g : x ⟶ y) (k : H.Section U)
        (t : Fiber H G.objects R.right.family (atSection x) k),
        f.app (point H G.objects (atSection y) k) (R.left.act g k t) =
          S.left.act g k (f.app (point H G.objects (atSection x) k) t))
    {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y) (k : H.Section U)
    (t : Fiber H G.objects R.right.family (atSection x) k) :
    f.app (point H G.objects (atSection y) k) (R.left.act g k t) =
      S.left.act g k (f.app (point H G.objects (atSection x) k) t) := by
  apply SplitSheafDescent.fiber_ext S.right.family (point H G.objects (atSection y) k)
    (Presheaf.imageSieve (SplitSheaf.p A).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x.val)
  rintro V j ⟨⟨z,a⟩,hz⟩
  change V ⟶ unop U at j
  change z = G.objects.obj.map j.op x.val at hz
  subst z
  rw [← NatTrans.naturality_apply f]
  change f.app _ (R.right.family.family.map
    (pointArrow H G.objects (ElementFamilies.along G.objects.obj j.op y.val) k) (R.left.act g k t)) =
    S.right.family.family.map
      (pointArrow H G.objects (ElementFamilies.along G.objects.obj j.op y.val) k)
      (S.left.act g k (f.app _ t))
  rw [R.left.natural, S.left.natural]
  exact (hf (x.restrict G j.op) a ((G.sectionRestriction j.op).map g) (k.restrict H j.op)
    (R.right.family.family.map
      (pointArrow H G.objects (ElementFamilies.along G.objects.obj j.op x.val) k) t)).trans
    (congrArg (S.left.act ((G.sectionRestriction j.op).map g) (k.restrict H j.op))
      (NatTrans.naturality_apply f
        (pointArrow H G.objects (ElementFamilies.along G.objects.obj j.op x.val) k) t))

variable (hP : LeftPrincipal P)

theorem identityFiber_rightAct {U : Cᵒᵖ} {x y z : G.Section U} (g : y ⟶ x) (a : z ⟶ y) :
    (identity G).right.act (atSection x) a (identityFiber g) = identityFiber (a ≫ g) :=
  congrArg (fun b => identityFiber (a ≫ b)) (identityFiber_arrow g)

theorem identityFiber_leftAct {U : Cᵒᵖ} {x y z : G.Section U} (g : z ⟶ x) (a : x ⟶ y) :
    (identity G).left.act a z (identityFiber g) = identityFiber (g ≫ a) :=
  congrArg (fun b => identityFiber (b ≫ a)) (identityFiber_arrow g)

theorem evaluationFamily_equivariant (x : G.objects.obj.Elements) {k l : G.Section x.obj}
    (g : k ⟶ l) (t : Fiber G G.objects (tensor P (opposite P hP)).right.family x l) :
    (evaluationFamily P hP).app (point G G.objects x k) ((tensor P (opposite P hP)).right.act x g t) =
      (identity G).right.act x g ((evaluationFamily P hP).app (point G G.objects x l) t) := by
  apply equivariant_of_local_points (cover P.right) (tensor P (opposite P hP)).right.toAction
    (identity G).right.toAction (evaluationFamily P hP) ?_ x g t
  intro z a k l g t
  let m := coverAnchor P.right z a
  let p := coverPoint P.right z a
  let a' : (cover P.right).family.obj z := ⟨⟨(z.val,m.val),p⟩,rfl⟩
  let q : Fiber G H.objects (opposite P hP).right.family (atSection m) l :=
    Descent.evaluationEquiv (compositionDatum P.right (opposite P hP).right (opposite P hP).left) z a' l t
  have ht : tensorPoint P.right (opposite P hP).right (opposite P hP).left z m p l q = t :=
    Equiv.symm_apply_apply _ t
  rw [← ht]
  have he := tensorPoint_equivariant P.right (opposite P hP).right (opposite P hP).left z m p g q
  refine (congrArg ((evaluationFamily P hP).app (point G G.objects z k)) he.symm).trans ?_
  have hc := leftConnector_preact P hP (x := l) (y := ⟨z.val⟩) (z := k) (k := m) q p (Groupoid.inv g)
  have hi : Groupoid.inv (Groupoid.inv g) = g := by simp [Groupoid.inv_eq_inv]
  rw [hi] at hc
  exact (evaluationFamily_tensorPoint P hP (⟨z.val⟩ : G.Section z.obj) m p k
    (P.left.act (Groupoid.inv g) m q)).trans
      ((congrArg identityFiber hc).trans
        ((identityFiber_rightAct (leftConnector P hP (x := l) (y := ⟨z.val⟩) (k := m) q p) g).symm.trans
          (congrArg ((identity G).right.act z g)
            (evaluationFamily_tensorPoint P hP (⟨z.val⟩ : G.Section z.obj) m p l q).symm)))

theorem evaluationFamily_left_equivariant {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y)
    (k : G.Section U) (t : Fiber G G.objects (tensor P (opposite P hP)).right.family (atSection x) k) :
    (evaluationFamily P hP).app (point G G.objects (atSection y) k) ((tensor P (opposite P hP)).left.act g k t) =
      (identity G).left.act g k ((evaluationFamily P hP).app (point G G.objects (atSection x) k) t) := by
  apply left_equivariant_of_cover (cover P.right) (evaluationFamily P hP) ?_ g k t
  intro U x a y g k t
  let m := coverAnchor P.right (atSection x) a
  let p := coverPoint P.right (atSection x) a
  let a' : (cover P.right).family.obj (atSection x) := ⟨⟨(x.val,m.val),p⟩,rfl⟩
  let q := Descent.evaluationEquiv (compositionDatum P.right (opposite P hP).right (opposite P hP).left)
    (atSection x) a' k t
  have ht : tensorPoint P.right (opposite P hP).right (opposite P hP).left (atSection x) m p k q = t :=
    Equiv.symm_apply_apply _ t
  rw [← ht]
  change (evaluationFamily P hP).app _
    (residualAct (opposite P hP).right (opposite P hP).left P.right P.left g k _) = _
  rw [residualAct_tensorPoint, evaluationFamily_tensorPoint, evaluationFamily_tensorPoint,
    identityFiber_leftAct, leftConnector_postact]

def evaluation : tensor P (opposite P hP) ⟶ identity G where
  hom := evaluationFamily P hP
  equivariant x _ _ g t := evaluationFamily_equivariant P hP x g t
  left_equivariant g k t := evaluationFamily_left_equivariant P hP g k t

def evaluationIso : tensor P (opposite P hP) ≅ identity G := asIso (evaluation P hP)

end SquareKit.SheafGroupoid.Bibundle
