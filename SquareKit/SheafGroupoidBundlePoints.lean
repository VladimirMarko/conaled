import SquareKit.SheafGroupoidBundleLocal

/-! Regular bundle maps from generalized points and their extensionality. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H : Operations J} [H.Laws] {X : Sheaf J (Type (max u v))}
variable (P : Principal H X) (k : H.Object X)

abbrev PointTerm := SplitSheaf.Tm (SplitSheaf.tySub P.family (SheafRelation.lift (𝟙 X) k.map))

def pointMap (t : PointTerm P k) : regular H k ⟶ P :=
  (localMap P).reindex (SplitSheaf.pair P.family (SheafRelation.lift (𝟙 X) k.map) t)

theorem pointMap_identity (t : PointTerm P k) (z : X.obj.Elements) :
    (pointMap P k t).hom.app (point H X z (value H k z)) (regularIdentity H k z) = t.val z := by
  change P.act z (regularFiberEquiv H k z (value H k z) (regularIdentity H k z)) (t.val z) = _
  rw [regularFiberEquiv_identity, P.act_id]

theorem regularMap_ext {f g : regular H k ⟶ P}
    (h : ∀ z : X.obj.Elements, f.hom.app (point H X z (value H k z)) (regularIdentity H k z) =
      g.hom.app (point H X z (value H k z)) (regularIdentity H k z)) : f = g := by
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro t
  let x := X.obj.elementsMk z.obj z.val.1
  let a : H.Section z.obj := ⟨z.val.2⟩
  have hf := f.equivariant x (regularFiberEquiv H k x a t) (regularIdentity H k x)
  have hg := g.equivariant x (regularFiberEquiv H k x a t) (regularIdentity H k x)
  have hi : (regular H k).act x (regularFiberEquiv H k x a t) (regularIdentity H k x) = t := by
    change (regularFiberEquiv H k x a).symm
      (regularFiberEquiv H k x a t ≫ regularFiberEquiv H k x (value H k x) (regularIdentity H k x)) = t
    rw [regularFiberEquiv_identity, Category.comp_id, Equiv.symm_apply_apply]
  rw [hi] at hf hg
  exact hf.trans ((congrArg (P.act x (regularFiberEquiv H k x a t)) (h x)).trans hg.symm)

end SquareKit.SheafGroupoid.Bundle
