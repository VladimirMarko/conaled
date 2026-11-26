import SquareKit.SheafFamilyTopology
import SquareKit.SheafTorsorStack
import SquareKit.SheafActionQuotientStack
import SquareKit.SheafActionQuotientCoproduct
import SquareKit.SheafFamilyDescentCore

/-! Family descent for the existing torsor and action-quotient pseudofunctors. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafFamilyDescent
open CategoryTheory Limits Opposite
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Torsor product restriction is proved by the actual coproduct construction. -/
theorem torsor_effectiveCoproducts (G : Sheaf J GrpCat.{max u v}) :
    CoproductDescent.EffectiveCoproducts.{max u v} (SheafTorsor.Stack.pseudofunctor G) := by
  intro I Y c hc
  apply CoproductDescent.restriction_isEquivalence_of_chosen_coproducts _ _ c hc
  intro Y
  change (SheafTorsor.Coproduct.restrict (G := G) (Y := Y)).IsEquivalence
  infer_instance

/-- Quotient product restriction retains target maps and stabilizer arrows. -/
theorem quotient_effectiveCoproducts {G : Sheaf J GrpCat.{max u v}}
    {M : Sheaf J (Type (max u v))} (a : SheafActionQuotient.Action G M) :
    CoproductDescent.EffectiveCoproducts.{max u v} (SheafActionQuotient.Stack.pseudofunctor a) := by
  intro I Y c hc
  apply CoproductDescent.restriction_isEquivalence_of_chosen_coproducts _ _ c hc
  intro Y
  change (SheafActionQuotient.Coproduct.restrict (a := a) (Y := Y)).IsEquivalence
  infer_instance

theorem torsor_isStackFor (G : Sheaf J GrpCat.{max u v})
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    (SheafTorsor.Stack.pseudofunctor G).IsStackFor (Presieve.ofArrows Y f) :=
  isStackFor_joint _ (torsor_effectiveCoproducts G)
    (fun f h => by have := h; exact SheafTorsor.Stack.isStackFor_cover f) f hf

theorem quotient_isStackFor {G : Sheaf J GrpCat.{max u v}}
    {M : Sheaf J (Type (max u v))} (a : SheafActionQuotient.Action G M)
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    (SheafActionQuotient.Stack.pseudofunctor a).IsStackFor (Presieve.ofArrows Y f) :=
  isStackFor_joint _ (quotient_effectiveCoproducts a)
    (fun f h => by have := h; exact SheafActionQuotient.Stack.isStackFor_cover a f) f hf

instance torsor_isPrestack (G : Sheaf J GrpCat.{max u v}) :
    (SheafTorsor.Stack.pseudofunctor G).IsPrestack (SheafFamilyCover.topology (J := J)) :=
  isPrestack_of_joint _ (torsor_isStackFor G)

instance torsor_isStack (G : Sheaf J GrpCat.{max u v}) :
    (SheafTorsor.Stack.pseudofunctor G).IsStack (SheafFamilyCover.topology (J := J)) :=
  isStack_of_joint _ (torsor_isStackFor G)

instance quotient_isPrestack {G : Sheaf J GrpCat.{max u v}}
    {M : Sheaf J (Type (max u v))} (a : SheafActionQuotient.Action G M) :
    (SheafActionQuotient.Stack.pseudofunctor a).IsPrestack (SheafFamilyCover.topology (J := J)) :=
  isPrestack_of_joint _ (quotient_isStackFor a)

instance quotient_isStack {G : Sheaf J GrpCat.{max u v}}
    {M : Sheaf J (Type (max u v))} (a : SheafActionQuotient.Action G M) :
    (SheafActionQuotient.Stack.pseudofunctor a).IsStack (SheafFamilyCover.topology (J := J)) :=
  isStack_of_joint _ (quotient_isStackFor a)

/-- The family recovery functor includes all compatible torsor arrows. -/
def torsorEquivalence (G : Sheaf J GrpCat.{max u v})
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    SheafTorsor.Torsor G X ≌ (SheafTorsor.Stack.pseudofunctor G).DescentData f := by
  have := ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
    (torsor_isStackFor G f hf)
  exact ((SheafTorsor.Stack.pseudofunctor G).toDescentData f).asEquivalence

/-- Quotient recovery preserves actual target maps and stabilizer arrows. -/
def quotientEquivalence {G : Sheaf J GrpCat.{max u v}}
    {M : Sheaf J (Type (max u v))} (a : SheafActionQuotient.Action G M)
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    SheafActionQuotient.Object a X ≌ (SheafActionQuotient.Stack.pseudofunctor a).DescentData f := by
  have := ((SheafActionQuotient.Stack.pseudofunctor a).isStackFor_ofArrows_iff _).mp
    (quotient_isStackFor a f hf)
  exact ((SheafActionQuotient.Stack.pseudofunctor a).toDescentData f).asEquivalence

/-- The family recovery of singleton data agrees with the original constructive torsor glue. -/
def torsorSingletonComparison (G : Sheaf J GrpCat.{max u v})
    {X : Sheaf J (Type (max u v))} (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (D : SheafTorsor.Stack.Data (G := G) A) :
    (singletonEquivalence (SheafTorsor.Stack.pseudofunctor G) (SplitSheaf.p A)).inverse.obj D ≅
        SheafTorsor.Stack.glue D := by
  let e := singletonEquivalence (SheafTorsor.Stack.pseudofunctor G) (SplitSheaf.p A)
  exact e.functor.preimageIso (e.counitIso.app D ≪≫ (SheafTorsor.Stack.localComparison D).symm)

/-- Singleton quotient recovery agrees with the original glue, including its target map. -/
def quotientSingletonComparison {G : Sheaf J GrpCat.{max u v}}
    {M : Sheaf J (Type (max u v))} (a : SheafActionQuotient.Action G M)
    {X : Sheaf J (Type (max u v))} (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (D : SheafActionQuotient.Stack.Data a A) :
    (singletonEquivalence (SheafActionQuotient.Stack.pseudofunctor a) (SplitSheaf.p A)).inverse.obj D ≅
        SheafActionQuotient.Stack.glue D := by
  let e := singletonEquivalence (SheafActionQuotient.Stack.pseudofunctor a) (SplitSheaf.p A)
  exact e.functor.preimageIso (e.counitIso.app D ≪≫ (SheafActionQuotient.Stack.localComparison D).symm)

end SquareKit.SheafFamilyDescent
