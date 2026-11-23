import SquareKit.SplitSheafStack
import SquareKit.SplitSheafCoproduct
import SquareKit.SheafFamilyDescentCore

/-! Effective family descent for sheaf displays and arbitrary fiber maps. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafDisplayFamilyDescent
open CategoryTheory Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Coproduct effectiveness follows from the actual assembled total sheaf. -/
theorem effectiveCoproducts :
    CoproductDescent.EffectiveCoproducts.{max u v} (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)) := by
  intro I Y c hc
  apply CoproductDescent.effectiveCoproducts_of_chosen _ _ c hc
  intro Y
  change (SplitSheafCoproduct.restrict (Y := Y)).IsEquivalence
  infer_instance

theorem isStackFor_joint
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).IsStackFor (Presieve.ofArrows Y f) :=
  SheafFamilyDescent.isStackFor_joint _ effectiveCoproducts
    (fun f h => by have := h; exact SplitSheafStack.isStackFor_cover f) f hf

instance isPrestack :
    (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).IsPrestack (SheafFamilyCover.topology (J := J)) :=
  SheafFamilyDescent.isPrestack_of_joint _ isStackFor_joint

instance isStack :
    (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).IsStack (SheafFamilyCover.topology (J := J)) :=
  SheafFamilyDescent.isStack_of_joint _ isStackFor_joint

def equivalence
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    SplitSheaf.Ty X ≌ (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).DescentData f := by
  have := ((SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).isStackFor_ofArrows_iff _).mp
    (isStackFor_joint f hf)
  exact ((SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).toDescentData f).asEquivalence

/-- Recovery can be presented as an ordinary display, retaining every map. -/
def overEquivalence
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    Over X ≌ (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).DescentData f :=
  SplitSheaf.overEquivalence.symm.trans (equivalence f hf)

/-- Chosen family recovery agrees with the independently constructed singleton glue. -/
def singletonComparison {X : Sheaf J (Type (max u v))} (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (SheafFamilyDescent.singletonEquivalence (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J))
      (SplitSheaf.p A)).inverse ≅ SplitSheafStack.glue (A := A) :=
  Iso.isoInverseOfIsoFunctor
    (G := SheafFamilyDescent.singletonEquivalence (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J))
      (SplitSheaf.p A)) (G' := SplitSheafStack.equivalence (A := A)) (Iso.refl _)


/-- Refinement and base change commute with recovery, naturally in all local maps. -/
def recoveryNaturality
    {S T : Sheaf J (Type (max u v))} {I K : Type (max u v)}
    {X : I → Sheaf J (Type (max u v))} {Y : K → Sheaf J (Type (max u v))}
    {f : ∀ i, X i ⟶ S} {g : ∀ k, Y k ⟶ T}
    (hf : SheafFamilyCover.JointlyLocallySurjective f)
    (hg : SheafFamilyCover.JointlyLocallySurjective g)
    (r : K → I) (p : T ⟶ S) (a : ∀ k, Y k ⟶ X (r k))
    (w : ∀ k, a k ≫ f (r k) = g k ≫ p) :
    Pseudofunctor.DescentData.pullFunctor (SplitSheaf.pseudofunctor (J := J)) w ⋙
      (equivalence g hg).inverse ≅ (equivalence f hf).inverse ⋙ SplitSheaf.restriction p := by
  have : ((SplitSheaf.pseudofunctor (J := J)).toDescentData f).IsEquivalence :=
    (equivalence f hf).isEquivalence_functor
  have : ((SplitSheaf.pseudofunctor (J := J)).toDescentData g).IsEquivalence :=
    (equivalence g hg).isEquivalence_functor
  exact SheafFamilyDescent.recoveryNaturality _ r p a w

end SquareKit.SheafDisplayFamilyDescent
