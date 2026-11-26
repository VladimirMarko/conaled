import SquareKit.SheafCoproductGeometry
import SquareKit.SheafFamilyTopology
import SquareKit.SheafContextTopology
import SquareKit.CoproductDescent
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-! From constructive singleton and coproduct descent to family stacks. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafFamilyDescent
open CategoryTheory Limits Opposite
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Every old singleton covering sieve is also a family covering sieve. -/
theorem singleton_topology_le :
    SheafCover.topology (J := J) ≤ SheafFamilyCover.topology (J := J) := by
  rintro X R ⟨Y,f,hf,hR⟩
  exact ⟨PUnit, fun _ => Y, fun _ => f,
    (SheafFamilyCover.singleton_iff f).mpr hf, fun _ => hR⟩

/-- Effective descent for every joint family supplies the family-topology prestack. -/
theorem isPrestack_of_joint
    (F : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) Cat.{v',u'})
    (hF : ∀ {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
      {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X),
      SheafFamilyCover.JointlyLocallySurjective f → F.IsStackFor (Presieve.ofArrows Y f)) :
    F.IsPrestack (SheafFamilyCover.topology (J := J)) where
  isSheaf {S} M N := by
    apply Presheaf.IsSheaf.of_le (SheafFamilyCover.over_topology_le S)
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
    rintro X R ⟨I,Y,f,rfl,hf⟩
    rw [Presieve.isSheafFor_iff_generate]
    apply Pseudofunctor.IsPrestackFor.isSheafFor'
    rw [Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward,
      Sieve.generate_sieve]
    simp only [Presieve.map_ofArrows]
    apply (Pseudofunctor.IsPrestackFor_generate_iff _ _).mpr
    exact (hF (fun i => (f i).left) hf).isPrestackFor

/-- Effectiveness extends from joint families to the topology they generate. -/
theorem isStack_of_joint
    (F : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) Cat.{v',u'})
    (hF : ∀ {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
      {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X),
      SheafFamilyCover.JointlyLocallySurjective f → F.IsStackFor (Presieve.ofArrows Y f)) :
    F.IsStack (SheafFamilyCover.topology (J := J)) := by
  have := isPrestack_of_joint F hF
  apply Pseudofunctor.IsStack.of_isStackFor
  rintro X R ⟨I,Y,f,hf,hR⟩
  apply Pseudofunctor.IsStackFor.of_le F (hF f hf)
    (J := SheafFamilyCover.topology (J := J)) (SheafFamilyCover.covering hf)
  rintro Z g ⟨i⟩
  exact hR i

/-- Family and aggregate descent agree on every object and compatible arrow,
even before a coverage hypothesis is imposed. -/
def aggregateEquivalence
    (F : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) Cat.{v',u'})
    (hF : CoproductDescent.EffectiveCoproducts.{max u v} F)
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X) :
    F.DescentData (fun _ : Unit => Sigma.desc f) ≌ F.DescentData f := by
  let c := colimit.cocone (Discrete.functor Y)
  have := CoproductDescent.aggregateRestriction_isEquivalence c
    (SheafCoproductGeometry.total_isVanKampenColimit Y) hF (Sigma.desc f)
  let e := (CoproductDescent.aggregateRestriction (F := F) c (Sigma.desc f)).asEquivalence
  change F.DescentData (fun _ : Unit => Sigma.desc f) ≌
    F.DescentData (fun i => Sigma.ι Y i ≫ Sigma.desc f) at e
  have he : (fun i => Sigma.ι Y i ≫ Sigma.desc f) = f := funext (Sigma.ι_comp_desc f)
  rw [he] at e
  exact e

/-- Singleton effectiveness and proved coproduct gluing imply family effectiveness. -/
theorem isStackFor_joint
    (F : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) Cat.{v',u'})
    (hF : CoproductDescent.EffectiveCoproducts.{max u v} F)
    (hSingle : ∀ {X Y : Sheaf J (Type (max u v))} (f : Y ⟶ X),
      Presheaf.IsLocallySurjective J f.hom → F.IsStackFor (Presieve.ofArrows _ (fun _ : Unit => f)))
    {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
    {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    F.IsStackFor (Presieve.ofArrows Y f) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  let c := colimit.cocone (Discrete.functor Y)
  have := CoproductDescent.aggregateRestriction_isEquivalence c
    (SheafCoproductGeometry.total_isVanKampenColimit Y) hF (Sigma.desc f)
  have := (F.isStackFor_ofArrows_iff _).mp
    (hSingle (Sigma.desc f) ((SheafFamilyCover.jointlyLocallySurjective_iff_sigmaDesc f).mp hf))
  have h := Functor.isEquivalence_of_iso
    (CoproductDescent.toDescentDataAggregateRestrictionIso (F := F) c (Sigma.desc f))
  change (F.toDescentData (fun i => Sigma.ι Y i ≫ Sigma.desc f)).IsEquivalence at h
  have he : (fun i => Sigma.ι Y i ≫ Sigma.desc f) = f := funext (Sigma.ι_comp_desc f)
  rw [he] at h
  exact h

/-- The family topology also recovers the original `Unit`-indexed singleton
category, independently of the universe used for supported covering families. -/
def singletonEquivalence
    (F : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) Cat.{v',u'})
    [F.IsStack (SheafFamilyCover.topology (J := J))]
    {X Y : Sheaf J (Type (max u v))} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    F.obj ⟨op X⟩ ≌ F.DescentData (fun _ : Unit => f) := by
  have := F.isEquivalence_toDescentData (J := SheafFamilyCover.topology (J := J))
    (fun _ : Unit => f) (singleton_topology_le _
      ⟨Y, f, inferInstance, Sieve.ofArrows_mk (fun _ : Unit => Y) (fun _ => f) ()⟩)
  exact (F.toDescentData (fun _ : Unit => f)).asEquivalence

/-- Chosen effective recovery is compatible with a refinement or a change of
base, naturally on every compatible arrow. The hypotheses are discharged below
for the two clients and jointly covering families. -/
def recoveryNaturality
    {D : Type*} [Category D]
    (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v',u'})
    {S T : D} {I K : Type*} {X : I → D} {Y : K → D}
    {f : ∀ i, X i ⟶ S} {g : ∀ k, Y k ⟶ T}
    [ (F.toDescentData f).IsEquivalence ] [ (F.toDescentData g).IsEquivalence ]
    (r : K → I) (p : T ⟶ S) (a : ∀ k, Y k ⟶ X (r k))
    (w : ∀ k, a k ≫ f (r k) = g k ≫ p) :
    Pseudofunctor.DescentData.pullFunctor F w ⋙ (F.toDescentData g).asEquivalence.inverse ≅
      (F.toDescentData f).asEquivalence.inverse ⋙ (F.map p.op.toLoc).toFunctor :=
  Iso.compInverseIso (H := (F.toDescentData g).asEquivalence)
    ((Iso.inverseCompIso (G := (F.toDescentData f).asEquivalence)
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F w).symm).symm ≪≫
        (Functor.associator _ _ _).symm)

end SquareKit.SheafFamilyDescent
