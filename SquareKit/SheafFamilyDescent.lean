import SquareKit.SheafFamilyTopology
import SquareKit.SheafTorsorStack
import SquareKit.SheafActionQuotientStack
import SquareKit.SheafActionQuotientCoproduct
import SquareKit.CoproductDescent

/-! Family descent for the existing torsor and action-quotient pseudofunctors. -/
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

/-- Torsor product restriction is proved by the actual coproduct construction. -/
theorem torsor_effectiveCoproducts (G : Sheaf J GrpCat.{max u v}) :
    CoproductDescent.EffectiveCoproducts.{max u v} (SheafTorsor.Stack.pseudofunctor G) := by
  intro I Y c hc
  apply CoproductDescent.effectiveCoproducts_of_chosen _ _ c hc
  intro Y
  change (SheafTorsor.Coproduct.restrict (G := G) (Y := Y)).IsEquivalence
  infer_instance

/-- Quotient product restriction retains target maps and stabilizer arrows. -/
theorem quotient_effectiveCoproducts {G : Sheaf J GrpCat.{max u v}}
    {M : Sheaf J (Type (max u v))} (a : SheafActionQuotient.Action G M) :
    CoproductDescent.EffectiveCoproducts.{max u v} (SheafActionQuotient.Stack.pseudofunctor a) := by
  intro I Y c hc
  apply CoproductDescent.effectiveCoproducts_of_chosen _ _ c hc
  intro Y
  change (SheafActionQuotient.Coproduct.restrict (a := a) (Y := Y)).IsEquivalence
  infer_instance

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
    (SheafCoproductGeometry.total_isVanKampen Y) hF (Sigma.desc f)
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
    (SheafCoproductGeometry.total_isVanKampen Y) hF (Sigma.desc f)
  have := (F.isStackFor_ofArrows_iff _).mp
    (hSingle (Sigma.desc f) ((SheafFamilyCover.jointlyLocallySurjective_iff_sigmaDesc f).mp hf))
  have h := Functor.isEquivalence_of_iso
    (CoproductDescent.toDescentDataAggregateRestrictionIso (F := F) c (Sigma.desc f))
  change (F.toDescentData (fun i => Sigma.ι Y i ≫ Sigma.desc f)).IsEquivalence at h
  have he : (fun i => Sigma.ι Y i ≫ Sigma.desc f) = f := funext (Sigma.ι_comp_desc f)
  rw [he] at h
  exact h

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

/-- Chosen effective recovery is compatible with a refinement or a change of
base, naturally on every compatible arrow. The hypotheses are discharged below
for the two clients and jointly covering families. -/
def recoveryNaturality
    (F : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) Cat.{v',u'})
    {S T : Sheaf J (Type (max u v))} {I K : Type (max u v)}
    {X : I → Sheaf J (Type (max u v))} {Y : K → Sheaf J (Type (max u v))}
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
