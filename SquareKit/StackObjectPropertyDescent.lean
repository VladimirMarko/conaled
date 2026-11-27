import SquareKit.StackDescentLifting
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Singleton covers and descent for full subcategories of a pseudofunctor. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.StackObjectPropertyDescent
open CategoryTheory Opposite Limits
universe u v u' v' t
variable {C : Type u} [Category.{v} C]

/-- Pulling back a singleton cover yields a singleton cover. -/
theorem singleton_pullback (J : GrothendieckTopology C)
    {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ X) [HasPullback q p]
    (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X) :
    Sieve.ofArrows _ (fun _ : Unit => pullback.fst q p) ∈ J Z := by
  rw [Sieve.ofArrows_eq_pullback_of_isPullback (fun _ : Unit => p)
    (fun _ => IsPullback.of_hasPullback q p)]
  exact J.pullback_stable q hp

/-- Composition of singleton covers is covering. -/
theorem singleton_comp (J : GrothendieckTopology C)
    {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y)
    (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    (hq : Sieve.ofArrows _ (fun _ : Unit => q) ∈ J Y) :
    Sieve.ofArrows _ (fun _ : Unit => q ≫ p) ∈ J X := by
  apply J.superset_covering _ (J.bindOfArrows hp (fun _ => hq))
  rw [Sieve.generate_le_iff]
  rintro W f ⟨i, g, ⟨j⟩⟩
  exact Sieve.ofArrows_mk _ _ ()

/-- Two singleton covers have a covering common refinement. -/
theorem singleton_common (J : GrothendieckTopology C)
    {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ X) [HasPullback p q]
    (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    (hq : Sieve.ofArrows _ (fun _ : Unit => q) ∈ J X) :
    Sieve.ofArrows _ (fun _ : Unit => pullback.fst p q ≫ p) ∈ J X :=
  singleton_comp J p (pullback.fst p q) hp (singleton_pullback J q p hq)

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
/-- A full subpresentation of a prestack already has sheaves of arrows. -/
theorem isPrestack_of_fullyFaithful
    {B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    (η : Pseudofunctor.StrongTrans F B)
    (hη : ∀ X : C, (StackDescentTransformation.component η X).FullyFaithful)
    (J : GrothendieckTopology C) [B.IsPrestack J] : F.IsPrestack J := by
  apply Pseudofunctor.IsPrestack.of_isPrestackFor
  intro S R hR
  let f := fun (r : R.arrows.category) => r.obj.hom
  have hf : Sieve.ofArrows _ f ∈ J S := by
    simpa only [f, Sieve.ofArrows_category] using hR
  let := (StackDescentTransformation.mapFullyFaithful η hη (f := f)).faithful
  exact ⟨⟨Functor.FullyFaithful.ofCompFaithful
    (((hη S).comp (B.fullyFaithfulToDescentData f hf)).ofIso
      (StackDescentTransformation.canonicalIso η f).symm)⟩⟩

variable (P : F.ObjectProperty) [P.IsClosedUnderMapObj]
variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- Descent data whose local objects satisfy a restriction-stable property
also form descent data in the full subpresentation. -/
def lift (D : F.DescentData f) (hD : ∀ i, P.prop (.mk (op (X i))) (D.obj i)) :
    P.fullsubcategory.DescentData f where
  obj i := ⟨D.obj i, hD i⟩
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := ObjectProperty.homMk (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    apply ObjectProperty.hom_ext
    change Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂ = _
    exact D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self _ q _ g hg := by
    apply ObjectProperty.hom_ext
    exact D.hom_self q g hg
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    apply ObjectProperty.hom_ext
    exact D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- Forgetting a full subcategory condition retains the entire descent datum. -/
def forgetData (D : P.fullsubcategory.DescentData f) : F.DescentData f where
  obj i := (D.obj i).obj
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).hom
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    congrArg InducedCategory.Hom.hom
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  hom_self _ q _ g hg := congrArg InducedCategory.Hom.hom (D.hom_self q g hg)
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    congrArg InducedCategory.Hom.hom (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Descent arrows are retained without quotienting by isomorphism classes. -/
def forget : P.fullsubcategory.DescentData f ⥤ F.DescentData f where
  obj := forgetData P
  map φ :=
    { hom i := (φ.hom i).hom
      comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
        congrArg InducedCategory.Hom.hom (φ.comm q f₁ f₂ hf₁ hf₂) }

@[simp] theorem forget_lift (D : F.DescentData f)
    (hD : ∀ i, P.prop (.mk (op (X i))) (D.obj i)) :
    (forget P).obj (lift P D hD) = D := rfl

@[simp] theorem forget_toDescentData (A : P.Obj (.mk (op S))) :
    (forget P).obj ((P.fullsubcategory.toDescentData f).obj A) =
      (F.toDescentData f).obj A.obj := rfl

/-- Effectiveness in a full subpresentation recovers the same ambient object.
Full faithfulness of descent supplies the comparison over the original base. -/
def recoveryIso (J : GrothendieckTopology C) [F.IsPrestack J]
    (hf : Sieve.ofArrows _ f ∈ J S) (M : F.obj (.mk (op S)))
    (hM : ∀ i, P.prop (.mk (op (X i)))
      (((F.toDescentData f).obj M).obj i))
    (N : P.Obj (.mk (op S)))
    (e : (P.fullsubcategory.toDescentData f).obj N ≅
      lift P ((F.toDescentData f).obj M) hM) : N.obj ≅ M :=
  (F.fullyFaithfulToDescentData f hf).preimageIso ((forget P).mapIso e)

end SquareKit.StackObjectPropertyDescent
