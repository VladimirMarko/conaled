import SquareKit.Internal.Cubical.Paths
import Mathlib.Logic.Equiv.Basic
import Mathlib.CategoryTheory.Whiskering

/-! Invertibility of dependent product and Path substitution comparisons.
Arrows out of a generalized element are uniquely determined by the underlying
cube restriction. This supplies the inverse without assuming a lifting law. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

/-- Every cube restriction has exactly one lift out of a generalized element. -/
def elementArrowEquiv (Γ : Context.{u}) (x : Γ.Elements) :
    (Σ y : Γ.Elements, x ⟶ y) ≃ (Σ J : Cubeᵒᵖ, x.obj ⟶ J) where
  toFun z := ⟨z.1.obj, z.2.hom⟩
  invFun z := ⟨Γ.elementsMk z.1 (Γ.map z.2 x.val), Functor.Elements.homMk z.2 rfl⟩
  left_inv z := by
    rcases z with ⟨@⟨J,y⟩,⟨f,h⟩⟩
    change x.obj ⟶ J at f
    change Γ.map f x.val = y at h
    subst y
    rfl
  right_inv _ := rfl

/-- Context substitution induces a bijection on arrows from a fixed element. -/
def substitutionArrowEquiv {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    (Σ y : Δ.Elements, x ⟶ y) ≃ (Σ y : Γ.Elements, σ.mapElements.obj x ⟶ y) where
  toFun z := ⟨σ.mapElements.obj z.1, σ.mapElements.map z.2⟩
  invFun z := (elementArrowEquiv Δ x).symm (elementArrowEquiv Γ (σ.mapElements.obj x) z)
  left_inv z := (elementArrowEquiv Δ x).injective (by
    change elementArrowEquiv Δ x ((elementArrowEquiv Δ x).symm _) = _
    rw [Equiv.apply_symm_apply]
    rfl)
  right_inv z := (elementArrowEquiv Γ (σ.mapElements.obj x)).injective (by
    change elementArrowEquiv Δ x ((elementArrowEquiv Δ x).symm _) = _
    rw [Equiv.apply_symm_apply])

/-- Extend function values along the proved bijection of generalized arrows. -/
def piInverseValue {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (σ : Δ ⟶ Γ) {x : Δ.Elements}
    (p : PiElement (reindex A σ) (reindex B (liftSub A σ)) x)
    {y : Γ.Elements} (f : σ.mapElements.obj x ⟶ y) (a : A.obj y) :
    B.obj (extendObj A y a) :=
  Equiv.piCongrLeft (P := fun z : Σ y : Γ.Elements, σ.mapElements.obj x ⟶ y =>
    ∀ a : A.obj z.1, B.obj (extendObj A z.1 a)) (substitutionArrowEquiv σ x)
      (fun z a => p.val z.2 a) ⟨y,f⟩ a

@[simp] theorem piInverseValue_map {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (σ : Δ ⟶ Γ) {x y : Δ.Elements}
    (p : PiElement (reindex A σ) (reindex B (liftSub A σ)) x)
    (f : x ⟶ y) (a : A.obj (σ.mapElements.obj y)) :
    piInverseValue σ p (σ.mapElements.map f) a = p.val f a := by
  exact congrFun (Equiv.piCongrLeft_apply_apply
    (P := fun z : Σ y : Γ.Elements, σ.mapElements.obj x ⟶ y =>
      ∀ a : A.obj z.1, B.obj (extendObj A z.1 a))
    (e := substitutionArrowEquiv σ x) (fun z a => p.val z.2 a) ⟨y,f⟩) a

def piInverseElement {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (σ : Δ ⟶ Γ) {x : Δ.Elements}
    (p : PiElement (reindex A σ) (reindex B (liftSub A σ)) x) :
    PiElement A B (σ.mapElements.obj x) where
  val := piInverseValue σ p
  naturality {y z} f g a := by
    obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
    change (⟨σ.mapElements.obj y', σ.mapElements.map f'⟩ :
      Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
    cases hf
    obtain ⟨⟨z',g'⟩,hg⟩ := (substitutionArrowEquiv σ y').surjective ⟨z,g⟩
    change (⟨σ.mapElements.obj z', σ.mapElements.map g'⟩ :
      Σ z, σ.mapElements.obj y' ⟶ z) = ⟨z,g⟩ at hg
    cases hg
    change B.map (extendHom A (σ.mapElements.map g') a)
      (piInverseValue σ p (σ.mapElements.map f') a) =
      piInverseValue σ p (σ.mapElements.map (f' ≫ g')) (A.map (σ.mapElements.map g') a)
    rw [piInverseValue_map, piInverseValue_map]
    exact p.naturality f' g' a

def piReindexInv {Γ Δ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) : pi (reindex A σ) (reindex B (liftSub A σ)) ⟶ reindex (pi A B) σ where
  app _ := TypeCat.ofHom (piInverseElement σ)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro p
    change PiElement (reindex A σ) (reindex B (liftSub A σ)) x at p
    apply PiElement.ext
    intro z g a
    obtain ⟨⟨z',g'⟩,hg⟩ := (substitutionArrowEquiv σ y).surjective ⟨z,g⟩
    change (⟨σ.mapElements.obj z', σ.mapElements.map g'⟩ :
      Σ z, σ.mapElements.obj y ⟶ z) = ⟨z,g⟩ at hg
    cases hg
    change piInverseValue σ (p.restrict f) (σ.mapElements.map g') a =
      piInverseValue σ p (σ.mapElements.map (f ≫ g')) a
    rw [piInverseValue_map, piInverseValue_map]
    rfl

theorem piInverse_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (σ : Δ ⟶ Γ) {x : Δ.Elements} (p : PiElement A B (σ.mapElements.obj x)) :
    piInverseElement σ ((piReindex A B σ).app x p) = p := by
  apply PiElement.ext
  intro y f a
  obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
  change (⟨σ.mapElements.obj y', σ.mapElements.map f'⟩ :
    Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
  cases hf
  exact piInverseValue_map σ _ f' a

theorem piReindex_inverse {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (σ : Δ ⟶ Γ) {x : Δ.Elements}
    (p : PiElement (reindex A σ) (reindex B (liftSub A σ)) x) :
    (piReindex A B σ).app x (piInverseElement σ p) = p := by
  apply PiElement.ext
  intro y f a
  exact piInverseValue_map σ p f a

/-- General dependent products commute with arbitrary context substitution. -/
def piReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ) :
    reindex (pi A B) σ ≅ pi (reindex A σ) (reindex B (liftSub A σ)) where
  hom := piReindex A B σ
  inv := piReindexInv A B σ
  hom_inv_id := by
    ext x p
    exact piInverse_reindex σ p
  inv_hom_id := by
    ext x p
    exact piReindex_inverse σ p

/-- The same inverse preserves the prescribed endpoints at every restriction. -/
def pathReindexInv {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    path (reindex B (liftSub (interval Γ) σ)) (Term.reindex a₀ σ) (Term.reindex a₁ σ) ⟶
      reindex (path B a₀ a₁) σ where
  app x := TypeCat.ofHom (fun p => ⟨piInverseElement (A := interval Γ) (B := B) σ p.val, by
    intro y f
    obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
    change (⟨σ.mapElements.obj y', σ.mapElements.map f'⟩ :
      Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
    cases hf
    change piInverseValue (A := interval Γ) (B := B) σ p.val (σ.mapElements.map f') _ = _ ∧
      piInverseValue (A := interval Γ) (B := B) σ p.val (σ.mapElements.map f') _ = _
    exact ⟨(piInverseValue_map (A := interval Γ) (B := B) σ p.val f' _).trans (p.property f').1,
      (piInverseValue_map (A := interval Γ) (B := B) σ p.val f' _).trans (p.property f').2⟩⟩)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congrArg (fun h => h p.val) ((piReindexInv (interval Γ) B σ).naturality f)

/-- Dependent Path formation commutes with arbitrary context substitution. -/
def pathReindexIso {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    reindex (path B a₀ a₁) σ ≅
      path (reindex B (liftSub (interval Γ) σ)) (Term.reindex a₀ σ) (Term.reindex a₁ σ) where
  hom := pathReindex B a₀ a₁ σ
  inv := pathReindexInv B a₀ a₁ σ
  hom_inv_id := by
    ext x p
    apply Subtype.ext
    exact piInverse_reindex σ p.val
  inv_hom_id := by
    ext x p
    apply Subtype.ext
    exact piReindex_inverse (A := interval Γ) (B := B) σ p.val

@[simp] theorem piReindex_id {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    piReindex A B (𝟙 Γ) = 𝟙 (pi A B) := rfl

theorem piReindex_comp {Γ Δ Θ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    piReindex A B (τ ≫ σ) =
      Functor.whiskerLeft τ.mapElements (piReindex A B σ) ≫
        piReindex (reindex A σ) (reindex B (liftSub A σ)) τ := rfl

@[simp] theorem pathReindex_id {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) :
    pathReindex B a₀ a₁ (𝟙 Γ) = 𝟙 (path B a₀ a₁) := rfl

theorem pathReindex_comp {Γ Δ Θ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    pathReindex B a₀ a₁ (τ ≫ σ) =
      Functor.whiskerLeft τ.mapElements (pathReindex B a₀ a₁ σ) ≫
        pathReindex (reindex B (liftSub (interval Γ) σ))
          (Term.reindex a₀ σ) (Term.reindex a₁ σ) τ := rfl

/-- A family isomorphism loses no dependent section in either direction. -/
theorem Term.map_iso_roundtrip {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) (t : Term A) :
    Term.map e.inv (Term.map e.hom t) = t := by
  apply Term.ext
  intro x
  exact congrArg (fun f => f.app x (t.val x)) e.hom_inv_id

theorem Term.map_injective_of_iso {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    Function.Injective (Term.map e.hom) := by
  intro s t h
  exact (Term.map_iso_roundtrip e s).symm.trans
    ((congrArg (Term.map e.inv) h).trans (Term.map_iso_roundtrip e t))

end SquareKit.Cubical.Presheaf
