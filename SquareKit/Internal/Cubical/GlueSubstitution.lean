import SquareKit.Internal.Cubical.Glue

/-! Base substitution of compatible Glue data. Face families are pulled back
along the actual restricted-context substitution. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.Glue
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} (φ : Cofibration Γ) (A : Family Γ)
  (T : Family (restrictContext φ)) (e : T ⟶ reindex A (restrictInclusion φ))
  (σ : Δ ⟶ Γ)

def compatibleReindexMap : reindex (compatibleFamily φ A T e) σ ⟶
    compatibleFamily (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) where
  app _ := TypeCat.ofHom (fun s => {
    ambient := s.ambient
    face := fun {_} f h => s.face (σ.mapElements.map f) h
    naturality := fun f g h => s.naturality (σ.mapElements.map f) (σ.mapElements.map g) h
    compatible := fun f h => s.compatible (σ.mapElements.map f) h })
  naturality _ _ _ := rfl

def reindexMap : reindex (family φ A T e) σ ⟶
    family (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) :=
  Functor.whiskerLeft σ.mapElements (familyIso φ A T e).hom ≫
    compatibleReindexMap φ A T e σ ≫
      (familyIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)).inv

theorem compatibleReindex_intro (t : Term T) (a : Term A)
    (h : Term.map e t = a.reindex (restrictInclusion φ)) :
    Term.map (compatibleReindexMap φ A T e σ)
      ((compatibleIntro φ A T e t a h).reindex σ) =
    compatibleIntro (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
      (t.reindex (restrictSubstitution φ σ)) (a.reindex σ)
      (congrArg (fun t => t.reindex (restrictSubstitution φ σ)) h) := rfl

def inverseFace {x : Δ.Elements}
    (s : CompatibleElement (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x)
    {y : Γ.Elements} (f : σ.mapElements.obj x ⟶ y) (h : φ.full y) : T.obj (faceObj φ y h) :=
  Equiv.piCongrLeft (P := fun z : Σ y, σ.mapElements.obj x ⟶ y =>
    ∀ h : φ.full z.1, T.obj (faceObj φ z.1 h)) (substitutionArrowEquiv σ x)
      (fun z h => s.face z.2 h) ⟨y,f⟩ h

theorem inverseFace_map {x y : Δ.Elements}
    (s : CompatibleElement (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x)
    (f : x ⟶ y) (h : φ.full (σ.mapElements.obj y)) :
    inverseFace φ A T e σ s (σ.mapElements.map f) h = s.face f h :=
  congrFun (Equiv.piCongrLeft_apply_apply
    (P := fun z : Σ y, σ.mapElements.obj x ⟶ y =>
      ∀ h : φ.full z.1, T.obj (faceObj φ z.1 h))
    (e := substitutionArrowEquiv σ x) (fun z h => s.face z.2 h) ⟨y,f⟩) h

def inverseElement {x : Δ.Elements}
    (s : CompatibleElement (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x) :
    CompatibleElement φ A T e (σ.mapElements.obj x) where
  ambient := s.ambient
  face := inverseFace φ A T e σ s
  naturality {y z} f g h := by
    obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
    change (⟨σ.mapElements.obj y',σ.mapElements.map f'⟩ : Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
    cases hf
    obtain ⟨⟨z',g'⟩,hg⟩ := (substitutionArrowEquiv σ y').surjective ⟨z,g⟩
    change (⟨σ.mapElements.obj z',σ.mapElements.map g'⟩ : Σ z, σ.mapElements.obj y' ⟶ z) = ⟨z,g⟩ at hg
    cases hg
    change T.map (faceHom φ (σ.mapElements.map g') h)
      (inverseFace φ A T e σ s (σ.mapElements.map f') h) =
      inverseFace φ A T e σ s (σ.mapElements.map (f' ≫ g')) _
    rw [inverseFace_map, inverseFace_map]
    exact s.naturality f' g' h
  compatible {y} f h := by
    obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
    change (⟨σ.mapElements.obj y',σ.mapElements.map f'⟩ : Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
    cases hf
    rw [inverseFace_map]
    exact s.compatible f' h

def compatibleReindexInv :
    compatibleFamily (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) ⟶
    reindex (compatibleFamily φ A T e) σ where
  app _ := TypeCat.ofHom (inverseElement φ A T e σ)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply CompatibleElement.ext
    · rfl
    · intro z g h
      obtain ⟨⟨z',g'⟩,hg⟩ := (substitutionArrowEquiv σ y).surjective ⟨z,g⟩
      change (⟨σ.mapElements.obj z',σ.mapElements.map g'⟩ : Σ z, σ.mapElements.obj y ⟶ z) = ⟨z,g⟩ at hg
      cases hg
      change inverseFace φ A T e σ (s.restrict _ _ _ _ f) (σ.mapElements.map g') h =
        inverseFace φ A T e σ s (σ.mapElements.map (f ≫ g')) h
      exact (inverseFace_map φ A T e σ (s.restrict _ _ _ _ f) g' h).trans
        (inverseFace_map φ A T e σ s (f ≫ g') h).symm

/-- Every restriction datum is recovered, including arrows outside the displayed substitution. -/
def compatibleReindexIso : reindex (compatibleFamily φ A T e) σ ≅
    compatibleFamily (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) where
  hom := compatibleReindexMap φ A T e σ
  inv := compatibleReindexInv φ A T e σ
  hom_inv_id := by
    ext x s
    apply CompatibleElement.ext
    · rfl
    · intro y f h
      obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
      change (⟨σ.mapElements.obj y',σ.mapElements.map f'⟩ : Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
      cases hf
      exact inverseFace_map φ A T e σ _ f' h
  inv_hom_id := by
    ext x s
    apply CompatibleElement.ext
    · rfl
    · intro y f h
      exact inverseFace_map φ A T e σ s f h

/-- Glue substitution is invertible for its complete compatible-data presentation. -/
noncomputable def reindexIso : reindex (family φ A T e) σ ≅
    family (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) :=
  (Functor.isoWhiskerLeft σ.mapElements (familyIso φ A T e)) ≪≫
    compatibleReindexIso φ A T e σ ≪≫
      (familyIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)).symm

end SquareKit.Cubical.Presheaf.Glue
