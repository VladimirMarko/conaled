import SquareKit.Internal.Cubical.EquivalenceFamilies
import SquareKit.Internal.Cubical.EquivalenceWitnessSubstitution

/-! Substitution of internal equivalence sections retains selected fiber contractions. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.EquivalenceFamilies
open CategoryTheory
universe u

theorem mapReindexSections_id {Γ : Context.{u}} (A B : Family Γ) (f : A ⟶ B) :
    mapReindexSections A B (𝟙 Γ) f = encodeMap f := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y k a
  exact piInverseValue_map (A := A) (B := reindex B (projection A)) (𝟙 Γ) ((encodeMap f).val x) k a

theorem mapReindexSections_comp {Γ Δ Θ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (f : reindex A σ ⟶ reindex B σ) :
    mapReindexSections A B (τ ≫ σ) (Functor.whiskerLeft τ.mapElements f) =
      (mapReindexSections A B σ f).reindex τ := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y k a
  obtain ⟨⟨y',k'⟩,hk⟩ := (substitutionArrowEquiv (τ ≫ σ) x).surjective ⟨y,k⟩
  change (⟨(τ ≫ σ).mapElements.obj y', (τ ≫ σ).mapElements.map k'⟩ :
    Σ y, (τ ≫ σ).mapElements.obj x ⟶ y) = ⟨y,k⟩ at hk
  cases hk
  change piInverseValue (A := A) (B := reindex B (projection A)) (τ ≫ σ) ((encodeMap (Functor.whiskerLeft τ.mapElements f)).val x)
      ((τ ≫ σ).mapElements.map k') a =
    piInverseValue (A := A) (B := reindex B (projection A)) σ ((encodeMap f).val (τ.mapElements.obj x))
      (σ.mapElements.map (τ.mapElements.map k')) a
  exact (piInverseValue_map (A := A) (B := reindex B (projection A)) (τ ≫ σ)
    ((encodeMap (Functor.whiskerLeft τ.mapElements f)).val x) k' a).trans
    (piInverseValue_map (A := A) (B := reindex B (projection A)) σ
      ((encodeMap f).val (τ.mapElements.obj x)) (τ.mapElements.map k') a).symm

private noncomputable def encodeAt {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (m : Term (reindex (maps A B) σ))
    (E : HomotopyEquivalence (Functor.whiskerLeft (pair σ m).mapElements (universalMap A B))) :
    Term (reindex (equiv A B) σ) :=
  sigmaIntro (B := reindex (isEquiv (universalMap A B)) (liftSub (maps A B) σ)) m
    (isEquivReindexSections (universalMap A B) (pair σ m) E)

private theorem encodeAt_congr {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (m n : Term (reindex (maps A B) σ)) (h : m = n)
    (E : HomotopyEquivalence (Functor.whiskerLeft (pair σ n).mapElements (universalMap A B))) :
    encodeAt A B σ m (cast (congrArg (fun k => HomotopyEquivalence
      (Functor.whiskerLeft (pair σ k).mapElements (universalMap A B))) h.symm) E) =
      encodeAt A B σ n E := by
  cases h
  rfl

private theorem encodeAt_reindex {Γ Δ Θ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (m : Term (reindex (maps A B) σ))
    (E : HomotopyEquivalence (Functor.whiskerLeft (pair σ m).mapElements (universalMap A B))) :
    encodeAt A B (τ ≫ σ) (m.reindex τ) (E.reindex τ) =
      (encodeAt A B σ m E).reindex τ := by
  exact congrArg (sigmaIntro (B := reindex (isEquiv (universalMap A B))
    (liftSub (maps A B) (τ ≫ σ))) (m.reindex τ))
    (isEquivReindexSections_comp (universalMap A B) (pair σ m) τ E)

private noncomputable def encodeAtFor {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (m : Term (reindex (maps A B) σ)) (f : reindex A σ ⟶ reindex B σ)
    (hf : Functor.whiskerLeft (pair σ m).mapElements (universalMap A B) = f)
    (E : HomotopyEquivalence f) : Term (reindex (equiv A B) σ) :=
  encodeAt A B σ m (cast (congrArg HomotopyEquivalence hf.symm) E)

private theorem encodeAtFor_congr {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (m n : Term (reindex (maps A B) σ)) (h : m = n)
    (f : reindex A σ ⟶ reindex B σ)
    (hm : Functor.whiskerLeft (pair σ m).mapElements (universalMap A B) = f)
    (hn : Functor.whiskerLeft (pair σ n).mapElements (universalMap A B) = f)
    (E : HomotopyEquivalence f) : encodeAtFor A B σ m f hm E = encodeAtFor A B σ n f hn E := by
  cases h
  rfl

private theorem encodeAtFor_reindex {Γ Δ Θ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (m : Term (reindex (maps A B) σ))
    (f : reindex A σ ⟶ reindex B σ)
    (hf : Functor.whiskerLeft (pair σ m).mapElements (universalMap A B) = f)
    (E : HomotopyEquivalence f) :
    encodeAtFor A B (τ ≫ σ) (m.reindex τ) (Functor.whiskerLeft τ.mapElements f)
      (congrArg (Functor.whiskerLeft τ.mapElements) hf) (E.reindex τ) =
      (encodeAtFor A B σ m f hf E).reindex τ := by
  cases hf
  exact encodeAt_reindex A B σ τ m E

private theorem equivReindexSections_apply {Γ Δ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f) :
    equivReindexSections A B σ ⟨f,E⟩ =
      encodeAtFor A B σ (mapReindexSections A B σ f) f
        (universalMap_reindex_encoded A B σ f) E := by
  apply Term.ext
  intro x
  rfl

private theorem equivSections_apply {Γ : Context.{u}} (A B : Family Γ)
    (f : A ⟶ B) (E : HomotopyEquivalence f) :
    equivSections A B ⟨f,E⟩ = encodeAtFor A B (𝟙 Γ) (encodeMap f) f rfl E := by
  apply Term.ext
  intro x
  rfl

theorem equivReindexSections_comp {Γ Δ Θ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (f : reindex A σ ⟶ reindex B σ)
    (E : HomotopyEquivalence f) :
    equivReindexSections A B (τ ≫ σ) ⟨Functor.whiskerLeft τ.mapElements f,E.reindex τ⟩ =
      (equivReindexSections A B σ ⟨f,E⟩).reindex τ := by
  let m := mapReindexSections A B σ f
  let hf := universalMap_reindex_encoded A B σ f
  let ft := Functor.whiskerLeft τ.mapElements f
  let mt := mapReindexSections A B (τ ≫ σ) ft
  let hft := universalMap_reindex_encoded A B (τ ≫ σ) ft
  let hfr := congrArg (Functor.whiskerLeft τ.mapElements) hf
  have h₁ : encodeAtFor A B (τ ≫ σ) mt ft hft (E.reindex τ) =
      encodeAtFor A B (τ ≫ σ) (m.reindex τ) ft hfr (E.reindex τ) :=
    encodeAtFor_congr A B (τ ≫ σ) mt (m.reindex τ)
      (mapReindexSections_comp A B σ τ f) ft hft hfr (E.reindex τ)
  have h₂ : encodeAtFor A B (τ ≫ σ) (m.reindex τ) ft hfr (E.reindex τ) =
      (encodeAtFor A B σ m f hf E).reindex τ :=
    encodeAtFor_reindex A B σ τ m f hf E
  have h₃ : equivReindexSections A B (τ ≫ σ) ⟨ft,E.reindex τ⟩ =
      encodeAtFor A B (τ ≫ σ) mt ft hft (E.reindex τ) :=
    equivReindexSections_apply A B (τ ≫ σ) ft (E.reindex τ)
  have h₄ : (encodeAtFor A B σ m f hf E).reindex τ =
      (equivReindexSections A B σ ⟨f,E⟩).reindex τ :=
    congrArg (fun t => t.reindex τ) (equivReindexSections_apply A B σ f E).symm
  exact h₃.trans (h₁.trans (h₂.trans h₄))

theorem equivReindexSections_id {Γ : Context.{u}} (A B : Family Γ)
    (f : A ⟶ B) (E : HomotopyEquivalence f) :
    equivReindexSections A B (𝟙 Γ) ⟨f,E⟩ = equivSections A B ⟨f,E⟩ := by
  exact (equivReindexSections_apply A B (𝟙 Γ) f E).trans
    ((encodeAtFor_congr A B (𝟙 Γ) (mapReindexSections A B (𝟙 Γ) f) (encodeMap f)
      (mapReindexSections_id A B f) f (universalMap_reindex_encoded A B (𝟙 Γ) f) rfl E).trans
      (equivSections_apply A B f E).symm)

end SquareKit.Cubical.Presheaf.EquivalenceFamilies
