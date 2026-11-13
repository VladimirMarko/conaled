import SquareKit.Internal.Cubical.EquivalenceFamilySubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.EquivalenceFamilies
open CategoryTheory
universe u

private def mapOfSections {Γ : Context.{u}} {C D : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex C σ) → Term (reindex D σ)) : C ⟶ D where
  app x := TypeCat.ofHom (fun c => (Φ (projection C) (generic C)).val (extendObj C x c))
  naturality x y k := by
    apply ConcreteCategory.hom_ext
    intro c
    exact ((Φ (projection C) (generic C)).property (extendHom C k c)).symm

private theorem mapOfSections_apply {Γ : Context.{u}} {C D : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex C σ) → Term (reindex D σ))
    (hn : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex C σ)),
      Φ (τ ≫ σ) (s.reindex τ) = (Φ σ s).reindex τ)
    {Δ : Context.{u}} (σ : Δ ⟶ Γ) (s : Term (reindex C σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (mapOfSections Φ)) s = Φ σ s :=
  (hn (projection C) (pair σ s) (generic C)).symm

private noncomputable def reindexTo {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    {Θ : Context.{u}} (τ : Θ ⟶ Δ) (s : Term (reindex (equiv A B) (τ ≫ σ))) :
    Term (reindex (equiv (reindex A σ) (reindex B σ)) τ) :=
  equivReindexSections (reindex A σ) (reindex B σ) τ
    ((equivReindexSections A B (τ ≫ σ)).symm s)

private noncomputable def reindexFrom {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    {Θ : Context.{u}} (τ : Θ ⟶ Δ)
    (s : Term (reindex (equiv (reindex A σ) (reindex B σ)) τ)) :
    Term (reindex (equiv A B) (τ ≫ σ)) :=
  equivReindexSections A B (τ ≫ σ)
    ((equivReindexSections (reindex A σ) (reindex B σ) τ).symm s)

private theorem equivReindexSections_decode_comp {Γ Δ Θ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex (equiv A B) σ)) :
    (equivReindexSections A B (τ ≫ σ)).symm (s.reindex τ) =
      ⟨Functor.whiskerLeft τ.mapElements ((equivReindexSections A B σ).symm s).1,
        ((equivReindexSections A B σ).symm s).2.reindex τ⟩ := by
  apply (equivReindexSections A B (τ ≫ σ)).injective
  exact (Equiv.apply_symm_apply _ _).trans
    ((congrArg (fun t => t.reindex τ) (Equiv.apply_symm_apply (equivReindexSections A B σ) s)).symm.trans
      (equivReindexSections_comp A B σ τ _ _).symm)

private theorem reindexTo_natural {Γ Δ Θ Ω : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (τ : Θ ⟶ Δ) (ρ : Ω ⟶ Θ) (s : Term (reindex (equiv A B) (τ ≫ σ))) :
    reindexTo A B σ (ρ ≫ τ) (s.reindex ρ) = (reindexTo A B σ τ s).reindex ρ := by
  exact (congrArg (equivReindexSections (reindex A σ) (reindex B σ) (ρ ≫ τ))
    (equivReindexSections_decode_comp A B (τ ≫ σ) ρ s)).trans
    (equivReindexSections_comp (reindex A σ) (reindex B σ) τ ρ _ _)

private theorem reindexFrom_natural {Γ Δ Θ Ω : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (τ : Θ ⟶ Δ) (ρ : Ω ⟶ Θ)
    (s : Term (reindex (equiv (reindex A σ) (reindex B σ)) τ)) :
    reindexFrom A B σ (ρ ≫ τ) (s.reindex ρ) = (reindexFrom A B σ τ s).reindex ρ := by
  exact (congrArg (equivReindexSections A B ((ρ ≫ τ) ≫ σ))
    (equivReindexSections_decode_comp (reindex A σ) (reindex B σ) τ ρ s)).trans
    (equivReindexSections_comp A B (τ ≫ σ) ρ _ _)

private theorem mapOfSections_inverse {Γ : Context.{u}} {C D : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex C σ) → Term (reindex D σ))
    (Ψ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex D σ) → Term (reindex C σ))
    (hΦ : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex C σ)),
      Φ (τ ≫ σ) (s.reindex τ) = (Φ σ s).reindex τ)
    (hΨ : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex D σ)),
      Ψ (τ ≫ σ) (s.reindex τ) = (Ψ σ s).reindex τ)
    (h : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (s : Term (reindex C σ)), Ψ σ (Φ σ s) = s) :
    mapOfSections Φ ≫ mapOfSections Ψ = 𝟙 C := by
  let π := projection C
  have ht := mapOfSections_apply Ψ hΨ π
    (Term.map (Functor.whiskerLeft π.mapElements (mapOfSections Φ)) (generic C))
  have ht' := congrArg (Ψ π) (mapOfSections_apply Φ hΦ π (generic C))
  have hh := ht.trans (ht'.trans (h π (generic C)))
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro c
  exact congrArg (fun t => t.val (extendObj C x c)) hh

private theorem bridge_roundtrip {α β γ : Type*} (e : α ≃ β) (d : α ≃ γ) (x : β) :
    e (d.symm (d (e.symm x))) = x := by
  rw [d.symm_apply_apply, e.apply_symm_apply]

/-- A native isomorphism of the complete internal equivalence families.
Its maps are constructed from coherent generic sections, including chosen data. -/
noncomputable def equivReindexIso {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ) :
    reindex (equiv A B) σ ≅ equiv (reindex A σ) (reindex B σ) where
  hom := mapOfSections (reindexTo A B σ)
  inv := mapOfSections (reindexFrom A B σ)
  hom_inv_id := mapOfSections_inverse
    (C := reindex (equiv A B) σ) (D := equiv (reindex A σ) (reindex B σ))
    (reindexTo A B σ) (reindexFrom A B σ)
    (reindexTo_natural A B σ) (reindexFrom_natural A B σ)
    (fun τ s => bridge_roundtrip (equivReindexSections A B (τ ≫ σ))
      (equivReindexSections (reindex A σ) (reindex B σ) τ) s)
  inv_hom_id := mapOfSections_inverse
    (C := equiv (reindex A σ) (reindex B σ)) (D := reindex (equiv A B) σ)
    (reindexFrom A B σ) (reindexTo A B σ)
    (reindexFrom_natural A B σ) (reindexTo_natural A B σ)
    (fun τ s => bridge_roundtrip (equivReindexSections (reindex A σ) (reindex B σ) τ)
      (equivReindexSections A B (τ ≫ σ)) s)

/-- The native family map realizes the complete bridge after any further
substitution, so it can act on the generic sections used by clients. -/
theorem equivReindexIso_hom_reindex_sections {Γ Δ Θ : Context.{u}}
    (A B : Family Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (s : Term (reindex (equiv A B) (τ ≫ σ))) :
    Term.map (Functor.whiskerLeft τ.mapElements (equivReindexIso A B σ).hom) s =
      equivReindexSections (reindex A σ) (reindex B σ) τ
        ((equivReindexSections A B (τ ≫ σ)).symm s) :=
  mapOfSections_apply (C := reindex (equiv A B) σ)
    (D := equiv (reindex A σ) (reindex B σ))
    (reindexTo A B σ) (reindexTo_natural A B σ) τ s

/-- The native family map realizes the original full chosen-data section bridge. -/
theorem equivReindexIso_hom_sections {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (s : Term (reindex (equiv A B) σ)) :
    Term.map (equivReindexIso A B σ).hom s =
      equivSections (reindex A σ) (reindex B σ) ((equivReindexSections A B σ).symm s) :=
  (mapOfSections_apply (C := reindex (equiv A B) σ) (D := equiv (reindex A σ) (reindex B σ)) (reindexTo A B σ) (reindexTo_natural A B σ) (𝟙 Δ) s).trans
    (equivReindexSections_id (reindex A σ) (reindex B σ) _ _)

/-- Reindexing the internal family preserves the supplied map and its exact
chosen fiber contractions together. -/
theorem equivReindexIso_hom_encode {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f) :
    Term.map (equivReindexIso A B σ).hom (equivReindexSections A B σ ⟨f,E⟩) =
      equivSections (reindex A σ) (reindex B σ) ⟨f,E⟩ :=
  (equivReindexIso_hom_sections A B σ _).trans
    (congrArg (equivSections (reindex A σ) (reindex B σ))
      ((equivReindexSections A B σ).symm_apply_apply ⟨f,E⟩))

theorem equivReindexIso_inv_encode {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f) :
    Term.map (equivReindexIso A B σ).inv
      (equivSections (reindex A σ) (reindex B σ) ⟨f,E⟩) =
      equivReindexSections A B σ ⟨f,E⟩ :=
  (congrArg (Term.map (equivReindexIso A B σ).inv)
    (equivReindexIso_hom_encode A B σ f E)).symm.trans
      (Term.map_iso_roundtrip (equivReindexIso A B σ) _)

end SquareKit.Cubical.Presheaf.EquivalenceFamilies
