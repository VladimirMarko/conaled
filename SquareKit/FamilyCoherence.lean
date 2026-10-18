import SquareKit.Family

/-! Experimental coherence for the existing chosen pullback substitutions.
Family maps are ordinary commuting morphisms; comparison routes include the
transport induced by equal base arrows. -/
noncomputable section
namespace SquareKit.Family
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B D Γ Δ Ξ Ω : C}

def map (p : A ⟶ Γ) (q : B ⟶ Γ) (σ : Δ ⟶ Γ) (f : A ⟶ B) (h : f ≫ q = p) :
    pullback p σ ⟶ pullback q σ :=
  pair q σ (comparison p σ ≫ f) (reindex p σ)
    (by rw [Category.assoc, h, pullback.condition])

@[reassoc (attr := simp)] theorem map_comparison (p : A ⟶ Γ) (q : B ⟶ Γ) (σ : Δ ⟶ Γ)
    (f : A ⟶ B) (h) : map p q σ f h ≫ comparison q σ = comparison p σ ≫ f := by
  simp [map]

@[reassoc (attr := simp)] theorem map_display (p : A ⟶ Γ) (q : B ⟶ Γ) (σ : Δ ⟶ Γ)
    (f : A ⟶ B) (h) : map p q σ f h ≫ reindex q σ = reindex p σ := by simp [map]

@[simp] theorem map_id (p : A ⟶ Γ) (σ : Δ ⟶ Γ) :
    map p p σ (𝟙 A) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [map]

theorem map_comp (p : A ⟶ Γ) (q : B ⟶ Γ) (r : D ⟶ Γ) (σ : Δ ⟶ Γ)
    (f : A ⟶ B) (g : B ⟶ D) (hf) (hg) :
    map p r σ (f ≫ g) (by simp [Category.assoc, hg, hf]) =
      map p q σ f hf ≫ map q r σ g hg := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Transport only along equality of the base arrows. -/
def baseIso (p : A ⟶ Γ) {σ τ : Δ ⟶ Γ} (h : σ = τ) : pullback p σ ≅ pullback p τ :=
  eqToIso (congrArg (fun σ : Δ ⟶ Γ => pullback p σ) h)

@[reassoc (attr := simp)] theorem baseIso_comparison (p : A ⟶ Γ) {σ τ : Δ ⟶ Γ} (h : σ = τ) :
    (baseIso p h).hom ≫ comparison p τ = comparison p σ := by cases h; simp [baseIso]

@[reassoc (attr := simp)] theorem baseIso_display (p : A ⟶ Γ) {σ τ : Δ ⟶ Γ} (h : σ = τ) :
    (baseIso p h).hom ≫ reindex p τ = reindex p σ := by cases h; simp [baseIso]

theorem identity_natural (p : A ⟶ Γ) (q : B ⟶ Γ) (f : A ⟶ B) (h) :
    map p q (𝟙 Γ) f h ≫ (identityIso q).hom = (identityIso p).hom ≫ f := by
  exact map_comparison p q (𝟙 Γ) f h

theorem composition_natural (p : A ⟶ Γ) (q : B ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    (f : A ⟶ B) (h) :
    map (reindex p σ) (reindex q σ) τ (map p q σ f h) (map_display p q σ f h) ≫
        (compositionIso q σ τ).hom =
      (compositionIso p σ τ).hom ≫ map p q (τ ≫ σ) f h := by
  apply pullback.hom_ext <;> simp [Category.assoc, compositionIso_comparison_assoc]

/-- First substitute σ, then the identity of its source. -/
theorem right_unit (p : A ⟶ Γ) (σ : Δ ⟶ Γ) :
    (compositionIso p σ (𝟙 Δ)).hom ≫ (baseIso p (Category.id_comp σ)).hom =
      (identityIso (reindex p σ)).hom := by
  apply pullback.hom_ext <;> simp [Category.assoc, identityIso, pullback.condition]

/-- First substitute the identity of the original base, then σ. -/
theorem left_unit (p : A ⟶ Γ) (σ : Δ ⟶ Γ) :
    (compositionIso p (𝟙 Γ) σ).hom ≫ (baseIso p (Category.comp_id σ)).hom =
      map (reindex p (𝟙 Γ)) p σ (identityIso p).hom (identityIso_display p) := by
  apply pullback.hom_ext <;> simp [Category.assoc, identityIso, map]

/-- Compose the inner two substitutions before the outer one. -/
def innerRoute (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    pullback (reindex (reindex p σ) τ) υ ⟶ pullback p (υ ≫ (τ ≫ σ)) :=
  map (reindex (reindex p σ) τ) (reindex p (τ ≫ σ)) υ
      (compositionIso p σ τ).hom (compositionIso_display p σ τ) ≫
    (compositionIso p (τ ≫ σ) υ).hom

/-- Compose the outer two first, then transport categorical associativity. -/
def outerRoute (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    pullback (reindex (reindex p σ) τ) υ ⟶ pullback p (υ ≫ (τ ≫ σ)) :=
  (compositionIso (reindex p σ) τ υ).hom ≫ (compositionIso p σ (υ ≫ τ)).hom ≫
    (baseIso p (Category.assoc υ τ σ)).hom

theorem associativity (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    innerRoute p σ τ υ = outerRoute p σ τ υ := by
  apply pullback.hom_ext <;>
    simp [innerRoute, outerRoute, Category.assoc, compositionIso_comparison_assoc]

/-- Sections transported along a family map remain sections. -/
def mapTerm (p : A ⟶ Γ) (q : B ⟶ Γ) (f : A ⟶ B) (h : f ≫ q = p) (t : Term p) : Term q :=
  ⟨t.val ≫ f, by simp [Category.assoc, h, t.property]⟩

theorem map_termSub (p : A ⟶ Γ) (q : B ⟶ Γ) (σ : Δ ⟶ Γ)
    (f : A ⟶ B) (h) (t : Term p) :
    (termSub p σ t).val ≫ map p q σ f h = (termSub q σ (mapTerm p q f h t)).val := by
  apply pullback.hom_ext <;> simp [map, termSub, pair, mapTerm, Category.assoc]

theorem baseIso_term (p : A ⟶ Γ) {σ τ : Δ ⟶ Γ} (h : σ = τ) (t : Term p) :
    (termSub p σ t).val ≫ (baseIso p h).hom = (termSub p τ t).val := by
  cases h
  simp [baseIso]

theorem triple_term_outer (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) (t : Term p) :
    (termSub (reindex (reindex p σ) τ) υ (termSub (reindex p σ) τ (termSub p σ t))).val ≫
      outerRoute p σ τ υ = (termSub p (υ ≫ (τ ≫ σ)) t).val := by
  simp only [outerRoute, ← Category.assoc, termSub_composition]
  exact baseIso_term p (Category.assoc υ τ σ) t

theorem triple_term_inner (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) (t : Term p) :
    (termSub (reindex (reindex p σ) τ) υ (termSub (reindex p σ) τ (termSub p σ t))).val ≫
      innerRoute p σ τ υ = (termSub p (υ ≫ (τ ≫ σ)) t).val := by
  rw [associativity]
  exact triple_term_outer p σ τ υ t

theorem right_unit_term (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (t : Term p) :
    (termSub (reindex p σ) (𝟙 Δ) (termSub p σ t)).val ≫
      (compositionIso p σ (𝟙 Δ)).hom ≫ (baseIso p (Category.id_comp σ)).hom =
        (termSub p σ t).val := by
  rw [right_unit]
  exact termSub_identity _ _

theorem left_unit_term (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (t : Term p) :
    (termSub (reindex p (𝟙 Γ)) σ (termSub p (𝟙 Γ) t)).val ≫
      (compositionIso p (𝟙 Γ) σ).hom ≫ (baseIso p (Category.comp_id σ)).hom =
        (termSub p σ t).val := by
  have ht : mapTerm (reindex p (𝟙 Γ)) p (identityIso p).hom (identityIso_display p)
      (termSub p (𝟙 Γ) t) = t := Subtype.ext (termSub_identity p t)
  rw [left_unit, map_termSub, ht]
end SquareKit.Family
