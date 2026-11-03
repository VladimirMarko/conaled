import SquareKit.FamilyCoherence

/-! Experimental dependent sums as composition of display maps.
Dependent second components remain sections of actual chosen pullbacks. -/
noncomputable section
namespace SquareKit.Family.Sum
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {B A Γ Δ : C} (p : A ⟶ Γ) (q : B ⟶ A)

abbrev display : B ⟶ Γ := q ≫ p

def pairTerm (a : Term p) (b : Term (reindex q a.val)) : Term (display p q) :=
  ⟨b.val ≫ comparison q a.val, by
    calc
      _ = (b.val ≫ reindex q a.val) ≫ a.val ≫ p := by
        simp only [display, Category.assoc, pullback.condition_assoc]
      _ = 𝟙 Γ := by rw [b.property, Category.id_comp, a.property]⟩

def first (s : Term (display p q)) : Term p :=
  ⟨s.val ≫ q, by simpa [Category.assoc] using s.property⟩

def second (s : Term (display p q)) : Term (reindex q (first p q s).val) :=
  (termEquiv q (first p q s).val).symm ⟨s.val, rfl⟩

@[reassoc (attr := simp)] theorem second_comparison (s : Term (display p q)) :
    (second p q s).val ≫ comparison q (first p q s).val = s.val :=
  congrArg Subtype.val ((termEquiv q (first p q s).val).apply_symm_apply ⟨s.val, rfl⟩)

@[simp] theorem first_pair (a : Term p) (b : Term (reindex q a.val)) :
    first p q (pairTerm p q a b) = a := by
  apply Subtype.ext
  change (b.val ≫ comparison q a.val) ≫ q = a.val
  rw [Category.assoc, pullback.condition, ← Category.assoc, b.property, Category.id_comp]

/-- Beta retains the full dependent second section after its base-arrow transport. -/
theorem second_pair (a : Term p) (b : Term (reindex q a.val)) :
    (second p q (pairTerm p q a b)).val ≫
      (baseIso q (congrArg Subtype.val (first_pair p q a b))).hom = b.val := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseIso_comparison, second_comparison]
    rfl
  · simp [Category.assoc, (second p q (pairTerm p q a b)).property, b.property]

@[simp] theorem eta (s : Term (display p q)) :
    pairTerm p q (first p q s) (second p q s) = s := by
  apply Subtype.ext
  exact second_comparison p q s

/-- Sum of reindexed families → reindexed sum, using Mathlib horizontal pasting. -/
def substitutionIso (σ : Δ ⟶ Γ) :
    pullback q (comparison p σ) ≅ pullback (display p q) σ :=
  pullbackRightPullbackFstIso p σ q

@[reassoc (attr := simp)] theorem substitutionIso_value (σ : Δ ⟶ Γ) :
    (substitutionIso p q σ).hom ≫ comparison (display p q) σ = comparison q (comparison p σ) := by
  simp [substitutionIso]

@[reassoc (attr := simp)] theorem substitutionIso_display (σ : Δ ⟶ Γ) :
    (substitutionIso p q σ).hom ≫ reindex (display p q) σ =
      reindex q (comparison p σ) ≫ reindex p σ := by simp [substitutionIso]

@[reassoc (attr := simp)] theorem substitutionIso_inv_value (σ : Δ ⟶ Γ) :
    (substitutionIso p q σ).inv ≫ comparison q (comparison p σ) = comparison (display p q) σ := by
  simp [substitutionIso]

@[reassoc (attr := simp)] theorem substitutionIso_inv_display (σ : Δ ⟶ Γ) :
    (substitutionIso p q σ).inv ≫ reindex q (comparison p σ) ≫ reindex p σ =
      reindex (display p q) σ := by simp [substitutionIso]

/-- Substitute a sum section, then transport it to the sum of reindexed families. -/
def termSub (σ : Δ ⟶ Γ) (s : Term (display p q)) :
    Term (display (reindex p σ) (reindex q (comparison p σ))) :=
  ⟨(Family.termSub (display p q) σ s).val ≫ (substitutionIso p q σ).inv,
    by simp [Category.assoc, (Family.termSub (display p q) σ s).property]⟩

/-- The dependent value used to substitute a second component. -/
def secondSubValue (σ : Δ ⟶ Γ) (a : Term p) (b : Term (reindex q a.val)) :
    Δ ⟶ pullback q (comparison p σ) :=
  Family.pair q (comparison p σ) (σ ≫ b.val ≫ comparison q a.val) (Family.termSub p σ a).val
    (by simp only [Category.assoc, pullback.condition, ← Category.assoc b.val, b.property,
      Category.id_comp, termSub_comparison])

@[reassoc (attr := simp)] theorem secondSubValue_display (σ : Δ ⟶ Γ) (a : Term p)
    (b : Term (reindex q a.val)) :
    secondSubValue p q σ a b ≫ reindex q (comparison p σ) = (Family.termSub p σ a).val := by
  simp [secondSubValue]

@[reassoc (attr := simp)] theorem secondSubValue_value (σ : Δ ⟶ Γ) (a : Term p)
    (b : Term (reindex q a.val)) :
    secondSubValue p q σ a b ≫ comparison q (comparison p σ) = σ ≫ b.val ≫ comparison q a.val := by
  simp [secondSubValue]

def secondSub (σ : Δ ⟶ Γ) (a : Term p) (b : Term (reindex q a.val)) :
    Term (reindex (reindex q (comparison p σ)) (Family.termSub p σ a).val) :=
  (termEquiv (reindex q (comparison p σ)) (Family.termSub p σ a).val).symm
    ⟨secondSubValue p q σ a b, secondSubValue_display p q σ a b⟩

@[reassoc (attr := simp)] theorem secondSub_comparison (σ : Δ ⟶ Γ) (a : Term p)
    (b : Term (reindex q a.val)) :
    (secondSub p q σ a b).val ≫ comparison (reindex q (comparison p σ)) (Family.termSub p σ a).val =
      secondSubValue p q σ a b :=
  congrArg Subtype.val ((termEquiv (reindex q (comparison p σ)) (Family.termSub p σ a).val).apply_symm_apply _)

theorem pair_substitution (σ : Δ ⟶ Γ) (a : Term p) (b : Term (reindex q a.val)) :
    (pairTerm (reindex p σ) (reindex q (comparison p σ)) (Family.termSub p σ a)
      (secondSub p q σ a b)).val ≫ (substitutionIso p q σ).hom =
        (Family.termSub (display p q) σ (pairTerm p q a b)).val := by
  apply pullback.hom_ext <;> simp [Category.assoc, pairTerm]

/-- The first component commutes with sum substitution. -/
theorem first_substitution (σ : Δ ⟶ Γ) (s : Term (display p q)) :
    first (reindex p σ) (reindex q (comparison p σ)) (termSub p q σ s) =
      Family.termSub p σ (first p q s) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [first, termSub, Category.assoc, ← pullback.condition,
      Family.termSub_comparison_assoc]
  · simp [first, termSub, Category.assoc, (Family.termSub (display p q) σ s).property]

/-- The full second section commutes after transporting the first-component equation. -/
theorem second_substitution (σ : Δ ⟶ Γ) (s : Term (display p q)) :
    (second (reindex p σ) (reindex q (comparison p σ)) (termSub p q σ s)).val ≫
      (baseIso (reindex q (comparison p σ)) (congrArg Subtype.val (first_substitution p q σ s))).hom =
        (secondSub p q σ (first p q s) (second p q s)).val := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseIso_comparison, second_comparison, secondSub_comparison]
    apply pullback.hom_ext
    · simp [termSub, Category.assoc]
    · rw [secondSubValue_display]
      exact congrArg Subtype.val (first_substitution p q σ s)
  · simp [Category.assoc, (second (reindex p σ) (reindex q (comparison p σ)) (termSub p q σ s)).property,
      (secondSub p q σ (first p q s) (second p q s)).property]
end SquareKit.Family.Sum
