import SquareKit.FamilySum
import SquareKit.TypeFamilyCoherence

/-! Experimental comparison of composed display maps with the existing split
Sigma operations. The dependent second component is retained throughout. -/
noncomputable section
namespace SquareKit.TypeFamily.Sum
open CategoryTheory Limits Family
universe u
variable {Γ Δ : Type u} (A : Γ → Type u) (B : DependentSquares.Ext Γ A → Type u)

/-- Reassociate dependent pairs without changing either component. -/
def totalIso : DependentSquares.Ext (DependentSquares.Ext Γ A) B ≅
    DependentSquares.Ext Γ (DependentSquares.sigmaTy A B) where
  hom := ↾fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  inv := ↾fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

@[reassoc (attr := simp)] theorem totalIso_display :
    (totalIso A B).hom ≫ display (DependentSquares.sigmaTy A B) = display B ≫ display A := rfl

@[reassoc (attr := simp)] theorem totalIso_inv_display :
    (totalIso A B).inv ≫ (display B ≫ display A) = display (DependentSquares.sigmaTy A B) := rfl

def sumSection (c : DependentSquares.Tm (DependentSquares.sigmaTy A B)) :
    Term (Family.Sum.display (display A) (display B)) :=
  mapTerm (display (DependentSquares.sigmaTy A B)) (display B ≫ display A)
    (totalIso A B).inv (totalIso_inv_display A B) (asSection _ c)

/-- Translate the native dependent second term through the existing pullback comparison. -/
def secondSection (a : DependentSquares.Tm A)
    (b : DependentSquares.Tm (DependentSquares.tySub B (DependentSquares.extend DependentSquares.idSub a))) :
    Term (reindex (display B) (asSection A a).val) :=
  ⟨(asSection _ b).val ≫ (pullbackIso B (DependentSquares.extend DependentSquares.idSub a)).hom, by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (asSection _ b).val ≫ k)
        (pullbackIso_display B (DependentSquares.extend DependentSquares.idSub a))).trans
          (asSection _ b).property)⟩

@[reassoc (attr := simp)] theorem secondSection_value (a : DependentSquares.Tm A)
    (b : DependentSquares.Tm (DependentSquares.tySub B (DependentSquares.extend DependentSquares.idSub a))) :
    (secondSection A B a b).val ≫ comparison (display B) (asSection A a).val =
      (↾fun γ => ⟨⟨γ, a γ⟩, b γ⟩) := by
  change ((asSection _ b).val ≫ (pullbackIso B (DependentSquares.extend DependentSquares.idSub a)).hom) ≫
    comparison (display B) (↾(DependentSquares.extend DependentSquares.idSub a)) = _
  rw [Category.assoc, pullbackIso_comparison]
  rfl

theorem pairing (a : DependentSquares.Tm A)
    (b : DependentSquares.Tm (DependentSquares.tySub B (DependentSquares.extend DependentSquares.idSub a))) :
    Family.Sum.pairTerm (display A) (display B) (asSection A a) (secondSection A B a b) =
      sumSection A B (DependentSquares.pairTerm a b) := by
  apply Subtype.ext
  exact secondSection_value A B a b

theorem first_projection (c : DependentSquares.Tm (DependentSquares.sigmaTy A B)) :
    Family.Sum.first (display A) (display B) (sumSection A B c) =
      asSection A (DependentSquares.fstTerm c) := rfl

theorem second_projection (c : DependentSquares.Tm (DependentSquares.sigmaTy A B)) :
    (Family.Sum.second (display A) (display B) (sumSection A B c)).val =
      (secondSection A B (DependentSquares.fstTerm c) (DependentSquares.sndTerm c)).val := by
  apply pullback.hom_ext
  · rw [Family.Sum.second_comparison]
    exact (secondSection_value A B (DependentSquares.fstTerm c) (DependentSquares.sndTerm c)).symm
  · exact (Family.Sum.second (display A) (display B) (sumSection A B c)).property.trans
      (secondSection A B (DependentSquares.fstTerm c) (DependentSquares.sndTerm c)).property.symm

theorem split_eta (c : DependentSquares.Tm (DependentSquares.sigmaTy A B)) :
    sumSection A B (DependentSquares.pairTerm (DependentSquares.fstTerm c) (DependentSquares.sndTerm c)) =
      sumSection A B c := congrArg (sumSection A B) (DependentSquares.sigma_eta c)

/-- The existing strict sigma_subst equation aligns the split family objects. -/
def substitutionTypeIso (σ : Δ → Γ) :
    DependentSquares.Ext Δ (DependentSquares.sigmaTy (DependentSquares.tySub A σ)
      (DependentSquares.tySub B (DependentSquares.lift σ))) ≅
        DependentSquares.Ext Δ (DependentSquares.tySub (DependentSquares.sigmaTy A B) σ) :=
  (eqToIso (congrArg (DependentSquares.Ext Δ) (DependentSquares.sigma_subst A B σ))).symm

/-- Compare the split substituted tower to the tower of chosen pullbacks. -/
def towerComparison (σ : Δ → Γ) :
    DependentSquares.Ext (DependentSquares.Ext Δ (DependentSquares.tySub A σ))
      (DependentSquares.tySub B (DependentSquares.lift σ)) ⟶
        pullback (display B) (comparison (display A) (↾σ)) :=
  Family.pair (display B) (comparison (display A) (↾σ))
    (↾(DependentSquares.lift (A := B) (DependentSquares.lift σ)))
    (display (DependentSquares.tySub B (DependentSquares.lift σ)) ≫ (pullbackIso A σ).hom)
    (by rw [Category.assoc, pullbackIso_comparison]; rfl)

@[reassoc (attr := simp)] theorem towerComparison_value (σ : Δ → Γ) :
    towerComparison A B σ ≫ comparison (display B) (comparison (display A) (↾σ)) =
      ↾(DependentSquares.lift (A := B) (DependentSquares.lift σ)) := by simp [towerComparison]

@[reassoc (attr := simp)] theorem towerComparison_base (σ : Δ → Γ) :
    towerComparison A B σ ≫ reindex (display B) (comparison (display A) (↾σ)) =
      display (DependentSquares.tySub B (DependentSquares.lift σ)) ≫ (pullbackIso A σ).hom := by
  simp [towerComparison]

/-- The route using split sigma_subst and the established Type pullback comparison. -/
def splitSubRoute (σ : Δ → Γ) :=
  (totalIso (DependentSquares.tySub A σ) (DependentSquares.tySub B (DependentSquares.lift σ))).hom ≫
    (substitutionTypeIso A B σ).hom ≫ (pullbackIso (DependentSquares.sigmaTy A B) σ).hom ≫
      Family.map (display (DependentSquares.sigmaTy A B)) (display B ≫ display A) (↾σ)
        (totalIso A B).inv (totalIso_inv_display A B)

theorem substitution_comparison (σ : Δ → Γ) :
    towerComparison A B σ ≫ (Family.Sum.substitutionIso (display A) (display B) (↾σ)).hom =
      splitSubRoute A B σ := by
  apply pullback.hom_ext
  · simp [splitSubRoute, Category.assoc, pullbackIso_comparison_assoc]
    rfl
  · simp [splitSubRoute, Category.assoc]
    rfl

/-- Existing pair substitution agrees with the interpreted split sum section. -/
theorem split_pair_substitution (σ : Δ → Γ) (a : DependentSquares.Tm A)
    (b : DependentSquares.Tm (DependentSquares.tySub B (DependentSquares.extend DependentSquares.idSub a))) :
    sumSection (DependentSquares.tySub A σ) (DependentSquares.tySub B (DependentSquares.lift σ))
      (DependentSquares.tmSub (DependentSquares.pairTerm a b) σ) =
    Family.Sum.pairTerm (display (DependentSquares.tySub A σ))
      (display (DependentSquares.tySub B (DependentSquares.lift σ)))
      (asSection _ (DependentSquares.tmSub a σ))
      (secondSection _ _ (DependentSquares.tmSub a σ) (DependentSquares.tmSub b σ)) := by
  rw [DependentSquares.pair_subst]
  exact (pairing _ _ _ _).symm
end SquareKit.TypeFamily.Sum
