import SquareKit.SplitSheaf

/-! Experimental transport and display coherence for split sheaf substitution.
The split equations are definitional; ordinary chosen pullbacks retain their
canonical FamilyCoherence comparisons. -/
noncomputable section
namespace SquareKit.SplitSheaf
open CategoryTheory Limits
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ Δ Ξ Ω : Sheaf J (Type w)}

theorem transport_sub {A B : Ty Γ} (h : A = B) (t : Tm A) (σ : Δ ⟶ Γ) :
    transport (congrArg (fun A => tySub A σ) h) (tmSub t σ) = tmSub (transport h t) σ := by
  cases h
  rfl

theorem transport_id {A : Ty Γ} (t : Tm A) : transport (tySub_id A) (tmSub t (𝟙 Γ)) = t := rfl
theorem transport_comp {A : Ty Γ} (t : Tm A) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    transport (tySub_comp A σ τ) (tmSub (tmSub t σ) τ) = tmSub t (τ ≫ σ) := rfl

theorem tySub_triple (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    tySub (tySub (tySub A σ) τ) υ = tySub A (υ ≫ (τ ≫ σ)) := rfl

theorem lift_triple (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    lift (tySub (tySub A σ) τ) υ ≫ lift (tySub A σ) τ ≫ lift A σ = lift A (υ ≫ (τ ≫ σ)) := rfl

/-- Two split transport routes through a triple substitution agree. -/
theorem transport_triple {A : Ty Γ} (t : Tm A) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    transport (tySub_triple A σ τ υ) (tmSub (tmSub (tmSub t σ) τ) υ) =
      transport (tySub_comp A σ (υ ≫ τ)) (tmSub (tmSub t σ) (υ ≫ τ)) := rfl

/-- This route sends a split iterated extension to the ordinary iterated
pullback, retaining the inner substitution comparison. -/
def doubleComparison (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    Ext (tySub (tySub A σ) τ) ⟶ pullback (Family.reindex (p A) σ) τ :=
  (substitutionIso (tySub A σ) τ).hom ≫
    Family.map (p (tySub A σ)) (Family.reindex (p A) σ) τ
      (substitutionIso A σ).hom (substitution_display A σ)

theorem double_display (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    doubleComparison A σ τ ≫ Family.reindex (Family.reindex (p A) σ) τ =
      p (tySub (tySub A σ) τ) := by
  simp only [doubleComparison, Category.assoc, Family.map_display]
  exact substitution_display (tySub A σ) τ

def tripleComparison (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    Ext (tySub (tySub (tySub A σ) τ) υ) ⟶ pullback (Family.reindex (Family.reindex (p A) σ) τ) υ :=
  (substitutionIso (tySub (tySub A σ) τ) υ).hom ≫
    Family.map (p (tySub (tySub A σ) τ)) (Family.reindex (Family.reindex (p A) σ) τ) υ
      (doubleComparison A σ τ) (double_display A σ τ)

/-- The two ordinary triple comparison routes still agree after the split
comparison. This uses the existing chosen-pullback associativity theorem. -/
theorem substitution_associativity (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    tripleComparison A σ τ υ ≫ Family.innerRoute (p A) σ τ υ =
      tripleComparison A σ τ υ ≫ Family.outerRoute (p A) σ τ υ := by
  rw [Family.associativity]

/-- Triple substitution also agrees with substitution by the composite. -/
theorem triple_composite (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    tripleComparison A σ τ υ ≫ Family.innerRoute (p A) σ τ υ =
      (substitutionIso A (υ ≫ (τ ≫ σ))).hom := by
  apply pullback.hom_ext
  · simp only [Family.innerRoute, Category.assoc, Family.compositionIso_comparison,
      Family.map_comparison_assoc]
    simp only [tripleComparison, doubleComparison, Category.assoc, Family.map_comparison_assoc]
    simp only [substitution_value_assoc, substitution_value]
    exact (substitution_value A (υ ≫ (τ ≫ σ))).symm
  · simp only [Family.innerRoute, Category.assoc, Family.compositionIso_display, Family.map_display]
    simp only [tripleComparison, Category.assoc, Family.map_display]
    exact (substitution_display (tySub (tySub A σ) τ) υ).trans
      (substitution_display A (υ ≫ (τ ≫ σ))).symm

/-- Terms of an arbitrary ordinary display, using the actual fiber/total
reconstruction and the split section equivalence. -/
def displayTerms {B : Sheaf J (Type w)} (d : B ⟶ Γ) : Tm (ofDisplay d) ≃ Family.Term d :=
  (terms (ofDisplay d)).trans {
    toFun t := Family.mapTerm _ _ (displayIso d).hom (displayIso_projection d) t
    invFun t := Family.mapTerm _ _ (displayIso d).inv
      (by rw [← displayIso_projection, Iso.inv_hom_id_assoc]) t
    left_inv t := by apply Subtype.ext; simp [Family.mapTerm]
    right_inv t := by apply Subtype.ext; simp [Family.mapTerm] }

/-- Taking actual display fibers recovers each accepted section-indexed family. -/
def familyRecovery (A : Ty Γ) : (ofDisplay (p A)).family ≅ A.family :=
  ElementFamilies.fiberTotalIso Γ.obj A.family

@[simp] theorem lift_q (A : Ty Γ) (σ : Δ ⟶ Γ) :
    tmSub (q A) (lift A σ) = q (tySub A σ) := rfl

/-- The split substitution comparison and reconstruction jointly recover
ordinary substitution of terms of any display. -/
theorem display_term_substitution {B : Sheaf J (Type w)} (d : B ⟶ Γ)
    (σ : Δ ⟶ Γ) (t : Tm (ofDisplay d)) :
    (terms (tySub (ofDisplay d) σ) (tmSub t σ)).val ≫
      (substitutionIso (ofDisplay d) σ).hom ≫
      Family.map (p (ofDisplay d)) d σ (displayIso d).hom (displayIso_projection d) =
        (Family.termSub d σ (displayTerms d t)).val := by
  rw [← Category.assoc, term_substitution, Family.map_termSub]
  rfl

end SquareKit.SplitSheaf
