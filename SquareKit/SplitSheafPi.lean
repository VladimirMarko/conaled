import SquareKit.SplitFunctionSheaf
import SquareKit.SplitSheafCoherence

/-! Experimental substitution-stable dependent functions in split sheaf families.
Formation uses compatible values over all restrictions. Stability is propositional;
ordinary split substitution and comprehension identity/composition are definitional. -/
noncomputable section
namespace SquareKit.SplitSheafPi
open CategoryTheory SplitSheaf
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ Δ Ξ Ω : Sheaf J (Type (max u v))}

abbrev pi (A : Ty Γ) (B : Ty (Ext A)) : Ty Γ := SplitFunctionSheaf.piType A B
abbrev lam (A : Ty Γ) {B : Ty (Ext A)} (t : Tm B) : Tm (pi A B) := SplitFunctionDiagram.lam A.family t
abbrev unlam (A : Ty Γ) {B : Ty (Ext A)} (t : Tm (pi A B)) : Tm B := SplitFunctionDiagram.unlam A.family t
abbrev terms (A : Ty Γ) (B : Ty (Ext A)) : Tm B ≃ Tm (pi A B) := SplitFunctionDiagram.terms A.family B.family

@[simp] theorem beta (A : Ty Γ) {B : Ty (Ext A)} (t : Tm B) : unlam A (lam A t) = t :=
  SplitFunctionDiagram.beta A.family t
@[simp] theorem eta (A : Ty Γ) {B : Ty (Ext A)} (t : Tm (pi A B)) : lam A (unlam A t) = t :=
  SplitFunctionDiagram.eta A.family t

/-- A proved equality of families, obtained from equality of restriction diagrams. -/
theorem substitution (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    tySub (pi A B) σ = pi (tySub A σ) (tySub B (lift A σ)) := by
  apply Ty.ext
  exact (SplitFunctionDiagram.pi_sub A.family B.family σ.hom).symm

theorem lam_substitution (A : Ty Γ) {B : Ty (Ext A)} (t : Tm B) (σ : Δ ⟶ Γ) :
    transport (substitution A B σ) (tmSub (lam A t) σ) =
      lam (tySub A σ) (tmSub t (lift A σ)) := by
  apply eq_of_heq
  exact (eqRec_heq _ _).trans (SplitFunctionDiagram.lam_sub_heq A.family t σ.hom)

theorem unlam_substitution (A : Ty Γ) {B : Ty (Ext A)} (t : Tm (pi A B)) (σ : Δ ⟶ Γ) :
    unlam (tySub A σ) (transport (substitution A B σ) (tmSub t σ)) = tmSub (unlam A t) (lift A σ) := by
  have h := congrArg (unlam (tySub A σ)) (lam_substitution A (unlam A t) σ)
  simpa only [eta, beta] using h

/-- Application substitutes the actual argument into the dependent result family. -/
def app (A : Ty Γ) {B : Ty (Ext A)} (t : Tm (pi A B)) (a : Tm A) :
    Tm (tySub B (pair A (𝟙 Γ) a)) := tmSub (unlam A t) (pair A (𝟙 Γ) a)

@[simp] theorem app_beta (A : Ty Γ) {B : Ty (Ext A)} (t : Tm B) (a : Tm A) :
    app A (lam A t) a = tmSub t (pair A (𝟙 Γ) a) := by rw [app, beta]

theorem app_substitution (A : Ty Γ) {B : Ty (Ext A)} (t : Tm (pi A B)) (a : Tm A) (σ : Δ ⟶ Γ) :
    tmSub (app A t a) σ =
      app (tySub A σ) (B := tySub B (lift A σ))
        (transport (substitution A B σ) (tmSub t σ)) (tmSub a σ) := by
  unfold app
  rw [unlam_substitution]
  rfl

/-- Identity transport is the identity, including its proof argument. -/
theorem substitution_id (A : Ty Γ) (B : Ty (Ext A)) (t : Tm (pi A B)) :
    transport (substitution A B (𝟙 Γ)) (tmSub t (𝟙 Γ)) = t := rfl

/-- Successive transports agree with direct substitution by proof irrelevance. -/
theorem substitution_comp (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    (t : Tm (pi A B)) :
    transport (substitution (tySub A σ) (tySub B (lift A σ)) τ)
      (tmSub (transport (substitution A B σ) (tmSub t σ)) τ) =
    transport (substitution A B (τ ≫ σ)) (tmSub t (τ ≫ σ)) := by
  erw [← transport_sub, transport_trans]
  rfl

theorem substitution_triple (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ)
    (t : Tm (pi A B)) :
    transport (substitution (tySub (tySub A σ) τ) (tySub (tySub B (lift A σ)) (lift (tySub A σ) τ)) υ)
      (tmSub (transport (substitution (tySub A σ) (tySub B (lift A σ)) τ)
        (tmSub (transport (substitution A B σ) (tmSub t σ)) τ)) υ) =
    transport (substitution A B (υ ≫ (τ ≫ σ))) (tmSub t (υ ≫ (τ ≫ σ))) := by
  rw [substitution_comp, substitution_comp]
  rfl


/-- Abstraction over a substituted context, retaining its exact target type. -/
def lamAt (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (t : Tm (tySub B (lift A σ))) :
    Tm (tySub (pi A B) σ) := transport (substitution A B σ).symm (lam (tySub A σ) t)

def unlamAt (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (t : Tm (tySub (pi A B) σ)) :
    Tm (tySub B (lift A σ)) := unlam (tySub A σ) (transport (substitution A B σ) t)

@[simp] theorem betaAt (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (t : Tm (tySub B (lift A σ))) :
    unlamAt A B σ (lamAt A B σ t) = t := by
  unfold unlamAt lamAt
  rw [transport_trans]
  exact beta _ t

@[simp] theorem etaAt (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (t : Tm (tySub (pi A B) σ)) :
    lamAt A B σ (unlamAt A B σ t) = t := by
  unfold unlamAt lamAt
  rw [eta, transport_trans]
  rfl

theorem lamAt_natural (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    (t : Tm (tySub B (lift A σ))) :
    tmSub (lamAt A B σ t) τ =
      lamAt A B (τ ≫ σ) (tmSub t (lift (tySub A σ) τ)) := by
  unfold lamAt
  apply eq_of_heq
  have h := lam_substitution (tySub A σ) t τ
  have hh := (eqRec_heq _ _).symm.trans (heq_of_eq h)
  have hs := transport_sub (substitution A B σ).symm (lam (tySub A σ) t) τ
  exact (heq_of_eq hs.symm).trans ((eqRec_heq _ _).trans (hh.trans (eqRec_heq _ _).symm))

theorem unlamAt_natural (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    (t : Tm (tySub (pi A B) σ)) :
    unlamAt A B (τ ≫ σ) (tmSub t τ) =
      tmSub (unlamAt A B σ t) (lift (tySub A σ) τ) := by
  have h := congrArg (unlamAt A B (τ ≫ σ)) (lamAt_natural A B σ τ (unlamAt A B σ t))
  simp only [etaAt] at h
  exact h.trans (betaAt A B (τ ≫ σ) _)

end SquareKit.SplitSheafPi
