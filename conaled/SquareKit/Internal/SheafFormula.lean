import SquareKit.Internal.SheafContexts

/-! Experimental closed predicates for the existing regular formulas.
Relation closure is an explicit theorem hypothesis, not a new model structure.
This module does not prove source-rule soundness.
-/
namespace SquareKit.Internal.SheafContexts
open CategoryTheory Opposite
universe u v w
variable {J : Type v} [SmallCategory J] {K : GrothendieckTopology J}
variable {S : Type u} {F P : S → S → Type u}
variable (M : Presheaf.Model.{u,v,w} (J := J) F P)
variable (hM : ∀ s, Presieve.IsSheaf K (M.carrier s))

/-- The relation product is the same two-variable environment, componentwise. -/
def pairIso (s t : S) : M.context [s,t] ≅ Presheaf.product (M.carrier s) (M.carrier t) where
  hom := { app _ := ↾fun ρ => (ρ .zero, ρ (.succ .zero)) }
  inv := {
    app j := ↾fun p => Env.extend p.1 (Env.extend p.2
      (show Env (M.fiber j) [] from fun {_} i => nomatch i))
    naturality := by
      intro j k f; ext p a i
      cases i with
      | zero => rfl
      | succ i =>
        cases i with
        | zero => rfl
        | succ i => nomatch i }
  hom_inv_id := by
    ext j ρ a i
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => nomatch i
  inv_hom_id := rfl

include hM in
theorem product_isSheaf (s t : S) :
    Presieve.IsSheaf K (Presheaf.product (M.carrier s) (M.carrier t)) :=
  Presieve.isSheaf_iso K (pairIso M s t) (context_isSheaf M hM [s,t])

abbrev product (s t : S) : Sheaf K (Type (max u w)) :=
  ⟨Presheaf.product (M.carrier s) (M.carrier t),
    (isSheaf_iff_isSheaf_of_type _ _).mpr (product_isSheaf M hM s t)⟩

def pairTerms (a : Term F Γ s) (b : Term F Γ t) : context M hM Γ ⟶ product M hM s t :=
  ⟨{ app j := ↾fun ρ => (a.eval (M.fiber j) ρ, b.eval (M.fiber j) ρ)
     naturality := by intro j k f; ext ρ; exact Prod.ext (M.eval_restrict f ρ a) (M.eval_restrict f ρ b) }⟩

include hM in
/-- Equality is closed because carrier sections are separated on covers. -/
theorem equality_isSheaf (a b : Term F Γ s) : Presieve.IsSheaf K (M.equality a b).toFunctor := by
  apply (Subfunctor.isSheaf_iff _ (context_isSheaf M hM Γ)).mpr
  intro U ρ hρ
  rcases U with ⟨U⟩
  apply (hM s _ hρ).isSeparatedFor.ext
  intro V f hf
  change a.eval _ (M.restrict f.op ρ) = b.eval _ (M.restrict f.op ρ) at hf
  rw [M.eval_restrict, M.eval_restrict] at hf
  exact hf

include hM in
theorem atom_isSheaf (r : P s t) (a : Term F Γ s) (b : Term F Γ t)
    (hr : Presieve.IsSheaf K (M.relation r).toFunctor) :
    Presieve.IsSheaf K (M.atom r a b).toFunctor := by
  exact SquareKit.SheafImage.preimage_isSheaf (B := product M hM s t)
    (M.relation r) (pairTerms M hM a b) hr

/-- Existence uses local image, while the other constructors reuse subfunctors. -/
def formula : {Γ : List S} → Formula F Γ P → Subfunctor (M.context Γ)
  | _, .atom r a b => M.atom r a b
  | _, .eq a b => M.equality a b
  | _, .conj p q => formula p ⊓ formula q
  | _, .ex p => SquareKit.SheafImage.localImage (formula p) (projection M hM)

/-- Formula closure follows from carrier and atomic-relation closure. -/
theorem formula_isSheaf
    (hR : ∀ {s t} (r : P s t), Presieve.IsSheaf K (M.relation r).toFunctor)
    (p : Formula F Γ P) : Presieve.IsSheaf K (formula M hM p).toFunctor := by
  induction p with
  | atom r a b => exact atom_isSheaf M hM r a b (hR r)
  | eq a b => exact equality_isSheaf M hM a b
  | conj p q hp hq =>
    exact SquareKit.SheafImage.inf_isSheaf (B := context M hM _) _ _ hp hq
  | ex p _ => exact SquareKit.SheafImage.localImage_isSheaf _ _

/-- Substitution under an existential uses the categorical context pullback law. -/
theorem formula_substitution (p : Formula F Γ P) (σ : Sub F Γ Δ) :
    formula M hM (p.subst σ) = (formula M hM p).preimage (substitution M hM σ).hom := by
  induction p generalizing Δ with
  | atom r a b => exact M.formula_substitution (.atom r a b) σ
  | eq a b => exact M.equality_substitution a b σ
  | conj p q hp hq =>
    change formula M hM (p.subst σ) ⊓ formula M hM (q.subst σ) = _
    rw [hp, hq]
    rfl
  | ex p ih =>
    change SquareKit.SheafImage.localImage (formula M hM (p.subst σ.lift)) (projection M hM) = _
    rw [ih]
    exact (exists_substitution M hM (formula M hM p) σ).symm

/-- Restriction stability applies to all formula predicates, including existence. -/
theorem formula_restrict (p : Formula F Γ P) {j k : Jᵒᵖ} (f : j ⟶ k)
    (ρ : Env (M.fiber j) Γ) (h : (formula M hM p).obj j ρ) :
    (formula M hM p).obj k (M.restrict f ρ) := (formula M hM p).map f h

/-- Semantic inclusion is separate from source derivability. -/
def Valid (p q : Formula F Γ P) : Prop := formula M hM p ≤ formula M hM q

end SquareKit.Internal.SheafContexts
