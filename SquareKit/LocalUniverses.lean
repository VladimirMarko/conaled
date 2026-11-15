import Dependent
import Mathlib.Logic.Equiv.Defs

/-!
# A local-universe construction for split Type families

Experimental semantic specialization for #292. A family stores a parameter
type, a family over it, and a name map from the context. Dependent sums are
constructed over an explicit parameter type; their substitution law is proved,
not assumed in a model record. Decoding recovers `DependentSquares` operations.

This is not the general Lumsdaine–Warren theorem or a model of higher identity.
There is no translation from generated `PathTransport.Typed` judgments here.
-/

namespace SquareKit.LocalUniverses

open DependentSquares

universe u

/-- Delayed substitution into a chosen family. The parameter type need not
classify every family and is not an object-language universe. -/
structure Family (Γ : Type u) where
  Parameters : Type u
  fiber : Parameters → Type u
  name : Γ → Parameters

namespace Family

variable {Γ Δ Θ : Type u}

def decode (A : Family Γ) : Ty Γ := fun γ => A.fiber (A.name γ)

def reindex (A : Family Γ) (σ : Sub Δ Γ) : Family Δ :=
  ⟨A.Parameters, A.fiber, fun δ => A.name (σ δ)⟩

def present (A : Ty Γ) : Family Γ := ⟨Γ, A, id⟩

@[simp] theorem decode_present (A : Ty Γ) : (present A).decode = A := rfl

@[simp] theorem decode_reindex (A : Family Γ) (σ : Sub Δ Γ) :
    (A.reindex σ).decode = tySub A.decode σ := rfl

@[simp] theorem reindex_id (A : Family Γ) : A.reindex idSub = A := rfl

@[simp] theorem reindex_comp (A : Family Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    (A.reindex σ).reindex τ = A.reindex (compSub σ τ) := rfl

abbrev Term (A : Family Γ) := Tm A.decode
abbrev Comprehension (A : Family Γ) := Ext Γ A.decode

def termReindex {A : Family Γ} (t : A.Term) (σ : Sub Δ Γ) :
    (A.reindex σ).Term := tmSub t σ

theorem termReindex_comp {A : Family Γ} (t : A.Term)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    termReindex (termReindex t σ) τ = termReindex t (compSub σ τ) :=
  tmSub_comp t σ τ

/-- Comprehension has the existing split family's universal pairing property. -/
def comprehensionEquiv (A : Family Γ) :
    (Δ → A.Comprehension) ≃ (σ : Δ → Γ) × ((A.reindex σ).Term) where
  toFun f := ⟨fun δ => (f δ).1, fun δ => (f δ).2⟩
  invFun st := extend st.1 st.2
  left_inv f := extend_eta_sub f
  right_inv st := by cases st; rfl

/-- The parameter object for a dependent constructor. A name for the second
family must be supplied separately at every element of the first fiber. -/
def sigma (A : Family Γ) (B : Family A.Comprehension) : Family Γ where
  Parameters := (a : A.Parameters) × (A.fiber a → B.Parameters)
  fiber v := (a : A.fiber v.1) × B.fiber (v.2 a)
  name γ := ⟨A.name γ, fun a => B.name ⟨γ, a⟩⟩

@[simp] theorem decode_sigma (A : Family Γ) (B : Family A.Comprehension) :
    (A.sigma B).decode = sigmaTy A.decode B.decode := rfl

/-- Strict stability includes the dependent reindexing of the second family. -/
theorem sigma_reindex (A : Family Γ) (B : Family A.Comprehension) (σ : Sub Δ Γ) :
    (A.sigma B).reindex σ = (A.reindex σ).sigma (B.reindex (lift (A := A.decode) σ)) := rfl

def pair {A : Family Γ} {B : Family A.Comprehension}
    (a : A.Term) (b : (B.reindex (extend idSub a)).Term) : (A.sigma B).Term :=
  pairTerm (B := B.decode) a b

theorem pair_reindex {A : Family Γ} {B : Family A.Comprehension}
    (a : A.Term) (b : (B.reindex (extend idSub a)).Term) (σ : Sub Δ Γ) :
    termReindex (pair a b) σ =
      pair (B := B.reindex (lift (A := A.decode) σ)) (termReindex a σ) (termReindex b σ) :=
  pair_subst (B := B.decode) a b σ

/-- Evaluation into the existing split-family semantics preserves the whole
dependent pair through two substitutions. No equality of presentations is needed. -/
theorem pair_twice {A : Family Γ} {B : Family A.Comprehension}
    (a : A.Term) (b : (B.reindex (extend idSub a)).Term)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    termReindex (termReindex (pair a b) σ) τ =
      pairTerm (B := tySub B.decode (lift (compSub σ τ)))
        (tmSub a (compSub σ τ)) (tmSub b (compSub σ τ)) := by
  rw [termReindex_comp]
  exact pair_subst (B := B.decode) a b (compSub σ τ)

end Family

/-- The dependent currying bijection for a display map in Type, with an
arbitrary base map. This constructs the relevant section representation;
it does not assume a right adjoint as a record field. -/
def displayCurry {X W : Type u} (A : Ty X) (B : Ty (Ext X A)) (σ : W → X) :
    Tm (tySub B (lift σ)) ≃ Tm (tySub (piTy A B) σ) where
  toFun t w a := t ⟨w, a⟩
  invFun t wa := t wa.1 wa.2
  left_inv t := by funext wa; cases wa; rfl
  right_inv _ := rfl

theorem displayCurry_natural {X W V : Type u} (A : Ty X) (B : Ty (Ext X A))
    (σ : W → X) (τ : V → W) (t : Tm (tySub B (lift σ))) :
    displayCurry A B (compSub σ τ) (tmSub t (lift τ)) =
      tmSub (displayCurry A B σ t) τ := rfl

end SquareKit.LocalUniverses
