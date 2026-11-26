import Dependent
import Mathlib.Logic.Equiv.Defs

/-!
# A local-universe construction for split Type families

Experimental semantic specialization for #292. A family stores a parameter
type, a family over it, and a name map from the context. Dependent sums and
products share an explicit input parameter type; their substitution laws are proved,
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
  Fiber : Parameters → Type u
  name : Γ → Parameters

/- Input classification is independent of constructing a sum or product. -/
namespace DependentInput

variable {P Q W V : Type u} (E : P → Type u)

abbrev Parameters := (a : P) × (E a → Q)

/-- A map into the parameter object retains both dependent names. -/
def representation : (W → Parameters (Q := Q) E) ≃
    ((a : W → P) × ((w : W) → E (a w) → Q)) where
  toFun n := ⟨fun w => (n w).1, fun w => (n w).2⟩
  invFun ab w := ⟨ab.1 w, ab.2 w⟩
  left_inv n := by
    funext w
    change (⟨(n w).1, (n w).2⟩ : Parameters E) = n w
    cases n w
    rfl
  right_inv ab := by cases ab; rfl

def name (a : W → P) (b : (w : W) → E (a w) → Q) :
    W → Parameters (Q := Q) E := (representation E).symm ⟨a, b⟩

@[simp] theorem representation_name (a : W → P) (b : (w : W) → E (a w) → Q) :
    representation E (name E a b) = ⟨a, b⟩ := (representation E).apply_symm_apply _

@[simp] theorem name_representation (n : W → Parameters (Q := Q) E) :
    name E (representation E n).1 (representation E n).2 = n :=
  (representation E).symm_apply_apply n

theorem representation_natural (n : W → Parameters (Q := Q) E) (σ : V → W) :
    representation E (n ∘ σ) =
      ⟨(representation E n).1 ∘ σ, fun v => (representation E n).2 (σ v)⟩ := rfl

theorem name_natural (a : W → P) (b : (w : W) → E (a w) → Q) (σ : V → W) :
    name E (a ∘ σ) (fun v => b (σ v)) = name E a b ∘ σ := rfl

/-- The two generic families have the same input context and different fibers. -/
def sigma (F : Q → Type u) : Family (Parameters (Q := Q) E) :=
  ⟨Parameters (Q := Q) E, fun v => (x : E v.1) × F (v.2 x), id⟩

def pi (F : Q → Type u) : Family (Parameters (Q := Q) E) :=
  ⟨Parameters (Q := Q) E, fun v => (x : E v.1) → F (v.2 x), id⟩

/-- Abstraction over any name, including the identity of the parameter context.
The body is supplied over its actual base, with no extension to other names. -/
def lam {F : Q → Type u} (n : W → Parameters (Q := Q) E)
    (b : (z : (w : W) × E (n w).1) → F ((n z.1).2 z.2)) :
    (w : W) → (x : E (n w).1) → F ((n w).2 x) :=
  DependentSquares.lam b

def app {F : Q → Type u} (n : W → Parameters (Q := Q) E)
    (f : (w : W) → (x : E (n w).1) → F ((n w).2 x))
    (a : (w : W) → E (n w).1) : (w : W) → F ((n w).2 (a w)) :=
  DependentSquares.app (A := fun w => E (n w).1)
    (B := fun z => F ((n z.1).2 z.2)) f a

end DependentInput

namespace Family

variable {Γ Δ Θ : Type u}

def decode (A : Family Γ) : Ty Γ := fun γ => A.Fiber (A.name γ)

def reindex (A : Family Γ) (σ : Sub Δ Γ) : Family Δ :=
  ⟨A.Parameters, A.Fiber, fun δ => A.name (σ δ)⟩

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

/-- The shared dependent naming map used by both constructors. -/
def dependentName (A : Family Γ) (B : Family A.Comprehension) :
    Γ → DependentInput.Parameters (Q := B.Parameters) A.Fiber :=
  DependentInput.name A.Fiber A.name (fun γ x => B.name ⟨γ, x⟩)

@[simp] theorem dependentName_fst (A : Family Γ) (B : Family A.Comprehension) (γ : Γ) :
    (dependentName A B γ).1 = A.name γ := rfl

@[simp] theorem dependentName_snd (A : Family Γ) (B : Family A.Comprehension)
    (γ : Γ) (x : A.decode γ) : (dependentName A B γ).2 x = B.name ⟨γ, x⟩ := rfl

theorem dependentName_reindex (A : Family Γ) (B : Family A.Comprehension)
    (σ : Sub Δ Γ) :
    dependentName (A.reindex σ) (B.reindex (lift (A := A.decode) σ)) =
      dependentName A B ∘ σ :=
  DependentInput.name_natural A.Fiber A.name (fun γ x => B.name ⟨γ, x⟩) σ

/-- Specialize the constructed generic sum along the shared name. -/
def sigma (A : Family Γ) (B : Family A.Comprehension) : Family Γ :=
  (DependentInput.sigma A.Fiber B.Fiber).reindex (dependentName A B)

/-- Specialize the constructed generic product along the same name. -/
def pi (A : Family Γ) (B : Family A.Comprehension) : Family Γ :=
  (DependentInput.pi A.Fiber B.Fiber).reindex (dependentName A B)

@[simp] theorem decode_pi (A : Family Γ) (B : Family A.Comprehension) :
    (A.pi B).decode = piTy A.decode B.decode := rfl

theorem pi_reindex (A : Family Γ) (B : Family A.Comprehension) (σ : Sub Δ Γ) :
    (A.pi B).reindex σ = (A.reindex σ).pi (B.reindex (lift (A := A.decode) σ)) := rfl

def lam {A : Family Γ} {B : Family A.Comprehension} (b : B.Term) :
    (A.pi B).Term := DependentInput.lam A.Fiber (dependentName A B) b

def app {A : Family Γ} {B : Family A.Comprehension} (f : (A.pi B).Term)
    (a : A.Term) : (B.reindex (extend idSub a)).Term :=
  DependentInput.app A.Fiber (dependentName A B) f a

theorem lam_native {A : Family Γ} {B : Family A.Comprehension} (b : B.Term) :
    lam b = DependentSquares.lam b := rfl

theorem app_native {A : Family Γ} {B : Family A.Comprehension}
    (f : (A.pi B).Term) (a : A.Term) : app f a = DependentSquares.app (B := B.decode) f a := rfl

theorem pi_beta {A : Family Γ} {B : Family A.Comprehension} (b : B.Term) (a : A.Term) :
    app (lam b) a = termReindex b (extend idSub a) := DependentSquares.pi_beta (B := B.decode) b a

/-- Selected Type eta retains weakening followed by application to the variable. -/
theorem pi_eta_cwf {A : Family Γ} {B : Family A.Comprehension} (f : (A.pi B).Term) :
    lam (A := A) (B := B) (etaBody (B := B.decode) f) = f :=
  DependentSquares.pi_eta_cwf (B := B.decode) f

theorem lam_reindex {A : Family Γ} {B : Family A.Comprehension} (b : B.Term)
    (σ : Sub Δ Γ) :
    termReindex (lam b) σ =
      lam (A := A.reindex σ) (B := B.reindex (lift (A := A.decode) σ)) (termReindex b (lift σ)) :=
  lam_subst b σ

theorem app_reindex {A : Family Γ} {B : Family A.Comprehension}
    (f : (A.pi B).Term) (a : A.Term) (σ : Sub Δ Γ) :
    termReindex (app f a) σ =
      app (B := B.reindex (lift (A := A.decode) σ)) (termReindex f σ) (termReindex a σ) :=
  app_subst (B := B.decode) f a σ

theorem lam_twice {A : Family Γ} {B : Family A.Comprehension} (b : B.Term)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    termReindex (termReindex (lam b) σ) τ =
      lam (A := A.reindex (compSub σ τ))
        (B := B.reindex (lift (A := A.decode) (compSub σ τ))) (termReindex b (lift (compSub σ τ))) := by
  rw [termReindex_comp]
  exact lam_reindex b (compSub σ τ)

theorem app_twice {A : Family Γ} {B : Family A.Comprehension}
    (f : (A.pi B).Term) (a : A.Term) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    termReindex (termReindex (app f a) σ) τ =
      app (B := B.reindex (lift (A := A.decode) (compSub σ τ)))
        (termReindex f (compSub σ τ)) (termReindex a (compSub σ τ)) := by
  rw [termReindex_comp]
  exact app_reindex f a (compSub σ τ)

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

namespace Family

variable {Γ Δ Θ : Type u}

/-- Product sections are represented by sections over the substituted display.
Both inverses come from the existing arbitrary-base `displayCurry`. -/
def piSections (A : Family Γ) (B : Family A.Comprehension) (σ : Sub Δ Γ) :
    (B.reindex (lift (A := A.decode) σ)).Term ≃ ((A.pi B).reindex σ).Term :=
  displayCurry A.decode B.decode σ

theorem piSections_apply (A : Family Γ) (B : Family A.Comprehension) (σ : Sub Δ Γ)
    (b : (B.reindex (lift (A := A.decode) σ)).Term) :
    piSections A B σ b =
      lam (A := A.reindex σ) (B := B.reindex (lift (A := A.decode) σ)) b := rfl

theorem piSections_symm_apply (A : Family Γ) (B : Family A.Comprehension)
    (σ : Sub Δ Γ) (b : (B.reindex (lift (A := A.decode) σ)).Term) :
    (piSections A B σ).symm (piSections A B σ b) = b :=
  (piSections A B σ).symm_apply_apply b

theorem piSections_apply_symm (A : Family Γ) (B : Family A.Comprehension)
    (σ : Sub Δ Γ) (f : ((A.pi B).reindex σ).Term) :
    piSections A B σ ((piSections A B σ).symm f) = f :=
  (piSections A B σ).apply_symm_apply f

theorem piSections_natural (A : Family Γ) (B : Family A.Comprehension)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) (b : (B.reindex (lift (A := A.decode) σ)).Term) :
    piSections A B (compSub σ τ) (termReindex b (lift τ)) =
      termReindex (piSections A B σ b) τ :=
  displayCurry_natural A.decode B.decode σ τ b

theorem piSections_symm_natural (A : Family Γ) (B : Family A.Comprehension)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) (f : ((A.pi B).reindex σ).Term) :
    (piSections A B (compSub σ τ)).symm (termReindex f τ) =
      termReindex ((piSections A B σ).symm f) (lift τ) := rfl

end Family

end SquareKit.LocalUniverses
