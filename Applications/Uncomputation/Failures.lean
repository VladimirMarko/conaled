import Applications.Uncomputation.Oracle

/-! Minimal density semantics for discriminating observations. Outer products
and partial trace suffice here; no general channel compiler is claimed. -/
noncomputable section
namespace Uncomputation

/-- Z is an additional phase gate, outside Boolean permutations. -/
def phaseZ : (Bool → ℂ) →ₗ[ℂ] (Bool → ℂ) where
  toFun v b := if b then -v b else v b
  map_add' _ _ := by ext b; cases b <;> simp [add_comm]
  map_smul' _ _ := by ext b; cases b <;> simp

def scratchZ : (Bool × Bool → ℂ) →ₗ[ℂ] (Bool × Bool → ℂ) where
  toFun v p := if p.2 then -v p else v p
  map_add' _ _ := by ext ⟨a,b⟩; cases b <;> simp [add_comm]
  map_smul' _ _ := by ext ⟨a,b⟩; cases b <;> simp

theorem phaseZ_unitary (v w : Bool → ℂ) :
    pairing (phaseZ v) (phaseZ w) = pairing v w := by
  simp [pairing, phaseZ]

/-- Phase kickback retains the specified Z effect while returning zero scratch. -/
theorem phase_cleanup (v : Bool → ℂ) :
    coherent cnot.symm (scratchZ (coherent cnot (initZero false v))) =
      initZero false (phaseZ v) := by
  have h := cleanup_correct amplitudeOps amplitudeLaws
    (coherent cnot) scratchZ (coherent cnot.symm) (initZero false) phaseZ
    (by ext v p; simp [LinearMap.comp_apply])
    (by
      ext v ⟨a,t⟩
      cases a <;> cases t <;>
        simp [coherent, cnot, controlled, scratchZ, initZero, phaseZ])
  exact LinearMap.congr_fun h v

/-- An invertible linear scaling need not preserve the inner product. -/
theorem scaling_not_unitary :
    pairing (fun _ : Unit => (2 : ℂ)) (fun _ : Unit => (2 : ℂ)) ≠
      pairing (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℂ)) := by
  norm_num [pairing]

def density {A : Type} (v : A → ℂ) : A → A → ℂ :=
  fun a b => v a * star (v b)

def traceScratch {A T : Type} [Fintype T] (ρ : (A × T) → (A × T) → ℂ) : A → A → ℂ :=
  fun a b => ∑ t, ρ (a,t) (b,t)

/-- Clean factorization preserves every density entry after release. -/
theorem trace_clean {A T : Type} [Fintype T] [DecidableEq T]
    (zero : T) (v : A → ℂ) :
    traceScratch (density (initZero zero v)) = density v := by
  ext a b
  simp [traceScratch, density, initZero]

/-- An unnormalized Bell vector makes the off-diagonal loss exact with integer
coefficients. Rescaling either vector scales every density entry equally. -/
def bell : Bool × Bool → ℂ := fun p => if p.1 = p.2 then 1 else 0

def plus : Bool → ℂ := fun _ => 1

theorem cnot_entangles : coherent cnot (initZero false plus) = bell := by
  ext ⟨a,t⟩; cases a <;> cases t <;> rfl

theorem trace_loses_coherence :
    traceScratch (density bell) false true = 0 ∧ density plus false true = 1 := by
  norm_num [traceScratch, density, bell, plus, Fintype.sum_bool]

theorem same_basis_observations (a : Bool) :
    traceScratch (density bell) a a = density plus a a := by
  cases a <;> norm_num [traceScratch, density, bell, plus, Fintype.sum_bool]

/-- Ignoring a computational-basis measurement removes off-diagonal scratch
blocks. Tracing it out has exactly the same retained marginal. -/
def measureScratch {A T : Type} [DecidableEq T]
    (ρ : (A × T) → (A × T) → ℂ) : (A × T) → (A × T) → ℂ :=
  fun p q => if p.2 = q.2 then ρ p q else 0

theorem ignored_measurement {A T : Type} [Fintype T] [DecidableEq T]
    (ρ : (A × T) → (A × T) → ℂ) :
    traceScratch (measureScratch ρ) = traceScratch ρ := by
  funext a b
  simp only [traceScratch, measureScratch, ite_true]

/-- Normalized Bell density and the product of its mixed marginals differ. -/
def bellDensity : (Bool × Bool) → (Bool × Bool) → ℂ :=
  fun p q => density bell p q / 2

def mixed : Bool → Bool → ℂ := fun a b => if a = b then 1 / 2 else 0

theorem bell_marginal : traceScratch bellDensity = mixed := by
  ext a b; cases a <;> cases b <;>
    norm_num [traceScratch, bellDensity, density, bell, mixed, Fintype.sum_bool]

theorem mixed_marginal_not_independent :
    bellDensity (false,false) (true,true) ≠ mixed false true * mixed false true := by
  norm_num [bellDensity, density, bell, mixed]

/-- Extension of an arbitrary operator by a clean scratch density. Positivity
and trace one may be imposed by callers; equality holds without those premises. -/
def initDensity {A T : Type} [DecidableEq T] (zero : T) (ρ : A → A → ℂ) :
    (A × T) → (A × T) → ℂ :=
  fun p q => if p.2 = zero ∧ q.2 = zero then ρ p.1 q.1 else 0

/-- Unitary conjugation for a basis permutation, including off-diagonal entries. -/
def evolve {A B : Type} (e : A ≃ B) (ρ : A → A → ℂ) : B → B → ℂ :=
  fun p q => ρ (e.symm p) (e.symm q)

theorem clean_inverse {A T : Type} (zero : T) (c : (A × T) ≃ (A × T))
    (out : A ≃ A) (h : ∀ a, c (a, zero) = (out a, zero)) (a : A) :
    c.symm (a, zero) = (out.symm a, zero) := by
  apply c.injective
  simpa using (h (out.symm a)).symm

theorem clean_inverse_iff {A T : Type} (zero : T) (c : (A × T) ≃ (A × T))
    (out : A ≃ A) (h : ∀ a, c (a, zero) = (out a, zero)) (p : A × T) :
    (c.symm p).2 = zero ↔ p.2 = zero := by
  constructor
  · intro hz
    have hp : c.symm p = ((c.symm p).1, zero) := Prod.ext rfl hz
    have hc := congrArg c hp
    rw [c.apply_symm_apply, h] at hc
    exact congrArg Prod.snd hc
  · intro hz
    rcases p with ⟨a,t⟩; dsimp at hz; subst t
    rw [clean_inverse zero c out h]

/-- Full operator equality with a reference, not merely equality of probabilities
or a product-input theorem. State order is (retained, scratch), reference. -/
theorem clean_density_reference {A T R : Type} [DecidableEq T]
    (zero : T) (c : (A × T) ≃ (A × T)) (out : A ≃ A)
    (h : ∀ a, c (a,zero) = (out a,zero)) (ρ : (A × R) → (A × R) → ℂ) :
    (fun p q : (A × T) × R =>
      if (c.symm p.1).2 = zero ∧ (c.symm q.1).2 = zero then
        ρ ((c.symm p.1).1,p.2) ((c.symm q.1).1,q.2) else 0) =
    (fun p q => if p.1.2 = zero ∧ q.1.2 = zero then
      ρ (out.symm p.1.1,p.2) (out.symm q.1.1,q.2) else 0) := by
  funext ⟨⟨a,t⟩,r⟩ ⟨⟨b,u⟩,s⟩
  simp only [clean_inverse_iff zero c out h]
  by_cases ht : t = zero <;> by_cases hu : u = zero
  · subst t; subst u; simp [clean_inverse zero c out h]
  all_goals simp [ht, hu]

theorem phaseZ_not_permutation : ¬ ∃ e : Bool ≃ Bool, phaseZ = coherent e := by
  rintro ⟨e, h⟩
  have he := congrArg (fun f : (Bool → ℂ) →ₗ[ℂ] (Bool → ℂ) => f plus true) h
  norm_num [phaseZ, coherent, plus] at he

theorem cnot_does_not_clone : coherent cnot (initZero false plus) ≠ tensorState plus plus := by
  intro h
  have he := congrFun h (false,true)
  norm_num [coherent, cnot, controlled, initZero, tensorState, plus] at he

end Uncomputation
