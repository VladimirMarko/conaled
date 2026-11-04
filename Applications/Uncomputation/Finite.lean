import Applications.Uncomputation.Core
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic

/-! Finite basis permutations and their complex linear extension. Products of
basis labels represent tensor systems, not cartesian products of vector spaces.
The gates admit exactly permutations; the phase example extends this vocabulary.
-/
namespace Uncomputation

/-- Controlled XOR leaves its dependency intact. -/
def controlled {X : Type} (f : X → Bool) : (X × Bool) ≃ (X × Bool) where
  toFun p := (p.1, xor p.2 (f p.1))
  invFun p := (p.1, xor p.2 (f p.1))
  left_inv p := by rcases p with ⟨x, b⟩; change (x, xor (xor b (f x)) (f x)) = (x, b); cases b <;> cases f x <;> rfl
  right_inv p := by rcases p with ⟨x, b⟩; change (x, xor (xor b (f x)) (f x)) = (x, b); cases b <;> cases f x <;> rfl

abbrev cnot := controlled (fun b : Bool => b)
abbrev toffoli := controlled (fun p : Bool × Bool => p.1 && p.2)

/-- Distinct product factors enforce disjoint wires. No diagonal or discard. -/
inductive Circuit : Type → Type → Type 1 where
  | ident (A : Type) : Circuit A A
  | seq {A B D} : Circuit A B → Circuit B D → Circuit A D
  | tensor {A B D E} : Circuit A B → Circuit D E → Circuit (A × D) (B × E)
  | inverse {A B} : Circuit A B → Circuit B A
  | assoc (A B D : Type) : Circuit ((A × B) × D) (A × (B × D))
  | swap (A B : Type) : Circuit (A × B) (B × A)
  | cnot : Circuit (Bool × Bool) (Bool × Bool)
  | toffoli : Circuit ((Bool × Bool) × Bool) ((Bool × Bool) × Bool)

def Circuit.perm {A B} : Circuit A B → A ≃ B
  | .ident _ => Equiv.refl _
  | .seq f g => f.perm.trans g.perm
  | .tensor f g => Equiv.prodCongr f.perm g.perm
  | .inverse f => f.perm.symm
  | .assoc _ _ _ => Equiv.prodAssoc _ _ _
  | .swap _ _ => Equiv.prodComm _ _
  | .cnot => Uncomputation.cnot
  | .toffoli => Uncomputation.toffoli

/-- Amplitudes transform by inverse reindexing, hence linearly on all vectors. -/
def coherent {A B : Type} (e : A ≃ B) : (A → ℂ) →ₗ[ℂ] (B → ℂ) where
  toFun v b := v (e.symm b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coherent_apply {A B} (e : A ≃ B) (v : A → ℂ) (b : B) :
    coherent e v b = v (e.symm b) := rfl

@[simp] theorem coherent_ident (A : Type) : coherent (Equiv.refl A) = LinearMap.id := rfl

@[simp] theorem coherent_comp {A B D} (e : A ≃ B) (f : B ≃ D) :
    coherent (e.trans f) = (coherent f).comp (coherent e) := rfl

@[simp] theorem coherent_inverse {A B} (e : A ≃ B) :
    (coherent e.symm).comp (coherent e) = LinearMap.id := by ext v a; simp

/-- The canonical finite inner product, conjugate linear in the first slot. -/
def pairing {A : Type} [Fintype A] (v w : A → ℂ) : ℂ :=
  ∑ a, star (v a) * w a

theorem coherent_unitary {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (v w : A → ℂ) :
    pairing (coherent e v) (coherent e w) = pairing v w := by
  exact e.symm.sum_comp (fun a => star (v a) * w a)

theorem coherent_adjoint {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (v : A → ℂ) (w : B → ℂ) :
    pairing (coherent e v) w = pairing v (coherent e.symm w) := by
  simpa [pairing] using e.sum_comp (fun b => star (v (e.symm b)) * w b) |>.symm

/-- Pure tensors; arbitrary vectors on `A × B` also include entangled states. -/
def tensorState {A B : Type} (v : A → ℂ) (w : B → ℂ) : A × B → ℂ :=
  fun p => v p.1 * w p.2

theorem coherent_tensor {A B D E : Type} (e : A ≃ B) (f : D ≃ E)
    (v : A → ℂ) (w : D → ℂ) :
    coherent (Equiv.prodCongr e f) (tensorState v w) =
      tensorState (coherent e v) (coherent f w) := rfl

/-- Clean initialization is an embedding, not an endomorphism gate. -/
def initZero {A T : Type} [DecidableEq T] (zero : T) :
    (A → ℂ) →ₗ[ℂ] (A × T → ℂ) where
  toFun v p := if p.2 = zero then v p.1 else 0
  map_add' v w := by ext p; by_cases h : p.2 = zero <;> simp [h]
  map_smul' c v := by ext p; by_cases h : p.2 = zero <;> simp [h]

/-- Release is only licensed on this image. Evaluation outside it is not a
physical discard operation. -/
def IsClean {A T : Type} [DecidableEq T] (zero : T) (v : A × T → ℂ) : Prop :=
  ∃ w, v = initZero zero w

theorem initZero_isometry {A T : Type} [Fintype A] [Fintype T] [DecidableEq T]
    (zero : T) (v w : A → ℂ) :
    pairing (initZero zero v) (initZero zero w) = pairing v w := by
  simp [pairing, initZero, Fintype.sum_prod_type]

/-- A clean basis contract lifts to all amplitudes, including correlations with
an arbitrary untouched reference. No factorization of `v` is assumed. -/
theorem coherent_clean_reference {A T R : Type} [DecidableEq T]
    (zero : T) (c : (A × T) ≃ (A × T)) (out : A ≃ A)
    (h : ∀ a, c (a, zero) = (out a, zero)) (v : A × R → ℂ) :
    (fun p : (A × T) × R =>
      (if (c.symm p.1).2 = zero then v ((c.symm p.1).1, p.2) else 0)) =
    (fun p => if p.1.2 = zero then v (out.symm p.1.1, p.2) else 0) := by
  funext ⟨⟨a, t⟩, r⟩
  by_cases ht : t = zero
  · subst t
    have hi : c.symm (a, zero) = (out.symm a, zero) := by
      apply c.injective
      simpa using (h (out.symm a)).symm
    simp [hi]
  · have hi : (c.symm (a, t)).2 ≠ zero := by
      intro hz
      have hp : c.symm (a, t) = ((c.symm (a, t)).1, zero) := Prod.ext rfl hz
      have hc := congrArg c hp
      rw [c.apply_symm_apply, h] at hc
      exact ht (congrArg Prod.snd hc)
    simp [ht, hi]

/-- Delta-basis initialization along an explicitly supplied basis embedding. -/
noncomputable def embedState {A B : Type} [Fintype A] [DecidableEq B]
    (i : A → B) (v : A → ℂ) : B → ℂ := ∑ a, v a • Pi.single (i a) 1

theorem coherent_delta {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (a : A) : coherent e (Pi.single a 1) = Pi.single (e a) 1 := by
  ext b
  simp only [coherent_apply, Pi.single_apply]
  have h : e.symm b = a ↔ b = e a := by
    constructor <;> intro h
    · rw [← h]; simp
    · rw [h]; simp
  simp only [h]

/-- Lifts an independently proved basis contract through linearity. The embedding
may include zero scratch and a reference label. -/
theorem coherent_embed {A B : Type} [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : B ≃ B) (out : A ≃ A) (i : A → B)
    (h : ∀ a, e (i a) = i (out a)) (v : A → ℂ) :
    coherent e (embedState i v) = embedState i (coherent out v) := by
  simp only [embedState, map_sum, map_smul, coherent_delta, h]
  simpa using out.sum_comp (fun a => v (out.symm a) • Pi.single (i a) 1)

/-- Explicit preservation for every constructor in the Boolean fragment. -/
theorem Circuit.coherent_seq {A B D} (f : Circuit A B) (g : Circuit B D) :
    coherent (Circuit.seq f g).perm = (coherent g.perm).comp (coherent f.perm) := rfl

theorem Circuit.coherent_inverse {A B} (f : Circuit A B) :
    (coherent (Circuit.inverse f).perm).comp (coherent f.perm) = LinearMap.id :=
  Uncomputation.coherent_inverse f.perm

theorem Circuit.coherent_tensor {A B D E} (f : Circuit A B) (g : Circuit D E)
    (v : A → ℂ) (w : D → ℂ) :
    coherent (Circuit.tensor f g).perm (tensorState v w) =
      tensorState (coherent f.perm v) (coherent g.perm w) := rfl

/-- Linear-map interpretation, with operations and laws kept separate. -/
abbrev amplitudeOps : SquareKit.CategoryOps Type where
  Hom A B := (A → ℂ) →ₗ[ℂ] (B → ℂ)
  ident := LinearMap.id
  comp := LinearMap.comp

theorem amplitudeLaws : SquareKit.CategoryLaws amplitudeOps (SquareKit.equality amplitudeOps) where
  id_comp f := LinearMap.id_comp f
  comp_id f := LinearMap.comp_id f
  assoc h g f := LinearMap.comp_assoc f g h

end Uncomputation


