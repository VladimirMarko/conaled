import SquareKit.Internal.Cubical.PartialDimension
import Mathlib.Data.Fintype.Pi

/-! The finite face lattice as upward-closed sets of partial assignments.
Substitution uses the three-valued evaluation of De Morgan expressions, not
Boolean evaluation of interval dimensions. -/
namespace SquareKit.Cubical
open CategoryTheory
namespace Face
abbrev Assignment (n : ℕ) := Fin n → PartialDimension.Carrier
abbrev Refines {n : ℕ} (a b : Assignment n) := ∀ i, PartialDimension.Refines (a i) (b i)

structure Carrier (n : ℕ) where
  holds : Assignment n → Bool
  stable : ∀ a b, Refines a b → holds a = true → holds b = true

@[ext] theorem Carrier.ext {n : ℕ} {a b : Carrier n} (h : ∀ ρ, a.holds ρ = b.holds ρ) : a = b := by
  cases a
  cases b
  simp_all only [mk.injEq]
  exact funext h

def top (n : ℕ) : Carrier n := ⟨fun _ => true, fun _ _ _ _ => rfl⟩
def bot (n : ℕ) : Carrier n := ⟨fun _ => false, fun _ _ _ h => h⟩

def atom {n : ℕ} (i : Fin n) (b : Bool) : Carrier n where
  holds ρ := decide (ρ i = some b)
  stable ρ τ h hp := by
    have he := of_decide_eq_true hp
    rcases h i with h | h
    · simp [he] at h
    · simpa only [decide_eq_true_eq] using h.symm.trans he

def meet {n : ℕ} (φ ψ : Carrier n) : Carrier n where
  holds ρ := φ.holds ρ && ψ.holds ρ
  stable ρ τ h hp := by
    simp only [Bool.and_eq_true] at hp ⊢
    exact ⟨φ.stable ρ τ h hp.1,ψ.stable ρ τ h hp.2⟩

def join {n : ℕ} (φ ψ : Carrier n) : Carrier n where
  holds ρ := φ.holds ρ || ψ.holds ρ
  stable ρ τ h hp := by
    simp only [Bool.or_eq_true] at hp ⊢
    exact hp.elim (fun p => Or.inl (φ.stable ρ τ h p)) (fun p => Or.inr (ψ.stable ρ τ h p))

theorem endpoint_disjoint {n : ℕ} (i : Fin n) : meet (atom i false) (atom i true) = bot n := by
  ext ρ
  simp only [meet,atom,bot]
  cases h : ρ i with
  | none => rfl
  | some b => cases b <;> rfl

/-- The interval boundary is not the full face. -/
theorem boundary_not_top : join (atom (0 : Fin 1) false) (atom 0 true) ≠ top 1 := by
  intro h
  have bad := congrArg (fun φ => φ.holds (fun _ => none)) h
  cases bad

/-- Every face is the finite union of its principal faces. -/
theorem disjunctive_normal_form {n : ℕ} (φ : Carrier n) (ρ : Assignment n) :
    φ.holds ρ = true ↔ ∃ τ : Assignment n, φ.holds τ = true ∧ Refines τ ρ := by
  constructor
  · intro h
    exact ⟨ρ,h,fun i => PartialDimension.refines_refl (ρ i)⟩
  · rintro ⟨τ,h,r⟩
    exact φ.stable τ ρ r h

/-- Evaluate a cube substitution at a partial assignment. -/
def assignmentMap {I J : Cube} (f : Cube.Hom I J) (ρ : Assignment I.dimension) : Assignment J.dimension :=
  Quotient.liftOn f (fun σ i => PartialDimension.eval ρ (σ i))
    (fun _σ _τ h => funext (fun i => PartialDimension.sound ρ (h i)))

theorem assignmentMap_refines {I J : Cube} (f : Cube.Hom I J)
    (ρ τ : Assignment I.dimension) (h : Refines ρ τ) : Refines (assignmentMap f ρ) (assignmentMap f τ) := by
  refine Quotient.inductionOn f ?_
  intro σ i
  exact PartialDimension.eval_refines ρ τ h (σ i)

@[simp] theorem assignmentMap_id (I : Cube) (ρ : Assignment I.dimension) :
    assignmentMap (Cube.identity I) ρ = ρ := rfl

@[simp] theorem assignmentMap_comp {I J K : Cube} (f : Cube.Hom I J) (g : Cube.Hom J K)
    (ρ : Assignment I.dimension) : assignmentMap (Cube.comp f g) ρ = assignmentMap g (assignmentMap f ρ) := by
  refine Quotient.inductionOn₂ f g ?_
  intro f g
  funext i
  exact PartialDimension.eval_subst ρ f (g i)

def substitute {I J : Cube} (f : Cube.Hom I J) (φ : Carrier J.dimension) : Carrier I.dimension where
  holds ρ := φ.holds (assignmentMap f ρ)
  stable ρ τ h := φ.stable _ _ (assignmentMap_refines f ρ τ h)

@[simp] theorem substitute_id (I : Cube) (φ : Carrier I.dimension) : substitute (Cube.identity I) φ = φ := rfl

@[simp] theorem substitute_comp {I J K : Cube} (f : Cube.Hom I J) (g : Cube.Hom J K)
    (φ : Carrier K.dimension) : substitute f (substitute g φ) = substitute (Cube.comp f g) φ := by
  ext ρ
  exact congrArg φ.holds (assignmentMap_comp f g ρ).symm

@[simp] theorem substitute_top {I J : Cube} (f : Cube.Hom I J) : substitute f (top J.dimension) = top I.dimension := rfl
@[simp] theorem substitute_bot {I J : Cube} (f : Cube.Hom I J) : substitute f (bot J.dimension) = bot I.dimension := rfl
@[simp] theorem substitute_meet {I J : Cube} (f : Cube.Hom I J) (φ ψ : Carrier J.dimension) :
    substitute f (meet φ ψ) = meet (substitute f φ) (substitute f ψ) := rfl
@[simp] theorem substitute_join {I J : Cube} (f : Cube.Hom I J) (φ ψ : Carrier J.dimension) :
    substitute f (join φ ψ) = join (substitute f φ) (substitute f ψ) := rfl

def Full {n : ℕ} (φ : Carrier n) : Prop := φ.holds (fun _ => none) = true

theorem full_iff_top {n : ℕ} (φ : Carrier n) : Full φ ↔ φ = top n := by
  constructor
  · intro h
    ext ρ
    exact φ.stable _ ρ (fun _ => Or.inl rfl) h
  · intro h
    rw [h]
    rfl

theorem full_meet {n : ℕ} (φ ψ : Carrier n) : Full (meet φ ψ) ↔ Full φ ∧ Full ψ := by simp [Full,meet]
theorem full_join {n : ℕ} (φ ψ : Carrier n) : Full (join φ ψ) ↔ Full φ ∨ Full ψ := by simp [Full,join]

theorem full_substitute {I J : Cube} (f : Cube.Hom I J) (φ : Carrier J.dimension)
    (h : Full φ) : Full (substitute f φ) := by
  rw [(full_iff_top φ).mp h,substitute_top]
  rfl

end Face
end SquareKit.Cubical
