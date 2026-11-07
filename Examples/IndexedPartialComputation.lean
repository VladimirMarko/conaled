import SquareKit.SelectedFixedPoint
import Mathlib.Tactic

/-! An independently specified dependent countdown, with partial least-solution semantics. -/
noncomputable section
namespace IndexedPartialComputation
open OmegaCompletePartialOrder SelectedFixedPoint

/-- Successful countdown trace, including the zero step. -/
def trace : Nat → List Nat
  | 0 => [0]
  | k+1 => (k+1) :: trace k

/-- The selected result specification fixes both value and trace. -/
structure Cert (n k : Nat) where
  value : Fin (n+1)
  steps : List Nat
  value_eq : value.val = n
  steps_eq : steps = trace k

/-- The specified successful certificate. -/
def certificate (n k : Nat) : Cert n k := ⟨⟨n, by omega⟩, trace k, rfl, rfl⟩

/-- Prepend a successful step without changing the selected dependent value. -/
def step {n k : Nat} (c : Cert n k) : Cert n (k+1) :=
  ⟨c.value, (k+1)::c.steps, c.value_eq, by rw [c.steps_eq]; rfl⟩

@[simp] theorem step_certificate (n k : Nat) :
    step (certificate n k) = certificate n (k+1) := rfl

variable {Γ Δ Θ : Type*}
abbrev State (size : Γ → Nat) := (γ : Γ) → (k : Nat) → Part (Cert (size γ) k)

/-- Disabled coordinates recur without producing a value. Enabled coordinates count down. -/
def runStep (enabled : Γ → Bool) (size : Γ → Nat) (q : State size) : State size :=
  fun γ k => if enabled γ then
    match k with
    | 0 => Part.some (certificate (size γ) 0)
    | k+1 => Part.map step (q γ k)
  else q γ k

theorem runStep_continuous (enabled : Γ → Bool) (size : Γ → Nat) :
    ωScottContinuous (runStep enabled size) := by
  apply ωScottContinuous.of_apply₂
  intro γ
  apply ωScottContinuous.of_apply₂
  intro k
  cases h : enabled γ <;> simp only [runStep, h, Bool.false_eq_true, ↓reduceIte]
  · exact (ωScottContinuous.apply γ).apply₂ k
  · cases k with
    | zero => exact ωScottContinuous.const
    | succ k => exact ContinuousHom.ωScottContinuous.map ((ωScottContinuous.apply γ).apply₂ k)

/-- Continuous countdown functional. -/
def functional (enabled : Γ → Bool) (size : Γ → Nat) : State size →𝒄 State size :=
  ContinuousHom.ofFun _ (runStep_continuous enabled size)

/-- A finite observation. Exhaustion supplies no divergence evidence. -/
def bounded (enabled : Γ → Bool) (size : Γ → Nat) (fuel : Nat) : State size :=
  fun γ k => if enabled γ = true ∧ k < fuel then Part.some (certificate (size γ) k) else Part.none

theorem approximants_eq_bounded (enabled : Γ → Bool) (size : Γ → Nat) (fuel : Nat) :
    approximants (functional enabled size) fuel = bounded enabled size fuel := by
  induction fuel with
  | zero => funext γ k; simp [approximants, fixedPoints.iterateChain, bounded]; rfl
  | succ fuel ih =>
    change (functional enabled size)^[fuel+1] ⊥ = _
    rw [Function.iterate_succ_apply']
    change runStep enabled size (approximants (functional enabled size) fuel) = _
    rw [ih]
    funext γ k
    cases h : enabled γ <;> cases k <;>
      simp [runStep, bounded, h]
    split_ifs <;> simp_all

/-- Independent denotation: a selected certificate exactly on enabled inputs. -/
def meaning (enabled : Γ → Bool) (size : Γ → Nat) : State size :=
  fun γ k => if enabled γ then Part.some (certificate (size γ) k) else Part.none

theorem solution_eq_meaning (enabled : Γ → Bool) (size : Γ → Nat) :
    solution (functional enabled size) = meaning enabled size := by
  apply le_antisymm
  · apply solution_le
    intro γ k
    cases h : enabled γ <;> cases k <;> simp [functional, runStep, meaning, h]
  · intro γ k
    cases h : enabled γ
    · simp [meaning, h]; exact bot_le
    · have hl := le_ωSup (approximants (functional enabled size)) (k+1)
      change approximants (functional enabled size) (k+1) ≤ solution (functional enabled size) at hl
      rw [approximants_eq_bounded] at hl
      simpa [bounded, meaning, h] using hl γ k

/-- Reindexing retains the entire dependent certificate. -/
def reindex (size : Γ → Nat) (σ : Δ → Γ) : State size →𝒄 State (size ∘ σ) :=
  ContinuousHom.ofFun (fun q δ k => q (σ δ) k) (by
    apply ωScottContinuous.of_apply₂
    intro δ
    exact ωScottContinuous.apply (σ δ))

theorem reindex_solution (enabled : Γ → Bool) (size : Γ → Nat) (σ : Δ → Γ) :
    reindex size σ (solution (functional enabled size)) =
      solution (functional (enabled ∘ σ) (size ∘ σ)) := by
  apply map_solution
  · rfl
  · intro q; rfl

theorem reindex_comp (size : Γ → Nat) (σ : Δ → Γ) (τ : Θ → Δ) (q : State size) :
    reindex (size ∘ σ) τ (reindex size σ q) = reindex size (σ ∘ τ) q := rfl

/-- Partial result observation forgets the successful trace, retaining the value. -/
def observe (size : Γ → Nat) : State size →𝒄 ((γ : Γ) → Nat → Part (Fin (size γ+1))) :=
  ContinuousHom.ofFun (fun q γ k => Part.map Cert.value (q γ k)) (by
    apply ωScottContinuous.of_apply₂
    intro γ
    apply ωScottContinuous.of_apply₂
    intro k
    exact ContinuousHom.ωScottContinuous.map ((ωScottContinuous.apply γ).apply₂ k))

theorem observe_strict (size : Γ → Nat) : observe size ⊥ = ⊥ := by
  funext γ k
  exact Part.map_none _

/-- The trace-free functional still waits for the predecessor. -/
def valueStep (enabled : Γ → Bool) (size : Γ → Nat)
    (q : (γ : Γ) → Nat → Part (Fin (size γ+1))) :
    (γ : Γ) → Nat → Part (Fin (size γ+1)) :=
  fun γ k => if enabled γ then match k with
    | 0 => Part.some ⟨size γ, by omega⟩
    | k+1 => q γ k
  else q γ k

def valueFunctional (enabled : Γ → Bool) (size : Γ → Nat) :
    ((γ : Γ) → Nat → Part (Fin (size γ+1))) →𝒄
      ((γ : Γ) → Nat → Part (Fin (size γ+1))) :=
  ContinuousHom.ofFun (valueStep enabled size) (by
    apply ωScottContinuous.of_apply₂
    intro γ
    apply ωScottContinuous.of_apply₂
    intro k
    cases h : enabled γ <;> simp only [valueStep, h, Bool.false_eq_true, ↓reduceIte]
    · exact (ωScottContinuous.apply γ).apply₂ k
    · cases k with
      | zero => exact ωScottContinuous.const
      | succ k => exact (ωScottContinuous.apply γ).apply₂ k)

theorem observe_solution (enabled : Γ → Bool) (size : Γ → Nat) :
    observe size (solution (functional enabled size)) = solution (valueFunctional enabled size) := by
  apply map_solution _ _ _ (observe_strict size)
  intro q
  funext γ k
  cases h : enabled γ <;> cases k <;>
    simp [observe, functional, runStep, valueFunctional, valueStep, h, certificate,
      Part.map_map, Function.comp_def, step]

def σ : Bool × Nat → Bool × Nat := fun (b, m) => (b, 2*m)
def τ : Nat → Bool × Nat := fun t => (true, t+1)

/-- Two nonidentity reindexings preserve the specified 4 : Fin 5 and [2,1,0]. -/
theorem two_reindexings :
    reindex (Prod.snd ∘ σ) τ
      (reindex Prod.snd σ (solution (functional Prod.fst Prod.snd))) 1 2 =
      Part.some (certificate 4 2) := by
  rw [reindex_solution, reindex_solution, solution_eq_meaning]
  rfl

example : (certificate 4 2).value = (⟨4, by omega⟩ : Fin 5) := rfl
example : (certificate 4 2).steps = [2,1,0] := rfl

example : solution (functional Prod.fst Prod.snd) (false, 4) 2 = Part.none := by
  rw [solution_eq_meaning]; rfl

/-- A successful computation may not yet be visible at finite fuel. -/
example : bounded Prod.fst Prod.snd 2 (true, 4) 2 = Part.none ∧
    solution (functional Prod.fst Prod.snd) (true, 4) 2 = Part.some (certificate 4 2) := by
  constructor
  · simp [bounded]
  · rw [solution_eq_meaning]; rfl

/-- Continuity and intertwining alone do not preserve the chosen least solution. -/
def nonStrict : Part Bool →𝒄 Part Bool := ContinuousHom.ofFun (fun _ => Part.some true)

example (x : Part Bool) :
    nonStrict (ContinuousHom.id x) = ContinuousHom.id (nonStrict x) := rfl

example : nonStrict (solution (ContinuousHom.id : Part Bool →𝒄 Part Bool)) ≠
    solution (ContinuousHom.id : Part Bool →𝒄 Part Bool) := by
  have h : solution (ContinuousHom.id : Part Bool →𝒄 Part Bool) = ⊥ :=
    le_antisymm (solution_le _ (le_refl _)) bot_le
  rw [h]
  exact Part.some_ne_none _

/-- Arbitrary total endomaps do not necessarily have any fixed point. -/
example : ¬ ∃ b : Bool, (!b) = b := by decide

end IndexedPartialComputation
