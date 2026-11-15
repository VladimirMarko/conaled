import SquareKit.Internal.Cubical.Judgments.PathsTheory
import SquareKit.Internal.Cubical.RestrictedTransport

/-! Selected filling providers and faces are separate source values. Partial
sections use ordinary terms in their restricted contexts. The provider law
predicate remains a typing guard. -/
namespace SquareKit.Cubical.Source.Value
open Presheaf
universe u

noncomputable def fillingAt (Γ : Context.{u}) (A : Family Γ) : Value.{u} → Option (Filling A) := by
  classical
  exact fun v => match v with
    | .filling Δ B F =>
      if h : Δ = Γ then
        let p : (B : Family Γ) × Filling B := h ▸ ⟨B,F⟩
        if k : p.1 = A then some (k ▸ p.2) else none
      else none
    | _ => none

noncomputable def cofibrationAt (Γ : Context.{u}) : Value.{u} → Option (Cofibration Γ) := by
  classical
  exact fun v => match v with
    | .cofibration Δ φ => if h : Δ = Γ then some (h ▸ φ) else none
    | _ => none

noncomputable def fillingIn (Γ : Context.{u}) : Value.{u} → Option ((A : Family Γ) × Filling A) := by
  classical
  exact fun v => match v with
    | .filling Δ A F => if h : Δ = Γ then some (h ▸ ⟨A,F⟩) else none
    | _ => none

@[simp] theorem fillingIn_filling (Γ : Context.{u}) (A : Family Γ) (F : Filling A) :
    fillingIn Γ (.filling Γ A F) = some ⟨A,F⟩ := by simp [fillingIn]

@[simp] theorem fillingAt_filling (Γ : Context.{u}) (A : Family Γ) (F : Filling A) :
    fillingAt Γ A (.filling Γ A F) = some F := by simp [fillingAt]

@[simp] theorem cofibrationAt_cofibration (Γ : Context.{u}) (φ : Cofibration Γ) :
    cofibrationAt Γ (.cofibration Γ φ) = some φ := by simp [cofibrationAt]


end SquareKit.Cubical.Source.Value
