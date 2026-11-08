import Examples.InternalCertificateSolver
import SquareKit.AssemblyCountdownTransport

/-! Selection transport is inherited from local algebra squares and contextual uniqueness. -/
namespace InternalCertificateSolver
open Realizability Realizability.Assembly
open VaryingPartialCertificates AssemblyCertificateFamily

theorem solver_shift {Γ : Assembly} {n m : Nat} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n)
    (d : Nat) (hd : n+d ≤ m) :
    (solver n enabled seed hs).comp (boundedShift d hd) =
      solver m enabled (shiftSeed seed d)
        (fun γ => Nat.le_trans (Nat.add_le_add_right (hs γ) d) hd) :=
  boundedCountdown_selected_shift enabled seed hs d hd

theorem solver_substitution {Γ Δ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) (σ : Hom Δ Γ) :
    σ.comp (solver n enabled seed hs) =
      solver n (σ.comp enabled) (σ.comp seed) (fun δ => hs (σ.toFun δ)) := by
  exact cutSelected_substitution (boundedSequenceAlgebra n) (boundedSequences_complete n)
    (boundedCountdown n enabled seed hs) σ

theorem solver_substitution_comp {Γ Δ Θ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n)
    (σ : Hom Δ Γ) (τ : Hom Θ Δ) :
    τ.comp (σ.comp (solver n enabled seed hs)) =
      solver n ((τ.comp σ).comp enabled) ((τ.comp σ).comp seed)
        (fun θ => hs (σ.toFun (τ.toFun θ))) :=
  solver_substitution n enabled seed hs (τ.comp σ)

theorem solver_two_shifts {Γ : Assembly} {n m r : Nat} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n)
    (d e : Nat) (hd : n+d ≤ m) (he : m+e ≤ r) :
    ((solver n enabled seed hs).comp (boundedShift d hd)).comp (boundedShift e he) =
      solver r enabled (shiftSeed (shiftSeed seed d) e)
        (fun γ => Nat.le_trans (Nat.add_le_add_right
          (Nat.le_trans (Nat.add_le_add_right (hs γ) d) hd) e) he) := by
  have h₁ := congrArg (fun f => f.comp (boundedShift e he)) (solver_shift enabled seed hs d hd)
  exact h₁.trans (solver_shift enabled (shiftSeed seed d)
    (fun γ => Nat.le_trans (Nat.add_le_add_right (hs γ) d) hd) e he)

theorem solver_shift_full_records {Γ : Assembly} {n m : Nat} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n)
    (d : Nat) (hd : n+d ≤ m) (γ : Γ.Carrier) :
    transport d hd (forget n ((solver n enabled seed hs).toFun γ)) =
      forget m ((solver m enabled (shiftSeed seed d)
        (fun δ => Nat.le_trans (Nat.add_le_add_right (hs δ) d) hd)).toFun γ) :=
  (forget_shift d hd _).symm.trans
    (congrArg (fun f => forget m (f.toFun γ)) (solver_shift enabled seed hs d hd))

end InternalCertificateSolver
