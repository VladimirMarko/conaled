import Examples.AssemblyCertificateTransport
import SquareKit.AssemblyCountdownFamily

/-! The internally selected solver agrees with the unchanged all-states certificate client. -/
namespace InternalCertificateSolver
open Realizability Realizability.Assembly
open VaryingPartialCertificates UniformCertificateStates AssemblyCertificateFamily

noncomputable def solver {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) :
    Hom Γ (boundedSequences n) :=
  cutSelected (boundedSequenceAlgebra n) (boundedSequences_complete n)
    (boundedCountdown n enabled seed hs)

theorem solver_coordinate {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) (γ : Γ.Carrier) (k : Nat) :
    ((solver n enabled seed hs).toFun γ).val.toFun k =
      countdownLimit (enabled.toFun γ) (seed.toFun γ) none k := by
  have he := congrArg (fun f : Hom Γ partialSequences => (f.toFun γ).toFun k)
    (boundedCountdown_selected_inclusion n enabled seed hs)
  exact he.trans (countdown_selected enabled seed γ k)

theorem coordinate_meaning (enabled : Bool) (n j : Nat) (hj : j ≤ n) (k : Nat) :
    coordinate (meaning enabled n j hj) k = countdownLimit enabled j none k := by
  cases enabled <;> simp [coordinate, meaning, countdownLimit, cutWaitValue, selected]

theorem solver_forget {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) (γ : Γ.Carrier) :
    forget n ((solver n enabled seed hs).toFun γ) =
      meaning (enabled.toFun γ) n (seed.toFun γ) (hs γ) := by
  apply coordinate_injective
  funext k
  exact (recover_coordinate _ k).trans
    ((solver_coordinate n enabled seed hs γ k).trans (coordinate_meaning _ _ _ _ k).symm)

/-- Equality is of whole partial certificate records, not merely their domains. -/
theorem solver_external_solution {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) (γ : Γ.Carrier) :
    forget n ((solver n enabled seed hs).toFun γ) =
      SelectedFixedPoint.solution (functional (enabled.toFun γ) n (seed.toFun γ) (hs γ)) :=
  (solver_forget n enabled seed hs γ).trans (solution_eq_meaning _ _ _ _).symm

theorem solver_uniform {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) (γ : Γ.Carrier) :
    UniformRealizable (meaning (enabled.toFun γ) n (seed.toFun γ) (hs γ)) := by
  have h := ((toStates n).toFun ((solver n enabled seed hs).toFun γ)).property
  exact (solver_forget n enabled seed hs γ) ▸ h

/-- Varying capacities use the same ambient selection, with uniformly tracked membership. -/
noncomputable def contextualSolver {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (enabled : Hom Γ (encoded Bool)) (seed : Hom Γ (encoded Nat))
    (hs : ∀ γ, Nat.le (seed.toFun γ) (capacity.toFun γ)) : Hom Γ (contextualStates capacity) :=
  (countdownSelectedFamily capacity enabled seed hs).comp (familyComparison capacity).hom

end InternalCertificateSolver
