import Examples.InternalUniqueCertificate
import Examples.InternalCertificateStep
import Examples.InternalCountdown
import Examples.InternalIteration

/-! Full selected records, two proper changes, arbitrary cut labels and honest unknowns. -/
namespace InternalCertificateControls
open Realizability Realizability.Assembly
open VaryingPartialCertificates AssemblyCertificateFamily InternalCertificateSolver
open Encodable Denumerable
open Nat.Partrec (Code)

private def enabled : Hom (encoded Nat) (encoded Bool) :=
  ofComputable (fun _ : Nat => true) (Computable.const true)
private def disabled : Hom (encoded Nat) (encoded Bool) :=
  ofComputable (fun _ : Nat => false) (Computable.const false)
private def seed (j : Nat) : Hom (encoded Nat) (encoded Nat) := natConstant _ j

private theorem seed_bound (j n : Nat) (h : j ≤ n) : ∀ γ, Nat.le ((seed j).toFun γ) n :=
  fun _ => h

example : forget 1 ((solver 1 enabled (seed 0) (seed_bound 0 1 (by decide))).toFun (17 : Nat)) 2 =
    Part.some (⟨⟨2, by decide⟩,[2,1,0],rfl⟩ : Cert 1 2) :=
  congrFun (solver_forget 1 enabled (seed 0) (seed_bound 0 1 (by decide)) (17 : Nat)) 2

example : forget 1 ((solver 1 enabled (seed 1) (seed_bound 1 1 (by decide))).toFun (17 : Nat)) 2 =
    Part.some (⟨⟨3, by decide⟩,[2,1,0],rfl⟩ : Cert 1 2) :=
  congrFun (solver_forget 1 enabled (seed 1) (seed_bound 1 1 (by decide)) (17 : Nat)) 2

example : forget 1 ((solver 1 disabled (seed 0) (seed_bound 0 1 (by decide))).toFun (17 : Nat)) =
    fun _ => Part.none := solver_forget _ _ _ _ _

/-- This proof uses the two local algebra transport theorems before observing the answer. -/
example : forget 4
    ((boundedShift 1 (show 2+1 ≤ 4 by omega)).toFun
      ((boundedShift 0 (show 1+0 ≤ 2 by omega)).toFun
        ((solver 1 enabled (seed 0) (seed_bound 0 1 (by decide))).toFun (17 : Nat)))) 2 =
      Part.some (⟨⟨3, by decide⟩,[2,1,0],rfl⟩ : Cert 4 2) := by
  have ht := solver_two_shifts enabled (seed 0) (seed_bound 0 1 (by decide)) 0 1
    (show 1+0 ≤ 2 by omega) (show 2+1 ≤ 4 by omega)
  have he := congrArg (fun f : Hom (encoded Nat) (boundedSequences 4) => forget 4 (f.toFun (17 : Nat)) 2) ht
  apply he.trans
  exact congrFun (solver_forget 4 enabled (shiftSeed (shiftSeed (seed 0) 0) 1) _ (17 : Nat)) 2

example : ¬ Function.Surjective (boundedShift 0 (show 1+0 ≤ 2 by omega)).toFun :=
  boundedShift_first_proper 1
example : ¬ Function.Surjective (boundedShift 1 (show 2+1 ≤ 4 by omega)).toFun :=
  boundedShift_second_proper 1

/-- Returned cut labels do not affect the successful coordinate or its value. -/
example : finalCuts.realizes (encode (Code.comp (Code.const 99) (cutCode 3))) ⟨some 3⟩ :=
  InternalIteration.alternative_cut_labels
example : cutWait.toFun (⟨some 3⟩,(2 : Nat)) = some (2 : Nat) := rfl

/-- Exhaustion is compatible with a later defined selected result. -/
example :
    ((strictIteration sequenceAlgebra (countdown enabled (seed 0))).toFun ((17 : Nat),⟨2⟩)).toFun (2 : Nat) = none ∧
    ((cutSelected sequenceAlgebra partialSequences_complete (countdown enabled (seed 0))).toFun (17 : Nat)).toFun
      (2 : Nat) = some (2 : Nat) :=
  ⟨countdown_iteration _ _ _ _ _,countdown_selected _ _ _ _⟩

example : observeUnique
    (forget 1 ((solver 1 enabled (seed 0) (seed_bound 0 1 (by decide))).toFun (17 : Nat))) 2 =
      Part.some (IndexedPartialComputation.certificate 1 2) := by
  have h := congrFun (congrFun (solver_unique 1 enabled (seed 0) (seed_bound 0 1 (by decide))) (17 : Nat)) 2
  exact h.trans (congrFun (congrFun
    (IndexedPartialComputation.solution_eq_meaning enabled.toFun (fun _ => 1)) (17 : Nat)) 2)

example :
    (forget 1 ((solver 1 enabled (seed 0) (seed_bound 0 1 (by decide))).toFun (17 : Nat)) 2).Dom ↔
    (forget 1 ((solver 1 enabled (seed 1) (seed_bound 1 1 (by decide))).toFun (17 : Nat)) 2).Dom := by
  have h₀ := congrFun (solver_external_solution 1 enabled (seed 0) (seed_bound 0 1 (by decide)) (17 : Nat)) 2
  have h₁ := congrFun (solver_external_solution 1 enabled (seed 1) (seed_bound 1 1 (by decide)) (17 : Nat)) 2
  exact (Iff.of_eq (congrArg Part.Dom h₀)).trans
    ((same_domain true 1 0 1 (by decide) (by decide) 2).trans (Iff.of_eq (congrArg Part.Dom h₁)).symm)

example :
    forget 1 ((solver 1 enabled (seed 0) (seed_bound 0 1 (by decide))).toFun (17 : Nat)) 2 ≠
    forget 1 ((solver 1 enabled (seed 1) (seed_bound 1 1 (by decide))).toFun (17 : Nat)) 2 := by
  intro h
  have h₀ := congrFun (solver_external_solution 1 enabled (seed 0) (seed_bound 0 1 (by decide)) (17 : Nat)) 2
  have h₁ := congrFun (solver_external_solution 1 enabled (seed 1) (seed_bound 1 1 (by decide)) (17 : Nat)) 2
  exact different_selection (h₀.symm.trans (h.trans h₁))

end InternalCertificateControls
