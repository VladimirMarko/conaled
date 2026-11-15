import Applications.Uncomputation.Failures
import Applications.Uncomputation.Schedules

/-! Author-facing specializations: a dependency oracle, its matrix coordinates,
and coherent scheduled computation with an arbitrary untouched reference. -/
namespace Uncomputation.Examples

example (a b y : Bool) :
    oracle (fun p : Bool × Bool => p.1 && p.2) (((a,b),y),false) =
      (((a,b),xor y (a && b)),false) := and_oracle a b y

example : coordinates cnot (true,true) (true,false) = 1 := by
  simp [coordinates_entry, cnot, controlled]

example (v : Bool → ℂ) :
    coherent cnot.symm (scratchZ (coherent cnot (initZero false v))) =
      initZero false (phaseZ v) := phase_cleanup v

example {R : Type} (ρ : (((Bool × Bool) × Bool) × R) →
    (((Bool × Bool) × Bool) × R) → ℂ) :
    (fun p q : ((((Bool × Bool) × Bool) × Bool) × R) =>
      if ((oracle (fun p : Bool × Bool => p.1 && p.2)).symm p.1).2 = false ∧
         ((oracle (fun p : Bool × Bool => p.1 && p.2)).symm q.1).2 = false then
        ρ (((oracle (fun p : Bool × Bool => p.1 && p.2)).symm p.1).1,p.2)
          (((oracle (fun p : Bool × Bool => p.1 && p.2)).symm q.1).1,q.2) else 0) =
    (fun p q => if p.1.2 = false ∧ q.1.2 = false then
      ρ (toffoli.symm p.1.1,p.2) (toffoli.symm q.1.1,q.2) else 0) :=
  clean_density_reference false _ toffoli (oracle_clean _) ρ

open Schedule

def pairOracle : (Fin 6 → Bool) ≃ (Fin 6 → Bool) where
  toFun := pairOutput
  invFun := pairOutput
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repeatedOracle : (Fin 4 → Bool) ≃ (Fin 4 → Bool) where
  toFun := repeatedOutput
  invFun := repeatedOutput
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- This theorem admits entangled amplitudes: `v` need not be a pure tensor. -/
theorem scheduled_reference {A B R : Type} [Fintype A] [DecidableEq A]
    [Fintype R] [DecidableEq R] [DecidableEq B]
    (e : B ≃ B) (out : A ≃ A) (i : A → B)
    (h : ∀ a, e (i a) = i (out a)) (v : A × R → ℂ) :
    coherent (Equiv.prodCongr e (Equiv.refl R))
      (embedState (fun p : A × R => (i p.1,p.2)) v) =
    embedState (fun p : A × R => (i p.1,p.2))
      (coherent (Equiv.prodCongr out (Equiv.refl R)) v) :=
  coherent_embed (Equiv.prodCongr e (Equiv.refl R))
    (Equiv.prodCongr out (Equiv.refl R)) (fun p => (i p.1,p.2))
    (fun p => Prod.ext (h p.1) rfl) v

theorem parallel_coherent {R : Type} [Fintype R] [DecidableEq R]
    (v : (Fin 6 → Bool) × R → ℂ) :
    coherent (Equiv.prodCongr parallelPerm (Equiv.refl R))
      (embedState (fun p => (pairInput p.1,p.2)) v) =
    embedState (fun p => (pairInput p.1,p.2))
      (coherent (Equiv.prodCongr pairOracle (Equiv.refl R)) v) := by
  apply scheduled_reference
  intro a
  simpa [parallelPerm, gatesPerm_apply, run, pairOracle] using parallel_correct a

theorem serial_coherent {R : Type} [Fintype R] [DecidableEq R]
    (v : (Fin 6 → Bool) × R → ℂ) :
    coherent (Equiv.prodCongr serialPerm (Equiv.refl R))
      (embedState (fun p => (pairInputSerial p.1,p.2)) v) =
    embedState (fun p => (pairInputSerial p.1,p.2))
      (coherent (Equiv.prodCongr pairOracle (Equiv.refl R)) v) := by
  apply scheduled_reference
  intro a
  simpa [serialPerm, gatesPerm_apply, run, pairOracle] using serial_correct a

theorem retain_coherent {R : Type} [Fintype R] [DecidableEq R]
    (v : (Fin 4 → Bool) × R → ℂ) :
    coherent (Equiv.prodCongr retainPerm (Equiv.refl R))
      (embedState (fun p => (repeatedInput p.1,p.2)) v) =
    embedState (fun p => (repeatedInput p.1,p.2))
      (coherent (Equiv.prodCongr repeatedOracle (Equiv.refl R)) v) := by
  apply scheduled_reference
  intro a
  simpa [retainPerm, gatesPerm_apply, run, repeatedOracle] using retain_correct a

theorem recompute_coherent {R : Type} [Fintype R] [DecidableEq R]
    (v : (Fin 4 → Bool) × R → ℂ) :
    coherent (Equiv.prodCongr recomputePerm (Equiv.refl R))
      (embedState (fun p => (repeatedInput p.1,p.2)) v) =
    embedState (fun p => (repeatedInput p.1,p.2))
      (coherent (Equiv.prodCongr repeatedOracle (Equiv.refl R)) v) := by
  apply scheduled_reference
  intro a
  simpa [recomputePerm, gatesPerm_apply, run, repeatedOracle] using recompute_correct a

end Uncomputation.Examples
