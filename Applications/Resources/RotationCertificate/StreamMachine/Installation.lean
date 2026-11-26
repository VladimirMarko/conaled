import Applications.Resources.RotationCertificate.StreamMachine.CleanExecution

/-!
# StreamMachine: Installation
-/

set_option autoImplicit false
set_option warningAsError true

-- BEGIN INSTALLED SHARED PREFIX1
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

/-- An actual ambient prefix is the complete physical image of one and the
same source-prefix witness. Only owned-label agreement is required. -/
theorem installed_owned_prefix_frame
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∃ source, (next caller)^[n] (some start) = some source ∧
      reached = installedCfg names symbols registers labels source ∧
      remainingSteps source = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start source ∧
      (n < remainingSteps start ↔ InstalledOwned labels reached.l) ∧
      (n = 0 → reached = installedCfg names symbols registers labels start) ∧
      reached.var = registers (registersAt start n) ∧
      source.var.2.2 = start.var.2.2 ∧
      ∀ k, reached.stk (names (.inr k)) = (start.stk (.inr k)).map (symbols (.inr k)) := by
  obtain ⟨source, run, rank, path, live, zero, reset, callerRegister, frame⟩ :=
    owned_prefix_frame caller start n bound
  have mapped := installed_owned_prefix names symbols registers labels caller ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  have same : reached = installedCfg names symbols registers labels source := Option.some.inj mapped
  subst reached
  refine ⟨source, run, rfl, rank, path, ?_, ?_, ?_, callerRegister, ?_⟩
  · rwa [installedCfg_owned_iff]
  · intro empty
    rw [zero empty]
  · change registers source.var = registers (registersAt start n)
    rw [reset]
  · intro k
    rw [installedCfg_stack, frame k]

/-- The staged register value is transported at the actual supplied ambient
endpoint, including every dirty field before its own paid reset. -/
theorem installed_prefix_reset
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    reached.var = registers (registersAt start n) := by
  obtain ⟨_, _, _, _, _, _, _, reset, _, _⟩ :=
    installed_owned_prefix_frame names symbols registers labels caller ambient installed start n bound reached executed
  exact reset

/-- The complete physical allowance includes every transported local and
protected store; the endpoint is the same actual ambient iterate. -/
theorem installed_prefix_stackCells_le_dirty [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ allowance start := by
  apply installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    start n bound (allowance start) _ reached executed
  intro source run
  exact prefix_stackCells_le_dirty caller start n bound source run

end Resources.RotationCertificate.StreamMachine

-- END INSTALLED SHARED PREFIX1
