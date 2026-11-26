import Applications.Resources.RotationCertificate.StreamMachine.FrontEnd

/-!
# StreamMachine: Package
-/

set_option autoImplicit false
set_option warningAsError true


-- BEGIN FINITE PACKAGE BASE PASSED2
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Actual finite package and certificate-only initialization

The designated output index is the existing fuel store. These carrier and
initializer equations make no output-word or halting claim.
-/

def initialRegisters (initial : R) : Registers R :=
  (none, ((none, (none, none)), initial))

@[simp] theorem resetAll_initialRegisters (initial : R) :
    resetAll (initialRegisters initial) = initialRegisters initial := rfl

section StreamFinitePackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- The actual program and caller state are fixed before the certificate input.
The fuel word is designated k₁ without any Boolean output emission. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .certificate
  k₁ := .inl .fuel
  Γ := Alphabet Γ
  Λ := Label Λ
  main := phaseLabel inspectPhase
  σ := Registers R
  initialState := initialRegisters initial
  Γk₀Fin := alphabetFintype (.inl .certificate)
  m := program caller

@[instance_reducible]
def machineAlphabetFintype (initial : R) (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := alphabetFintype k

theorem machine_input_index (initial : R) :
    (machine caller initial).k₀ = Sum.inl LocalStack.certificate := rfl

theorem machine_output_index (initial : R) :
    (machine caller initial).k₁ = Sum.inl LocalStack.fuel := rfl

theorem machine_input_alphabet (initial : R) :
    (machine caller initial).Γ (machine caller initial).k₀ = Tag := rfl

theorem machine_output_alphabet (initial : R) :
    (machine caller initial).Γ (machine caller initial).k₁ = Bool := rfl

theorem machine_card_stackId (initial : R) :
    @Fintype.card (machine caller initial).K (machine caller initial).kFin =
      9 + Fintype.card K := card_stackId

theorem machine_card_label (initial : R) :
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin =
      41 + Fintype.card Λ := card_label

theorem machine_card_registers (initial : R) :
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin =
      306 * Fintype.card R := card_registers

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

/-- Only the certificate is initialized with the supplied word. Every other
physical word, including the designated fuel/output word, is initially empty. -/
theorem initList_eq (initial : R) (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel inspectPhase)) (initialRegisters initial) { certificate := raw }
        (fun _ => []) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

theorem initList_certificate (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (.inl .certificate) = raw := by
  rw [initList_eq]
  rfl

theorem initList_output_empty (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (machine caller initial).k₁ = [] := by
  rw [initList_eq]
  rfl

theorem initList_source_empty (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (.inl .source) = [] := by
  rw [initList_eq]
  rfl

theorem initList_target_empty (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (.inl .target) = [] := by
  rw [initList_eq]
  rfl

theorem initList_context_empty (initial : R) (raw : Word) (k : K) :
    (Turing.initList (machine caller initial) raw).stk (.inr k) = [] := by
  rw [initList_eq]
  rfl

end StreamFinitePackage

end Resources.RotationCertificate.StreamMachine

-- END FINITE PACKAGE BASE PASSED2

-- BEGIN INSTALLATION BASE PASSED2
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type}

section FurtherInstallation

variable {K' Λ' R' : Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, Alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

def installedCfg (c : Cfg Γ Λ R) : Turing.TM2.Cfg Γ' Λ' R' :=
  FrontEndMachine.Transport.cfg names symbols registers labels c

theorem installedCfg_injective :
    Function.Injective (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.cfg_injective names symbols registers labels labels.injective

/-- The inverse recovers the entire dependent stack family and every caller
register/label component, including live halt-labelled configurations. -/
def installedCfgEquiv : Cfg Γ Λ R ≃ Turing.TM2.Cfg Γ' Λ' R' where
  toFun := installedCfg names symbols registers labels
  invFun c :=
    { l := c.l.map labels.symm
      var := registers.symm c.var
      stk := (FrontEndMachine.Transport.stackEquiv names symbols).symm c.stk }
  left_inv c := by
    rcases c with ⟨label, regs, data⟩
    cases label <;> simp [installedCfg, FrontEndMachine.Transport.cfg]
  right_inv c := by
    rcases c with ⟨label, regs, data⟩
    cases label <;> simp [installedCfg, FrontEndMachine.Transport.cfg]

@[simp] theorem installedCfgEquiv_apply (c : Cfg Γ Λ R) :
    installedCfgEquiv names symbols registers labels c =
      installedCfg names symbols registers labels c := rfl

theorem installedCfg_label (c : Cfg Γ Λ R) :
    (installedCfg names symbols registers labels c).l = c.l.map labels := rfl

theorem installedCfg_registers (c : Cfg Γ Λ R) :
    (installedCfg names symbols registers labels c).var = registers c.var := rfl

theorem installedCfg_stack (c : Cfg Γ Λ R) (k : StackId K) :
    (installedCfg names symbols registers labels c).stk (names k) =
      (c.stk k).map (symbols k) :=
  FrontEndMachine.Transport.stackEquiv_apply names symbols c.stk k

theorem installedCfg_registers_readback (c : Cfg Γ Λ R) :
    registers.symm (installedCfg names symbols registers labels c).var = c.var :=
  registers.symm_apply_apply c.var

theorem installedCfg_stack_readback (c : Cfg Γ Λ R) (k : StackId K) :
    ((installedCfg names symbols registers labels c).stk (names k)).map
      (symbols k).symm = c.stk k := by
  rw [installedCfg_stack]
  simp

theorem installed_stack_cells [Fintype K] [Fintype K'] (c : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels c).stk k).length =
      ∑ k, (c.stk k).length :=
  FrontEndMachine.Transport.stackEquiv_total_length names symbols c.stk

variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

theorem installed_owned_step
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (owned : Owned start.l) :
    Turing.TM2.step ambient (installedCfg names symbols registers labels start) =
      (step caller start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.step_owned names symbols registers labels
    (program caller) ambient Owned installed start owned

/-- This transport uses the supplied actual owned prefix; later caller bodies
are unconstrained. Canonical rank-bounded specializations are proved separately. -/
theorem installed_prefix_of_owned
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Cfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ Owned reached.l) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate_owned names symbols registers labels
    (program caller) ambient Owned installed n start earlier

/-- Arbitrary iterations, including later Boolean/caller behaviour, require
literal agreement on every label of the complete carrier. -/
theorem installed_iterate
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate names symbols registers labels
    (program caller) ambient installed n start

def installedTimed
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (final : Option (Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (step caller) start final bound) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (final.map (installedCfg names symbols registers labels)) bound :=
  FrontEndMachine.Transport.timed names symbols registers labels
    (program caller) ambient installed start final bound run

@[simp] theorem installedTimed_steps
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (final : Option (Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (step caller) start final bound) :
    (installedTimed names symbols registers labels caller ambient installed start final bound run).steps =
      run.steps := rfl

end FurtherInstallation

end Resources.RotationCertificate.StreamMachine

-- END INSTALLATION BASE PASSED2
