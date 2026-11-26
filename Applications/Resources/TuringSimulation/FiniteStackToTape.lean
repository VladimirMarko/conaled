import Applications.Resources.TuringSimulation.StackToTape
import Applications.Resources.TuringSimulation.FiniteControl
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite source programmes and their encoded tape initialization

The maximum number of source stack actions is fixed by the finite programme.
The target initial state uses the supplied package fields and the existing
marked multiplexed input encoding. It is not an executed input serializer.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.StackToTape

open Function
open Turing Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- A fixed finite source programme determines its action bound before the
input or any runtime branch is chosen. -/
def finiteActionBound [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup (fun l => actionBound (M l))

theorem actionBound_le_finiteActionBound [Fintype Λ]
    (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) :
    actionBound (M l) ≤ finiteActionBound M := by
  change actionBound (M l) ≤ Finset.univ.sup (fun q => actionBound (M q))
  exact Finset.le_sup (f := fun q => actionBound (M q)) (Finset.mem_univ l)

/-- Explicit target initialization on the existing encoded input. The main
label and registers are supplied by the package, without ambient defaults. -/
def encodedInitial (tm : Turing.FinTM2) (raw : List (tm.Γ tm.k₀)) :
    TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ :=
  ⟨some (Λ'.normal tm.main), tm.initialState, Tape.mk₁ (trInit tm.k₀ raw)⟩

/-- The existing initial relation instantiated with the package's actual main
label and registers. The full dependent initial stack family is retained. -/
theorem encodedInitial_related (tm : Turing.FinTM2) (raw : List (tm.Γ tm.k₀)) :
    TrCfg (Turing.initList tm raw) (encodedInitial tm raw) := by
  let : Inhabited tm.Λ := ⟨tm.main⟩
  let : Inhabited tm.σ := ⟨tm.initialState⟩
  have hsource : (TM2.init tm.k₀ raw : TM2.Cfg tm.Γ tm.Λ tm.σ) =
      Turing.initList tm raw := by
    unfold TM2.init Turing.initList
    congr 1
    funext j
    by_cases hj : j = tm.k₀
    · subst j
      simp
    · simp only [Function.update_of_ne hj, dite_eq_right hj]
  have hrel := trCfg_init (Λ := tm.Λ) (σ := tm.σ) tm.k₀ raw
  rw [hsource] at hrel
  exact hrel

end Resources.TuringSimulation.StackToTape

namespace Resources.TuringSimulation.StackToTape

open Turing Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- Read the actual marker-position observation from the complete native
simulation relation. The head sees the bottom (last source-list element) of
each stack; it must not be confused with the source stack's top. -/
theorem related_marker_observation
    (source : TM2.Cfg Γ Λ σ) (target : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (related : TrCfg source target) :
    target.l = source.l.map Λ'.normal ∧ target.var = source.var ∧
      target.Tape.head.1 = true ∧
      ∀ k, target.Tape.head.2 k = (source.stk k).reverse[0]? := by
  cases related with
  | mk L hL =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [Tape.mk'_head, addBottom_head_fst]
    · intro k
      rw [Tape.mk'_head, ← ListBlank.nth_zero, addBottom_nth_snd]
      exact stk_nth_val 0 (hL k)

end Resources.TuringSimulation.StackToTape

namespace Resources.TuringSimulation.StackToTape

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- Every source statement is supported by all source labels, even when its
goto computes a label from the current register. -/
theorem supportsStmt_univ [Fintype Λ] (q : TM2.Stmt Γ Λ σ) :
    TM2.SupportsStmt (Finset.univ : Finset Λ) q := by
  induction q with
  | push _ _ _ IH => exact IH
  | peek _ _ _ IH => exact IH
  | pop _ _ _ IH => exact IH
  | load _ _ IH => exact IH
  | branch _ _ _ IH₁ IH₂ => exact ⟨IH₁, IH₂⟩
  | goto _ => exact fun _ => Finset.mem_univ _
  | halt => trivial

/-- A fixed finite source programme starts and remains inside all its labels.
The `Inhabited` instance identifies its actual chosen starting label. -/
theorem source_supports_univ [Fintype Λ] [Inhabited Λ]
    (M : Λ → TM2.Stmt Γ Λ σ) :
    TM2.Supports M (Finset.univ : Finset Λ) :=
  ⟨Finset.mem_univ _, fun l _ => supportsStmt_univ (M l)⟩

/-- The native finite primitive-control support obtained by applying the two
existing simulator support constructions to the fixed source programme. -/
noncomputable def stackControlSupport [DecidableEq K] [Fintype Λ] [Fintype σ]
    (M : Λ → TM2.Stmt Γ Λ σ) : Finset (TM1to0.Λ' (TM2to1.tr M)) :=
  TM1to0.trStmts (TM2to1.tr M) (TM2to1.trSupp M (Finset.univ : Finset Λ))

/-- Actual primitive transitions from the actual default stay inside the
finite set. Alphabet finiteness is independent of this control-support fact. -/
theorem stackControlSupport_supports [DecidableEq K] [Fintype Λ] [Fintype σ]
    [Inhabited Λ] [Inhabited σ] (M : Λ → TM2.Stmt Γ Λ σ) :
    TM0.Supports (TM1to0.tr (TM2to1.tr M)) (↑(stackControlSupport M)) :=
  TM1to0.tr_supports (TM2to1.tr M)
    (TM2to1.tr_supports M (source_supports_univ M))

end Resources.TuringSimulation.StackToTape


namespace Resources.TuringSimulation.StackToTape.Package

open Resources.TuringSimulation.FiniteControl

open Function Turing

abbrev Alphabet (tm : Turing.FinTM2) := TM2to1.Γ' tm.K tm.Γ

abbrev AmbientControl (tm : Turing.FinTM2) :=
  TM1to0.Λ' (TM2to1.tr tm.m)

/-- The actual two-stage native finite support. No global Fintype on either
translated continuation-bearing ambient carrier is assumed. -/
noncomputable def controlSupport (tm : Turing.FinTM2) :
    Finset (AmbientControl tm) := by
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype tm.σ := tm.σFin
  exact Resources.TuringSimulation.StackToTape.stackControlSupport tm.m

/-- The actual native primitive initial control, derived from the package's
main label and initial registers rather than arbitrary ambient defaults. -/
@[instance_reducible] def ambientInhabited (tm : Turing.FinTM2) : Inhabited (AmbientControl tm) :=
  ⟨(some ((TM2to1.tr tm.m) (.normal tm.main)), tm.initialState)⟩

/-- The existing primitive translation of this fixed source package. -/
def ambientMachine (tm : Turing.FinTM2) :
    @TM0.Machine (Alphabet tm) (AmbientControl tm) (ambientInhabited tm) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  letI : Inhabited tm.σ := ⟨tm.initialState⟩
  exact TM1to0.tr (TM2to1.tr tm.m)

/-- The native support theorem instantiated with the source package's actual
main/register defaults. This covers every primitive intermediate control. -/
theorem controlSupport_supports (tm : Turing.FinTM2) :
    letI : Inhabited (AmbientControl tm) := ambientInhabited tm
    TM0.Supports (ambientMachine tm) (↑(controlSupport tm)) := by
  let : Inhabited tm.Λ := ⟨tm.main⟩
  let : Inhabited tm.σ := ⟨tm.initialState⟩
  let : Fintype tm.Λ := tm.ΛFin
  let : Fintype tm.σ := tm.σFin
  change TM0.Supports (TM1to0.tr (TM2to1.tr tm.m))
    (↑(Resources.TuringSimulation.StackToTape.stackControlSupport tm.m))
  exact Resources.TuringSimulation.StackToTape.stackControlSupport_supports tm.m

abbrev Control (tm : Turing.FinTM2) :=
  {q : AmbientControl tm // q ∈ controlSupport tm}

/-- The actual finite control carrier, independently of the input. -/
@[instance_reducible] noncomputable def controlFintype (tm : Turing.FinTM2) : Fintype (Control tm) :=
  inferInstance

/-- All-index alphabet finiteness is required separately from FinTM2's
input-only field. The resulting native product alphabet is finite. -/
@[instance_reducible] def alphabetFintype (tm : Turing.FinTM2) [∀ k, Fintype (tm.Γ k)] :
    Fintype (Alphabet tm) := by
  letI : Fintype tm.K := tm.kFin
  infer_instance

/-- The finite control starts at the same supported actual primitive default. -/
@[instance_reducible] def controlInhabited (tm : Turing.FinTM2) : Inhabited (Control tm) :=
  ⟨⟨(ambientInhabited tm).default, (controlSupport_supports tm).1⟩⟩

/-- The actual finite-carrier primitive machine. Together with
`controlFintype` and the separately justified `alphabetFintype`, this is the
finite-state, finite-alphabet TM0 on the existing encoded input alphabet. -/
noncomputable def machine (tm : Turing.FinTM2) :
    @TM0.Machine (Alphabet tm) (Control tm) (controlInhabited tm) := by
  letI : Inhabited (AmbientControl tm) := ambientInhabited tm
  exact restrictMachine (ambientMachine tm) (controlSupport tm)
    (controlSupport_supports tm).1

/-- Only the control carrier changes. The native configuration map retains
the complete tape, including the bottom marker and every dependent stack track. -/
noncomputable def mapCfg (tm : Turing.FinTM2) :
    TM0.Cfg (Alphabet tm) (AmbientControl tm) → TM0.Cfg (Alphabet tm) (Control tm) := by
  letI : Inhabited (AmbientControl tm) := ambientInhabited tm
  exact restrictCfg (controlSupport tm) (controlSupport_supports tm).1

theorem mapCfg_supported (tm : Turing.FinTM2)
    (c : TM0.Cfg (Alphabet tm) (AmbientControl tm)) (hc : c.q ∈ controlSupport tm) :
    mapCfg tm c = ⟨⟨c.q, hc⟩, c.Tape⟩ := by
  let : Inhabited (AmbientControl tm) := ambientInhabited tm
  exact restrictCfg_supported (controlSupport tm) (controlSupport_supports tm).1 c hc

theorem mapCfg_tape (tm : Turing.FinTM2)
    (c : TM0.Cfg (Alphabet tm) (AmbientControl tm)) :
    (mapCfg tm c).Tape = c.Tape := by
  let : Inhabited (AmbientControl tm) := ambientInhabited tm
  change (restrictCfg (controlSupport tm) (controlSupport_supports tm).1 c).Tape = c.Tape
  rw [restrictCfg_eq]

/-- The actual native primitive initial configuration on the existing
encoded input. It is the native trCfg image of normal main/initialState. -/
def initial (tm : Turing.FinTM2) (raw : List (tm.Γ tm.k₀)) :
    TM0.Cfg (Alphabet tm) (AmbientControl tm) :=
  ⟨(some ((TM2to1.tr tm.m) (.normal tm.main)), tm.initialState),
    Tape.mk₁ (TM2to1.trInit tm.k₀ raw)⟩

theorem initial_eq_trCfg (tm : Turing.FinTM2) (raw : List (tm.Γ tm.k₀)) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    letI : Inhabited tm.σ := ⟨tm.initialState⟩
    initial tm raw = TM1to0.trCfg (TM2to1.tr tm.m)
      (⟨some (.normal tm.main), tm.initialState, Tape.mk₁ (TM2to1.trInit tm.k₀ raw)⟩ :
        TM1.Cfg (Alphabet tm) (TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ) := rfl

theorem initial_eq_init (tm : Turing.FinTM2) (raw : List (tm.Γ tm.k₀)) :
    letI : Inhabited (AmbientControl tm) := ambientInhabited tm
    initial tm raw =
      (TM0.init (TM2to1.trInit tm.k₀ raw) : TM0.Cfg (Alphabet tm) (AmbientControl tm)) := rfl

theorem initial_supported (tm : Turing.FinTM2) (raw : List (tm.Γ tm.k₀)) :
    (initial tm raw).q ∈ controlSupport tm := by
  exact (controlSupport_supports tm).1

/-- Native finite-machine initialization uses the same encoded tape and the
same actual initial control; restricting control adds no transition. -/
theorem mapCfg_initial (tm : Turing.FinTM2) (raw : List (tm.Γ tm.k₀)) :
    letI : Inhabited (Control tm) := controlInhabited tm
    mapCfg tm (initial tm raw) =
      (TM0.init (TM2to1.trInit tm.k₀ raw) : TM0.Cfg (Alphabet tm) (Control tm)) := by
  let : Inhabited (AmbientControl tm) := ambientInhabited tm
  let : Inhabited (Control tm) := controlInhabited tm
  exact restrict_init (controlSupport tm) (controlSupport_supports tm).1
    (TM2to1.trInit tm.k₀ raw)

/-- Consume an actual supported primitive witness. The target retains the
whole optional endpoint and the identical count and bound. -/
noncomputable def restrictRun (tm : Turing.FinTM2)
    (c : TM0.Cfg (Alphabet tm) (AmbientControl tm)) (hc : c.q ∈ controlSupport tm)
    (b : Option (TM0.Cfg (Alphabet tm) (AmbientControl tm))) (B : ℕ)
    (h : letI : Inhabited (AmbientControl tm) := ambientInhabited tm
      StateTransition.EvalsToInTime (TM0.step (ambientMachine tm)) c b B) :
    letI : Inhabited (Control tm) := controlInhabited tm
    StateTransition.EvalsToInTime (TM0.step (machine tm))
      (mapCfg tm c) (b.map (mapCfg tm)) B := by
  letI : Inhabited (AmbientControl tm) := ambientInhabited tm
  letI : Inhabited (Control tm) := controlInhabited tm
  exact restrictEvalsToInTime (ambientMachine tm) (controlSupport tm)
    (controlSupport_supports tm) c hc b B h

theorem restrictRun_steps (tm : Turing.FinTM2)
    (c : TM0.Cfg (Alphabet tm) (AmbientControl tm)) (hc : c.q ∈ controlSupport tm)
    (b : Option (TM0.Cfg (Alphabet tm) (AmbientControl tm))) (B : ℕ)
    (h : letI : Inhabited (AmbientControl tm) := ambientInhabited tm
      StateTransition.EvalsToInTime (TM0.step (ambientMachine tm)) c b B) :
    (restrictRun tm c hc b B h).steps = h.steps := rfl

/-- The initial consumer discharges support from the fixed package and
starts the actual finite primitive machine with native TM0.init. It still
expects trInit-encoded input, and makes no ordinary raw-Boolean I/O claim. -/
noncomputable def restrictInitialRun (tm : Turing.FinTM2)
    (raw : List (tm.Γ tm.k₀))
    (b : Option (TM0.Cfg (Alphabet tm) (AmbientControl tm))) (B : ℕ)
    (h : letI : Inhabited (AmbientControl tm) := ambientInhabited tm
      StateTransition.EvalsToInTime (TM0.step (ambientMachine tm)) (initial tm raw) b B) :
    letI : Inhabited (Control tm) := controlInhabited tm
    StateTransition.EvalsToInTime (TM0.step (machine tm))
      (TM0.init (TM2to1.trInit tm.k₀ raw)) (b.map (mapCfg tm)) B := by
  letI : Inhabited (AmbientControl tm) := ambientInhabited tm
  letI : Inhabited (Control tm) := controlInhabited tm
  exact restrictInitialEvalsToInTime (ambientMachine tm) (controlSupport tm)
    (controlSupport_supports tm) (TM2to1.trInit tm.k₀ raw) b B h

theorem restrictInitialRun_steps (tm : Turing.FinTM2)
    (raw : List (tm.Γ tm.k₀))
    (b : Option (TM0.Cfg (Alphabet tm) (AmbientControl tm))) (B : ℕ)
    (h : letI : Inhabited (AmbientControl tm) := ambientInhabited tm
      StateTransition.EvalsToInTime (TM0.step (ambientMachine tm)) (initial tm raw) b B) :
    (restrictInitialRun tm raw b B h).steps = h.steps := rfl

end Resources.TuringSimulation.StackToTape.Package


namespace Resources.TuringSimulation.StackToTape.Package

open Resources.TuringSimulation.FiniteControl

open Function Turing

/-- Direct support-closed transition for the fixed package. The runtime body
uses only the existing primitive translator; membership is a proof field.
The original main/initialState-derived finite default remains unchanged. -/
def closedMachine (tm : Turing.FinTM2) :
    @TM0.Machine (Alphabet tm) (Control tm) (controlInhabited tm) :=
  fun q a =>
    match h : ambientMachine tm q.val a with
    | none => none
    | some (q', act) => some (⟨q', (controlSupport_supports tm).2 h q.property⟩, act)

/-- The constructive transition is the exact same native restricted machine
as before; this is an equality of transition functions, not a new simulation. -/
theorem closedMachine_eq (tm : Turing.FinTM2) : closedMachine tm = machine tm := by
  let : Inhabited (AmbientControl tm) := ambientInhabited tm
  funext q a
  unfold closedMachine
  split
  · rename_i hstep
    simp only [machine, restrictMachine, TM0.Machine.map, identityPointed,
      PointedMap.mk_val, id_eq, hstep, Option.map_none]
  · rename_i q' act hstep
    have hq' : q' ∈ controlSupport tm :=
      (controlSupport_supports tm).2 hstep q.property
    have hlabel : restrictLabel (controlSupport tm) (controlSupport_supports tm).1 q' =
        ⟨q', hq'⟩ := by
      apply Subtype.ext
      exact restrictLabel_val (controlSupport tm) (controlSupport_supports tm).1 q' hq'
    cases act <;>
      simp only [machine, restrictMachine, TM0.Machine.map, identityPointed,
        PointedMap.mk_val, id_eq, hstep, Option.map_some, Prod.map, TM0.Stmt.map, hlabel]

/-- Consume the existing actual primitive witness from encoded native init.
Only the equality of transition functions is used; count and whole optional
endpoint stay the same, including the distinction between live halt and none. -/
def closedInitialRun (tm : Turing.FinTM2)
    (raw : List (tm.Γ tm.k₀))
    (b : Option (TM0.Cfg (Alphabet tm) (AmbientControl tm))) (B : ℕ)
    (h : letI : Inhabited (AmbientControl tm) := ambientInhabited tm
      StateTransition.EvalsToInTime (TM0.step (ambientMachine tm)) (initial tm raw) b B) :
    letI : Inhabited (Control tm) := controlInhabited tm
    StateTransition.EvalsToInTime (TM0.step (closedMachine tm))
      (TM0.init (TM2to1.trInit tm.k₀ raw)) (b.map (mapCfg tm)) B := by
  letI : Inhabited (Control tm) := controlInhabited tm
  refine {
    toEvalsTo := { steps := h.steps, evals_in_steps := ?_ }
    steps_le_m := h.steps_le_m }
  rw [closedMachine_eq]
  exact (restrictInitialRun tm raw b B h).evals_in_steps

theorem closedInitialRun_steps (tm : Turing.FinTM2)
    (raw : List (tm.Γ tm.k₀))
    (b : Option (TM0.Cfg (Alphabet tm) (AmbientControl tm))) (B : ℕ)
    (h : letI : Inhabited (AmbientControl tm) := ambientInhabited tm
      StateTransition.EvalsToInTime (TM0.step (ambientMachine tm)) (initial tm raw) b B) :
    (closedInitialRun tm raw b B h).steps = h.steps := rfl

end Resources.TuringSimulation.StackToTape.Package

namespace Resources.TuringSimulation.StackToTape

open Turing Turing.TM2to1

/-- The existing encoded input has one marker cell even for empty raw input.
This is a list-length fact, not an executed serializer or an input-cost claim. -/
theorem trInit_length {K : Type*} {Γ : K → Type*} [DecidableEq K]
    (k : K) (raw : List (Γ k)) : (trInit k raw).length = max raw.length 1 := by
  let row : Γ k → Γ' K Γ :=
    fun a => (false, Function.update (fun _ => none) k (some a))
  change (raw.reverse.map row).tail.length + 1 = max raw.length 1
  rw [List.length_tail, List.length_map, List.length_reverse]
  omega

end Resources.TuringSimulation.StackToTape
