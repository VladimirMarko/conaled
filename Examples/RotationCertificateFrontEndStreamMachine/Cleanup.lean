import Examples.RotationCertificateFrontEndStreamMachine.Runtime

/-!
# RotationCertificateFrontEndStreamMachine: Cleanup
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Exhaustive domains and exact physical cleanup contracts -/

-- Name the component decisions so the complete finite sum is synthesized at defaults.
local instance : DecidableEq (FrontEndMachine.ExtraLabel Empty) := inferInstance
local instance : DecidableEq (FrontEndMachine.Label Empty) := inferInstance
local instance : DecidableEq (FuelDispatchMachine.Label Empty) := inferInstance
local instance : DecidableEq (MoveApplyMachine.External Empty) := inferInstance
local instance : DecidableEq (MoveApplyMachine.Label Empty) := inferInstance
local instance : DecidableEq (TreeEqualityMachine.Label Empty) := inferInstance
local instance : DecidableEq (StreamMachine.Label Empty) := inferInstance
local instance : DecidableEq Phase := inferInstance

theorem the_96_phase_domains_are_distinct : phaseDomains.Nodup := by decide

theorem the_96_phase_domains_are_complete (phase : Phase) : phase ∈ phaseDomains := by
  have cardinality : phaseDomains.toFinset.card = Fintype.card Phase := by
    rw [List.toFinset_card_of_nodup the_96_phase_domains_are_distinct,
      phase_domains_count, card_phase]
  have complete := Finset.eq_univ_of_card phaseDomains.toFinset cardinality
  exact List.mem_toFinset.mp (complete ▸ Finset.mem_univ phase)

section ExactPhysicalConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  (caller : Λ → Statement Γ Λ R)

theorem exact_peak_from_the_actual_public_prefix_contract
    {start : Cfg Γ Λ R} {ticks peak : Nat}
    (checked : Resources.RotationCertificate.FrontEndStreamMachine.ExactPeak caller start ticks peak) :
    ExactPeak (step caller) start ticks peak := by
  constructor
  · exact checked.1
  · obtain ⟨n, bound, reached, executed, cells⟩ := checked.2
    exact ⟨n, reached, bound, executed, cells⟩

theorem arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak
    (index : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some (clearLabel index)) regs D ctx)
      (suffixCells index D + (16 - index.val) + 1)
      (max (prefixCells index D + suffixCells index D) (prefixCells index D + 1) + externalCells ctx) :=
  exact_peak_from_the_actual_public_prefix_contract caller (cleanup_peak caller index D regs ctx)

/-- Compose actual inclusive prefixes; the peak is attained in one of the two segments. -/
theorem exact_peaks_compose
    {start middle : Cfg Γ Λ R} {m n firstPeak secondPeak : Nat}
    (executed : Runs (step caller) start m middle)
    (first : ExactPeak (step caller) start m firstPeak)
    (second : ExactPeak (step caller) middle n secondPeak) :
    ExactPeak (step caller) start (m + n) (max firstPeak secondPeak) := by
  constructor
  · exact PrefixProperty.trans caller executed
      (fun j bound reached run => (first.1 j bound reached run).trans (Nat.le_max_left _ _))
      (fun j bound reached run => (second.1 j bound reached run).trans (Nat.le_max_right _ _))
  · by_cases larger : secondPeak ≤ firstPeak
    · obtain ⟨j, reached, bound, run, cells⟩ := first.2
      exact ⟨j, reached, by omega, run, cells.trans (Nat.max_eq_left larger).symm⟩
    · obtain ⟨j, reached, bound, run, cells⟩ := second.2
      refine ⟨j + m, reached, by omega, ?_, cells.trans (Nat.max_eq_right (by omega)).symm⟩
      change (next caller)^[j + m] (some start) = some reached
      change (next caller)^[m] (some start) = some middle at executed
      rw [Function.iterate_add_apply, executed]
      exact run

/-- A load-and-goto join changes no physical word, including at its endpoint. -/
theorem one_step_with_unchanged_words_has_its_initial_mass_as_peak
    {start finish : Cfg Γ Λ R} (executed : step caller start = some finish)
    (same : physicalCells finish = physicalCells start) :
    ExactPeak (step caller) start 1 (physicalCells start) := by
  have run : Runs (step caller) start 1 finish := executed
  constructor
  · intro n bound reached arrived
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl
    · have equal := Option.some.inj arrived
      subst reached
      exact Nat.le_refl _
    · have equal := Option.some.inj (run.symm.trans arrived)
      subst reached
      exact Nat.le_of_eq same
  · exact ⟨0, start, by omega, rfl, rfl⟩

theorem rejecting_join_has_the_exact_cleanup_peak
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some (phaseLabel rejectPhase)) regs D ctx)
      (1 + cleanupSteps 0 D) (max (localCells D) 1 + externalCells ctx) := by
  have first := one_step_with_unchanged_words_has_its_initial_mass_as_peak caller
    (reject_step caller D regs ctx) (by rw [actual_physical_cells_of_cfg, actual_physical_cells_of_cfg])
  have second := arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller
    0 D (answerRegisters false regs) ctx
  have joined := exact_peaks_compose caller ((phase_step_localRun caller (reject_step caller D regs ctx)).iterate caller)
    first second
  rw [actual_physical_cells_of_cfg] at joined
  have prefixZero : prefixCells 0 D = 0 := by
    simp [prefixCells, suffixCells, localCells]
  rw [prefixZero, Nat.zero_add, Nat.zero_add] at joined
  have suffixZero : suffixCells 0 D = localCells D := by
    simpa only [prefixZero, Nat.zero_add] using prefixCells_add_suffixCells 0 D
  rw [suffixZero] at joined
  have equation : max (localCells D + externalCells ctx)
      (max (localCells D) 1 + externalCells ctx) = max (localCells D) 1 + externalCells ctx :=
    Nat.max_eq_right (Nat.add_le_add_right (Nat.le_max_left _ _) _)
  exact equation ▸ joined

theorem boolean_join_has_the_exact_cleanup_peak
    (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some (phaseLabel (resultPhase bit))) regs D ctx)
      (1 + cleanupSteps 0 D) (max (localCells D) 1 + externalCells ctx) := by
  have first := one_step_with_unchanged_words_has_its_initial_mass_as_peak caller
    (result_step caller bit D regs ctx) (by rw [actual_physical_cells_of_cfg, actual_physical_cells_of_cfg])
  have second := arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller
    0 D (answerRegisters bit regs) ctx
  have joined := exact_peaks_compose caller ((phase_step_localRun caller (result_step caller bit D regs ctx)).iterate caller)
    first second
  rw [actual_physical_cells_of_cfg] at joined
  have prefixZero : prefixCells 0 D = 0 := by
    simp [prefixCells, suffixCells, localCells]
  rw [prefixZero, Nat.zero_add, Nat.zero_add] at joined
  have suffixZero : suffixCells 0 D = localCells D := by
    simpa only [prefixZero, Nat.zero_add] using prefixCells_add_suffixCells 0 D
  rw [suffixZero] at joined
  have equation : max (localCells D + externalCells ctx)
      (max (localCells D) 1 + externalCells ctx) = max (localCells D) 1 + externalCells ctx :=
    Nat.max_eq_right (Nat.add_le_add_right (Nat.le_max_left _ _) _)
  exact equation ▸ joined

theorem clear_C00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C00.toClosedFixture.start value ctx) clear_C00.ticks
      (clear_C00.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    clear_C00.before (clear_C00.fields.withUser value) ctx

theorem clear_C00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C00_actual_first_halt caller value ctx, clear_C00_actual_exact_peak caller value ctx⟩

theorem clear_C00E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C00E.toClosedFixture.start value ctx) clear_C00E.ticks
      (clear_C00E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    clear_C00E.before (clear_C00E.fields.withUser value) ctx

theorem clear_C00E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C00E_actual_first_halt caller value ctx, clear_C00E_actual_exact_peak caller value ctx⟩

theorem clear_C01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C01.toClosedFixture.start value ctx) clear_C01.ticks
      (clear_C01.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 1
    clear_C01.before (clear_C01.fields.withUser value) ctx

theorem clear_C01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C01_actual_first_halt caller value ctx, clear_C01_actual_exact_peak caller value ctx⟩

theorem clear_C01E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C01E.toClosedFixture.start value ctx) clear_C01E.ticks
      (clear_C01E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 1
    clear_C01E.before (clear_C01E.fields.withUser value) ctx

theorem clear_C01E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C01E_actual_first_halt caller value ctx, clear_C01E_actual_exact_peak caller value ctx⟩

theorem clear_C02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C02.toClosedFixture.start value ctx) clear_C02.ticks
      (clear_C02.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 2
    clear_C02.before (clear_C02.fields.withUser value) ctx

theorem clear_C02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C02_actual_first_halt caller value ctx, clear_C02_actual_exact_peak caller value ctx⟩

theorem clear_C02E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C02E.toClosedFixture.start value ctx) clear_C02E.ticks
      (clear_C02E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 2
    clear_C02E.before (clear_C02E.fields.withUser value) ctx

theorem clear_C02E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C02E_actual_first_halt caller value ctx, clear_C02E_actual_exact_peak caller value ctx⟩

theorem clear_C03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C03.toClosedFixture.start value ctx) clear_C03.ticks
      (clear_C03.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 3
    clear_C03.before (clear_C03.fields.withUser value) ctx

theorem clear_C03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C03_actual_first_halt caller value ctx, clear_C03_actual_exact_peak caller value ctx⟩

theorem clear_C03E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C03E.toClosedFixture.start value ctx) clear_C03E.ticks
      (clear_C03E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 3
    clear_C03E.before (clear_C03E.fields.withUser value) ctx

theorem clear_C03E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C03E_actual_first_halt caller value ctx, clear_C03E_actual_exact_peak caller value ctx⟩

theorem clear_C04_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C04.toClosedFixture.start value ctx) clear_C04.ticks
      (clear_C04.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 4
    clear_C04.before (clear_C04.fields.withUser value) ctx

theorem clear_C04_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C04_actual_first_halt caller value ctx, clear_C04_actual_exact_peak caller value ctx⟩

theorem clear_C04E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C04E.toClosedFixture.start value ctx) clear_C04E.ticks
      (clear_C04E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 4
    clear_C04E.before (clear_C04E.fields.withUser value) ctx

theorem clear_C04E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C04E_actual_first_halt caller value ctx, clear_C04E_actual_exact_peak caller value ctx⟩

theorem clear_C05_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C05.toClosedFixture.start value ctx) clear_C05.ticks
      (clear_C05.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 5
    clear_C05.before (clear_C05.fields.withUser value) ctx

theorem clear_C05_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C05_actual_first_halt caller value ctx, clear_C05_actual_exact_peak caller value ctx⟩

theorem clear_C05E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C05E.toClosedFixture.start value ctx) clear_C05E.ticks
      (clear_C05E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 5
    clear_C05E.before (clear_C05E.fields.withUser value) ctx

theorem clear_C05E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C05E_actual_first_halt caller value ctx, clear_C05E_actual_exact_peak caller value ctx⟩

theorem clear_C06_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C06.toClosedFixture.start value ctx) clear_C06.ticks
      (clear_C06.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 6
    clear_C06.before (clear_C06.fields.withUser value) ctx

theorem clear_C06_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C06_actual_first_halt caller value ctx, clear_C06_actual_exact_peak caller value ctx⟩

theorem clear_C06E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C06E.toClosedFixture.start value ctx) clear_C06E.ticks
      (clear_C06E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 6
    clear_C06E.before (clear_C06E.fields.withUser value) ctx

theorem clear_C06E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C06E_actual_first_halt caller value ctx, clear_C06E_actual_exact_peak caller value ctx⟩

theorem clear_C07_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C07.toClosedFixture.start value ctx) clear_C07.ticks
      (clear_C07.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 7
    clear_C07.before (clear_C07.fields.withUser value) ctx

theorem clear_C07_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C07_actual_first_halt caller value ctx, clear_C07_actual_exact_peak caller value ctx⟩

theorem clear_C07E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C07E.toClosedFixture.start value ctx) clear_C07E.ticks
      (clear_C07E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 7
    clear_C07E.before (clear_C07E.fields.withUser value) ctx

theorem clear_C07E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C07E_actual_first_halt caller value ctx, clear_C07E_actual_exact_peak caller value ctx⟩

theorem clear_C08_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C08.toClosedFixture.start value ctx) clear_C08.ticks
      (clear_C08.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 8
    clear_C08.before (clear_C08.fields.withUser value) ctx

theorem clear_C08_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C08_actual_first_halt caller value ctx, clear_C08_actual_exact_peak caller value ctx⟩

theorem clear_C08E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C08E.toClosedFixture.start value ctx) clear_C08E.ticks
      (clear_C08E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 8
    clear_C08E.before (clear_C08E.fields.withUser value) ctx

theorem clear_C08E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C08E_actual_first_halt caller value ctx, clear_C08E_actual_exact_peak caller value ctx⟩

theorem clear_C09_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C09.toClosedFixture.start value ctx) clear_C09.ticks
      (clear_C09.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 9
    clear_C09.before (clear_C09.fields.withUser value) ctx

theorem clear_C09_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C09_actual_first_halt caller value ctx, clear_C09_actual_exact_peak caller value ctx⟩

theorem clear_C09E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C09E.toClosedFixture.start value ctx) clear_C09E.ticks
      (clear_C09E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 9
    clear_C09E.before (clear_C09E.fields.withUser value) ctx

theorem clear_C09E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C09E_actual_first_halt caller value ctx, clear_C09E_actual_exact_peak caller value ctx⟩

theorem clear_C10_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C10.toClosedFixture.start value ctx) clear_C10.ticks
      (clear_C10.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 10
    clear_C10.before (clear_C10.fields.withUser value) ctx

theorem clear_C10_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C10_actual_first_halt caller value ctx, clear_C10_actual_exact_peak caller value ctx⟩

theorem clear_C10E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C10E.toClosedFixture.start value ctx) clear_C10E.ticks
      (clear_C10E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 10
    clear_C10E.before (clear_C10E.fields.withUser value) ctx

theorem clear_C10E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C10E_actual_first_halt caller value ctx, clear_C10E_actual_exact_peak caller value ctx⟩

theorem clear_C11_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C11.toClosedFixture.start value ctx) clear_C11.ticks
      (clear_C11.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 11
    clear_C11.before (clear_C11.fields.withUser value) ctx

theorem clear_C11_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C11_actual_first_halt caller value ctx, clear_C11_actual_exact_peak caller value ctx⟩

theorem clear_C11E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C11E.toClosedFixture.start value ctx) clear_C11E.ticks
      (clear_C11E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 11
    clear_C11E.before (clear_C11E.fields.withUser value) ctx

theorem clear_C11E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C11E_actual_first_halt caller value ctx, clear_C11E_actual_exact_peak caller value ctx⟩

theorem clear_C12_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C12.toClosedFixture.start value ctx) clear_C12.ticks
      (clear_C12.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 12
    clear_C12.before (clear_C12.fields.withUser value) ctx

theorem clear_C12_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C12_actual_first_halt caller value ctx, clear_C12_actual_exact_peak caller value ctx⟩

theorem clear_C12E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C12E.toClosedFixture.start value ctx) clear_C12E.ticks
      (clear_C12E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 12
    clear_C12E.before (clear_C12E.fields.withUser value) ctx

theorem clear_C12E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C12E_actual_first_halt caller value ctx, clear_C12E_actual_exact_peak caller value ctx⟩

theorem clear_C13_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C13.toClosedFixture.start value ctx) clear_C13.ticks
      (clear_C13.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 13
    clear_C13.before (clear_C13.fields.withUser value) ctx

theorem clear_C13_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C13_actual_first_halt caller value ctx, clear_C13_actual_exact_peak caller value ctx⟩

theorem clear_C13E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C13E.toClosedFixture.start value ctx) clear_C13E.ticks
      (clear_C13E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 13
    clear_C13E.before (clear_C13E.fields.withUser value) ctx

theorem clear_C13E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C13E_actual_first_halt caller value ctx, clear_C13E_actual_exact_peak caller value ctx⟩

theorem clear_C14_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C14.toClosedFixture.start value ctx) clear_C14.ticks
      (clear_C14.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 14
    clear_C14.before (clear_C14.fields.withUser value) ctx

theorem clear_C14_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C14_actual_first_halt caller value ctx, clear_C14_actual_exact_peak caller value ctx⟩

theorem clear_C14E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C14E.toClosedFixture.start value ctx) clear_C14E.ticks
      (clear_C14E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 14
    clear_C14E.before (clear_C14E.fields.withUser value) ctx

theorem clear_C14E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C14E_actual_first_halt caller value ctx, clear_C14E_actual_exact_peak caller value ctx⟩

theorem clear_C15_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C15.toClosedFixture.start value ctx) clear_C15.ticks
      (clear_C15.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 15
    clear_C15.before (clear_C15.fields.withUser value) ctx

theorem clear_C15_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C15_actual_first_halt caller value ctx, clear_C15_actual_exact_peak caller value ctx⟩

theorem clear_C15E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C15E.toClosedFixture.start value ctx) clear_C15E.ticks
      (clear_C15E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 15
    clear_C15E.before (clear_C15E.fields.withUser value) ctx

theorem clear_C15E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C15E_actual_first_halt caller value ctx, clear_C15E_actual_exact_peak caller value ctx⟩

theorem emit_E00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E00.toClosedFixture.start value ctx) emit_E00.ticks
      (emit_E00.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E00.before (emit_E00.fields.withUser value) ctx

theorem emit_E00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E00_actual_first_halt caller value ctx, emit_E00_actual_exact_peak caller value ctx⟩

theorem emit_E01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E01.toClosedFixture.start value ctx) emit_E01.ticks
      (emit_E01.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E01.before (emit_E01.fields.withUser value) ctx

theorem emit_E01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E01_actual_first_halt caller value ctx, emit_E01_actual_exact_peak caller value ctx⟩

theorem emit_E02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E02.toClosedFixture.start value ctx) emit_E02.ticks
      (emit_E02.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E02.before (emit_E02.fields.withUser value) ctx

theorem emit_E02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E02_actual_first_halt caller value ctx, emit_E02_actual_exact_peak caller value ctx⟩

theorem emit_E03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E03.toClosedFixture.start value ctx) emit_E03.ticks
      (emit_E03.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E03.before (emit_E03.fields.withUser value) ctx

theorem emit_E03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E03_actual_first_halt caller value ctx, emit_E03_actual_exact_peak caller value ctx⟩

theorem join_J00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (join_J00.toClosedFixture.start value ctx) join_J00.ticks
      (join_J00.peak + externalCells ctx) :=
  rejecting_join_has_the_exact_cleanup_peak caller join_J00.before (join_J00.fields.withUser value) ctx

theorem join_J00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨join_J00_actual_first_halt caller value ctx, join_J00_actual_exact_peak caller value ctx⟩

theorem join_J01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (join_J01.toClosedFixture.start value ctx) join_J01.ticks
      (join_J01.peak + externalCells ctx) :=
  boolean_join_has_the_exact_cleanup_peak caller false join_J01.before (join_J01.fields.withUser value) ctx

theorem join_J01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨join_J01_actual_first_halt caller value ctx, join_J01_actual_exact_peak caller value ctx⟩

theorem join_J02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (join_J02.toClosedFixture.start value ctx) join_J02.ticks
      (join_J02.peak + externalCells ctx) :=
  boolean_join_has_the_exact_cleanup_peak caller true join_J02.before (join_J02.fields.withUser value) ctx

theorem join_J02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨join_J02_actual_first_halt caller value ctx, join_J02_actual_exact_peak caller value ctx⟩

theorem clear_CZERO_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_CZERO.toClosedFixture.start value ctx) clear_CZERO.ticks
      (clear_CZERO.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    clear_CZERO.before (clear_CZERO.fields.withUser value) ctx

theorem clear_CZERO_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_CZERO.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_CZERO_actual_first_halt caller value ctx, clear_CZERO_actual_exact_peak caller value ctx⟩

end ExactPhysicalConnections


end Examples.RotationCertificateFrontEndStreamMachine
