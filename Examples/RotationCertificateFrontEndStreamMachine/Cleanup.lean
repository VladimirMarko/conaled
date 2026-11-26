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

theorem cleanupC00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC00.toClosedFixture.start value ctx) cleanupC00.ticks
      (cleanupC00.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    cleanupC00.before (cleanupC00.fields.withUser value) ctx

theorem cleanupC00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC00_actual_first_halt caller value ctx, cleanupC00_actual_exact_peak caller value ctx⟩

theorem cleanupC00E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC00E.toClosedFixture.start value ctx) cleanupC00E.ticks
      (cleanupC00E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    cleanupC00E.before (cleanupC00E.fields.withUser value) ctx

theorem cleanupC00E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC00E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC00E_actual_first_halt caller value ctx, cleanupC00E_actual_exact_peak caller value ctx⟩

theorem cleanupC01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC01.toClosedFixture.start value ctx) cleanupC01.ticks
      (cleanupC01.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 1
    cleanupC01.before (cleanupC01.fields.withUser value) ctx

theorem cleanupC01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC01_actual_first_halt caller value ctx, cleanupC01_actual_exact_peak caller value ctx⟩

theorem cleanupC01E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC01E.toClosedFixture.start value ctx) cleanupC01E.ticks
      (cleanupC01E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 1
    cleanupC01E.before (cleanupC01E.fields.withUser value) ctx

theorem cleanupC01E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC01E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC01E_actual_first_halt caller value ctx, cleanupC01E_actual_exact_peak caller value ctx⟩

theorem cleanupC02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC02.toClosedFixture.start value ctx) cleanupC02.ticks
      (cleanupC02.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 2
    cleanupC02.before (cleanupC02.fields.withUser value) ctx

theorem cleanupC02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC02_actual_first_halt caller value ctx, cleanupC02_actual_exact_peak caller value ctx⟩

theorem cleanupC02E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC02E.toClosedFixture.start value ctx) cleanupC02E.ticks
      (cleanupC02E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 2
    cleanupC02E.before (cleanupC02E.fields.withUser value) ctx

theorem cleanupC02E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC02E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC02E_actual_first_halt caller value ctx, cleanupC02E_actual_exact_peak caller value ctx⟩

theorem cleanupC03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC03.toClosedFixture.start value ctx) cleanupC03.ticks
      (cleanupC03.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 3
    cleanupC03.before (cleanupC03.fields.withUser value) ctx

theorem cleanupC03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC03_actual_first_halt caller value ctx, cleanupC03_actual_exact_peak caller value ctx⟩

theorem cleanupC03E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC03E.toClosedFixture.start value ctx) cleanupC03E.ticks
      (cleanupC03E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 3
    cleanupC03E.before (cleanupC03E.fields.withUser value) ctx

theorem cleanupC03E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC03E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC03E_actual_first_halt caller value ctx, cleanupC03E_actual_exact_peak caller value ctx⟩

theorem cleanupC04_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC04.toClosedFixture.start value ctx) cleanupC04.ticks
      (cleanupC04.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 4
    cleanupC04.before (cleanupC04.fields.withUser value) ctx

theorem cleanupC04_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC04.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC04_actual_first_halt caller value ctx, cleanupC04_actual_exact_peak caller value ctx⟩

theorem cleanupC04E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC04E.toClosedFixture.start value ctx) cleanupC04E.ticks
      (cleanupC04E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 4
    cleanupC04E.before (cleanupC04E.fields.withUser value) ctx

theorem cleanupC04E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC04E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC04E_actual_first_halt caller value ctx, cleanupC04E_actual_exact_peak caller value ctx⟩

theorem cleanupC05_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC05.toClosedFixture.start value ctx) cleanupC05.ticks
      (cleanupC05.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 5
    cleanupC05.before (cleanupC05.fields.withUser value) ctx

theorem cleanupC05_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC05.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC05_actual_first_halt caller value ctx, cleanupC05_actual_exact_peak caller value ctx⟩

theorem cleanupC05E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC05E.toClosedFixture.start value ctx) cleanupC05E.ticks
      (cleanupC05E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 5
    cleanupC05E.before (cleanupC05E.fields.withUser value) ctx

theorem cleanupC05E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC05E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC05E_actual_first_halt caller value ctx, cleanupC05E_actual_exact_peak caller value ctx⟩

theorem cleanupC06_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC06.toClosedFixture.start value ctx) cleanupC06.ticks
      (cleanupC06.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 6
    cleanupC06.before (cleanupC06.fields.withUser value) ctx

theorem cleanupC06_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC06.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC06_actual_first_halt caller value ctx, cleanupC06_actual_exact_peak caller value ctx⟩

theorem cleanupC06E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC06E.toClosedFixture.start value ctx) cleanupC06E.ticks
      (cleanupC06E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 6
    cleanupC06E.before (cleanupC06E.fields.withUser value) ctx

theorem cleanupC06E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC06E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC06E_actual_first_halt caller value ctx, cleanupC06E_actual_exact_peak caller value ctx⟩

theorem cleanupC07_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC07.toClosedFixture.start value ctx) cleanupC07.ticks
      (cleanupC07.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 7
    cleanupC07.before (cleanupC07.fields.withUser value) ctx

theorem cleanupC07_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC07.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC07_actual_first_halt caller value ctx, cleanupC07_actual_exact_peak caller value ctx⟩

theorem cleanupC07E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC07E.toClosedFixture.start value ctx) cleanupC07E.ticks
      (cleanupC07E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 7
    cleanupC07E.before (cleanupC07E.fields.withUser value) ctx

theorem cleanupC07E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC07E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC07E_actual_first_halt caller value ctx, cleanupC07E_actual_exact_peak caller value ctx⟩

theorem cleanupC08_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC08.toClosedFixture.start value ctx) cleanupC08.ticks
      (cleanupC08.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 8
    cleanupC08.before (cleanupC08.fields.withUser value) ctx

theorem cleanupC08_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC08.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC08_actual_first_halt caller value ctx, cleanupC08_actual_exact_peak caller value ctx⟩

theorem cleanupC08E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC08E.toClosedFixture.start value ctx) cleanupC08E.ticks
      (cleanupC08E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 8
    cleanupC08E.before (cleanupC08E.fields.withUser value) ctx

theorem cleanupC08E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC08E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC08E_actual_first_halt caller value ctx, cleanupC08E_actual_exact_peak caller value ctx⟩

theorem cleanupC09_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC09.toClosedFixture.start value ctx) cleanupC09.ticks
      (cleanupC09.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 9
    cleanupC09.before (cleanupC09.fields.withUser value) ctx

theorem cleanupC09_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC09.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC09_actual_first_halt caller value ctx, cleanupC09_actual_exact_peak caller value ctx⟩

theorem cleanupC09E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC09E.toClosedFixture.start value ctx) cleanupC09E.ticks
      (cleanupC09E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 9
    cleanupC09E.before (cleanupC09E.fields.withUser value) ctx

theorem cleanupC09E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC09E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC09E_actual_first_halt caller value ctx, cleanupC09E_actual_exact_peak caller value ctx⟩

theorem cleanupC10_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC10.toClosedFixture.start value ctx) cleanupC10.ticks
      (cleanupC10.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 10
    cleanupC10.before (cleanupC10.fields.withUser value) ctx

theorem cleanupC10_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC10.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC10_actual_first_halt caller value ctx, cleanupC10_actual_exact_peak caller value ctx⟩

theorem cleanupC10E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC10E.toClosedFixture.start value ctx) cleanupC10E.ticks
      (cleanupC10E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 10
    cleanupC10E.before (cleanupC10E.fields.withUser value) ctx

theorem cleanupC10E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC10E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC10E_actual_first_halt caller value ctx, cleanupC10E_actual_exact_peak caller value ctx⟩

theorem cleanupC11_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC11.toClosedFixture.start value ctx) cleanupC11.ticks
      (cleanupC11.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 11
    cleanupC11.before (cleanupC11.fields.withUser value) ctx

theorem cleanupC11_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC11.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC11_actual_first_halt caller value ctx, cleanupC11_actual_exact_peak caller value ctx⟩

theorem cleanupC11E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC11E.toClosedFixture.start value ctx) cleanupC11E.ticks
      (cleanupC11E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 11
    cleanupC11E.before (cleanupC11E.fields.withUser value) ctx

theorem cleanupC11E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC11E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC11E_actual_first_halt caller value ctx, cleanupC11E_actual_exact_peak caller value ctx⟩

theorem cleanupC12_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC12.toClosedFixture.start value ctx) cleanupC12.ticks
      (cleanupC12.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 12
    cleanupC12.before (cleanupC12.fields.withUser value) ctx

theorem cleanupC12_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC12.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC12_actual_first_halt caller value ctx, cleanupC12_actual_exact_peak caller value ctx⟩

theorem cleanupC12E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC12E.toClosedFixture.start value ctx) cleanupC12E.ticks
      (cleanupC12E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 12
    cleanupC12E.before (cleanupC12E.fields.withUser value) ctx

theorem cleanupC12E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC12E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC12E_actual_first_halt caller value ctx, cleanupC12E_actual_exact_peak caller value ctx⟩

theorem cleanupC13_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC13.toClosedFixture.start value ctx) cleanupC13.ticks
      (cleanupC13.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 13
    cleanupC13.before (cleanupC13.fields.withUser value) ctx

theorem cleanupC13_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC13.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC13_actual_first_halt caller value ctx, cleanupC13_actual_exact_peak caller value ctx⟩

theorem cleanupC13E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC13E.toClosedFixture.start value ctx) cleanupC13E.ticks
      (cleanupC13E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 13
    cleanupC13E.before (cleanupC13E.fields.withUser value) ctx

theorem cleanupC13E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC13E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC13E_actual_first_halt caller value ctx, cleanupC13E_actual_exact_peak caller value ctx⟩

theorem cleanupC14_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC14.toClosedFixture.start value ctx) cleanupC14.ticks
      (cleanupC14.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 14
    cleanupC14.before (cleanupC14.fields.withUser value) ctx

theorem cleanupC14_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC14.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC14_actual_first_halt caller value ctx, cleanupC14_actual_exact_peak caller value ctx⟩

theorem cleanupC14E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC14E.toClosedFixture.start value ctx) cleanupC14E.ticks
      (cleanupC14E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 14
    cleanupC14E.before (cleanupC14E.fields.withUser value) ctx

theorem cleanupC14E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC14E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC14E_actual_first_halt caller value ctx, cleanupC14E_actual_exact_peak caller value ctx⟩

theorem cleanupC15_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC15.toClosedFixture.start value ctx) cleanupC15.ticks
      (cleanupC15.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 15
    cleanupC15.before (cleanupC15.fields.withUser value) ctx

theorem cleanupC15_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC15.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC15_actual_first_halt caller value ctx, cleanupC15_actual_exact_peak caller value ctx⟩

theorem cleanupC15E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cleanupC15E.toClosedFixture.start value ctx) cleanupC15E.ticks
      (cleanupC15E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 15
    cleanupC15E.before (cleanupC15E.fields.withUser value) ctx

theorem cleanupC15E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    cleanupC15E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨cleanupC15E_actual_first_halt caller value ctx, cleanupC15E_actual_exact_peak caller value ctx⟩

theorem emitE00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emitE00.toClosedFixture.start value ctx) emitE00.ticks
      (emitE00.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emitE00.before (emitE00.fields.withUser value) ctx

theorem emitE00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emitE00_actual_first_halt caller value ctx, emitE00_actual_exact_peak caller value ctx⟩

theorem emitE01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emitE01.toClosedFixture.start value ctx) emitE01.ticks
      (emitE01.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emitE01.before (emitE01.fields.withUser value) ctx

theorem emitE01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emitE01_actual_first_halt caller value ctx, emitE01_actual_exact_peak caller value ctx⟩

theorem emitE02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emitE02.toClosedFixture.start value ctx) emitE02.ticks
      (emitE02.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emitE02.before (emitE02.fields.withUser value) ctx

theorem emitE02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emitE02_actual_first_halt caller value ctx, emitE02_actual_exact_peak caller value ctx⟩

theorem emitE03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emitE03.toClosedFixture.start value ctx) emitE03.ticks
      (emitE03.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emitE03.before (emitE03.fields.withUser value) ctx

theorem emitE03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emitE03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emitE03_actual_first_halt caller value ctx, emitE03_actual_exact_peak caller value ctx⟩

theorem joinJ00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (joinJ00.toClosedFixture.start value ctx) joinJ00.ticks
      (joinJ00.peak + externalCells ctx) :=
  rejecting_join_has_the_exact_cleanup_peak caller joinJ00.before (joinJ00.fields.withUser value) ctx

theorem joinJ00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨joinJ00_actual_first_halt caller value ctx, joinJ00_actual_exact_peak caller value ctx⟩

theorem joinJ01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (joinJ01.toClosedFixture.start value ctx) joinJ01.ticks
      (joinJ01.peak + externalCells ctx) :=
  boolean_join_has_the_exact_cleanup_peak caller false joinJ01.before (joinJ01.fields.withUser value) ctx

theorem joinJ01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨joinJ01_actual_first_halt caller value ctx, joinJ01_actual_exact_peak caller value ctx⟩

theorem joinJ02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (joinJ02.toClosedFixture.start value ctx) joinJ02.ticks
      (joinJ02.peak + externalCells ctx) :=
  boolean_join_has_the_exact_cleanup_peak caller true joinJ02.before (joinJ02.fields.withUser value) ctx

theorem joinJ02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    joinJ02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨joinJ02_actual_first_halt caller value ctx, joinJ02_actual_exact_peak caller value ctx⟩

theorem emptyCleanupFixture_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emptyCleanupFixture.toClosedFixture.start value ctx) emptyCleanupFixture.ticks
      (emptyCleanupFixture.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    emptyCleanupFixture.before (emptyCleanupFixture.fields.withUser value) ctx

theorem emptyCleanupFixture_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emptyCleanupFixture.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emptyCleanupFixture_actual_first_halt caller value ctx, emptyCleanupFixture_actual_exact_peak caller value ctx⟩

end ExactPhysicalConnections


end Examples.RotationCertificateFrontEndStreamMachine
