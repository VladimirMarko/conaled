import Examples.RotationCertificateFrontEndStreamMachine.Cleanup

/-!
# RotationCertificateFrontEndStreamMachine: Boundaries
-/

namespace Examples.RotationCertificateFrontEndStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine
local instance : DecidableEq (FrontEndMachine.ExtraLabel Empty) := inferInstance
local instance : DecidableEq (FrontEndMachine.Label Empty) := inferInstance
local instance : DecidableEq (FuelDispatchMachine.Label Empty) := inferInstance
local instance : DecidableEq (MoveApplyMachine.External Empty) := inferInstance
local instance : DecidableEq (MoveApplyMachine.Label Empty) := inferInstance
local instance : DecidableEq (TreeEqualityMachine.Label Empty) := inferInstance
local instance : DecidableEq (StreamMachine.Label Empty) := inferInstance
local instance : DecidableEq Phase := inferInstance

/-! ## The fixed selected cleanup boundaries are actual configurations -/

section CleanupBoundaryConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  (caller : Λ → Statement Γ Λ R)

omit [Fintype K] in
/-- All intermediate slot prefixes use the real transported finite cleaner. -/
theorem every_indexed_cleanup_prefix_retains_all_nonactive_words
    (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx)
      ((∑ k : Fin 16, if i.val ≤ k.val ∧ k.val < j.val then slotLength k D + 1 else 0) + t)
      (cfg (some (clearLabel j))
        (if t = 0 then (if i = j then regs else occupancyRegisters false regs)
          else occupancyRegisters true regs)
        (dropData j t (boundaryData i j D)) ctx) := by
  have run := cleanup_prefix_iterate caller i j t D regs ctx ordered within
  have registers := cleanupPrefixCfg_registers (Λ := Λ) i j t regs D ctx
  change (drainRegisters (boundaryRegisters i j regs) t) = _ at registers
  change (next caller)^[boundarySteps i j D + t]
    (some (cfg (some (clearLabel i)) regs D ctx)) = _
  simpa only [cleanupPrefixCfg, registers] using run

theorem clear_C00_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C00_boundaries,
      point.Expected clear_C00.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C00_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 0 clear_C00.before (clear_C00.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 0 clear_C00.before (clear_C00.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 0 15 clear_C00.before (clear_C00.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 0 15 clear_C00.before)
          (boundaryRegisters 0 15 (clear_C00.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C00_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C00E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C00E_boundaries,
      point.Expected clear_C00E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C00E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 0 clear_C00E.before (clear_C00E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 0 15 clear_C00E.before (clear_C00E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 0 15 clear_C00E.before)
          (boundaryRegisters 0 15 (clear_C00E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C00E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C01_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C01_boundaries,
      point.Expected clear_C01.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C01_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 1 clear_C01.before (clear_C01.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 1 clear_C01.before (clear_C01.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 1 15 clear_C01.before (clear_C01.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 1 15 clear_C01.before)
          (boundaryRegisters 1 15 (clear_C01.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C01_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C01E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C01E_boundaries,
      point.Expected clear_C01E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C01E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 1 clear_C01E.before (clear_C01E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 1 15 clear_C01E.before (clear_C01E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 1 15 clear_C01E.before)
          (boundaryRegisters 1 15 (clear_C01E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C01E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C02_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C02_boundaries,
      point.Expected clear_C02.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C02_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 2 clear_C02.before (clear_C02.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 2 clear_C02.before (clear_C02.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 2 15 clear_C02.before (clear_C02.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 2 15 clear_C02.before)
          (boundaryRegisters 2 15 (clear_C02.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C02_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C02E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C02E_boundaries,
      point.Expected clear_C02E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C02E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 2 clear_C02E.before (clear_C02E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 2 15 clear_C02E.before (clear_C02E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 2 15 clear_C02E.before)
          (boundaryRegisters 2 15 (clear_C02E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C02E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C03_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C03_boundaries,
      point.Expected clear_C03.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C03_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 3 clear_C03.before (clear_C03.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 3 clear_C03.before (clear_C03.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 3 15 clear_C03.before (clear_C03.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 3 15 clear_C03.before)
          (boundaryRegisters 3 15 (clear_C03.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C03_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C03E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C03E_boundaries,
      point.Expected clear_C03E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C03E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 3 clear_C03E.before (clear_C03E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 3 15 clear_C03E.before (clear_C03E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 3 15 clear_C03E.before)
          (boundaryRegisters 3 15 (clear_C03E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C03E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C04_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C04_boundaries,
      point.Expected clear_C04.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C04_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 4 clear_C04.before (clear_C04.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 4 clear_C04.before (clear_C04.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 4 15 clear_C04.before (clear_C04.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 4 15 clear_C04.before)
          (boundaryRegisters 4 15 (clear_C04.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C04_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C04E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C04E_boundaries,
      point.Expected clear_C04E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C04E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 4 clear_C04E.before (clear_C04E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 4 15 clear_C04E.before (clear_C04E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 4 15 clear_C04E.before)
          (boundaryRegisters 4 15 (clear_C04E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C04E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C05_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C05_boundaries,
      point.Expected clear_C05.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C05_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 5 clear_C05.before (clear_C05.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 5 clear_C05.before (clear_C05.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 5 15 clear_C05.before (clear_C05.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 5 15 clear_C05.before)
          (boundaryRegisters 5 15 (clear_C05.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C05_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C05E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C05E_boundaries,
      point.Expected clear_C05E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C05E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 5 clear_C05E.before (clear_C05E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 5 15 clear_C05E.before (clear_C05E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 5 15 clear_C05E.before)
          (boundaryRegisters 5 15 (clear_C05E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C05E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C06_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C06_boundaries,
      point.Expected clear_C06.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C06_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 6 clear_C06.before (clear_C06.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 6 clear_C06.before (clear_C06.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 6 15 clear_C06.before (clear_C06.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 6 15 clear_C06.before)
          (boundaryRegisters 6 15 (clear_C06.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C06_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C06E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C06E_boundaries,
      point.Expected clear_C06E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C06E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 6 clear_C06E.before (clear_C06E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 6 15 clear_C06E.before (clear_C06E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 6 15 clear_C06E.before)
          (boundaryRegisters 6 15 (clear_C06E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C06E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C07_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C07_boundaries,
      point.Expected clear_C07.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C07_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 7 clear_C07.before (clear_C07.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 7 clear_C07.before (clear_C07.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 7 15 clear_C07.before (clear_C07.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 7 15 clear_C07.before)
          (boundaryRegisters 7 15 (clear_C07.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C07_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C07E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C07E_boundaries,
      point.Expected clear_C07E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C07E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 7 clear_C07E.before (clear_C07E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 7 15 clear_C07E.before (clear_C07E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 7 15 clear_C07E.before)
          (boundaryRegisters 7 15 (clear_C07E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C07E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C08_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C08_boundaries,
      point.Expected clear_C08.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C08_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 8 clear_C08.before (clear_C08.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 8 clear_C08.before (clear_C08.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 8 15 clear_C08.before (clear_C08.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 8 15 clear_C08.before)
          (boundaryRegisters 8 15 (clear_C08.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C08_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C08E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C08E_boundaries,
      point.Expected clear_C08E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C08E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 8 clear_C08E.before (clear_C08E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 8 15 clear_C08E.before (clear_C08E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 8 15 clear_C08E.before)
          (boundaryRegisters 8 15 (clear_C08E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C08E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C09_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C09_boundaries,
      point.Expected clear_C09.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C09_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 9 clear_C09.before (clear_C09.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 9 clear_C09.before (clear_C09.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 9 15 clear_C09.before (clear_C09.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 9 15 clear_C09.before)
          (boundaryRegisters 9 15 (clear_C09.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C09_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C09E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C09E_boundaries,
      point.Expected clear_C09E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C09E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 9 clear_C09E.before (clear_C09E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 9 15 clear_C09E.before (clear_C09E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 9 15 clear_C09E.before)
          (boundaryRegisters 9 15 (clear_C09E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C09E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C10_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C10_boundaries,
      point.Expected clear_C10.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C10_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 10 clear_C10.before (clear_C10.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 10 clear_C10.before (clear_C10.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 10 15 clear_C10.before (clear_C10.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 10 15 clear_C10.before)
          (boundaryRegisters 10 15 (clear_C10.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C10_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C10E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C10E_boundaries,
      point.Expected clear_C10E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C10E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 10 clear_C10E.before (clear_C10E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 10 15 clear_C10E.before (clear_C10E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 10 15 clear_C10E.before)
          (boundaryRegisters 10 15 (clear_C10E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C10E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C11_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C11_boundaries,
      point.Expected clear_C11.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C11_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 11 clear_C11.before (clear_C11.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 11 clear_C11.before (clear_C11.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 11 15 clear_C11.before (clear_C11.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 11 15 clear_C11.before)
          (boundaryRegisters 11 15 (clear_C11.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C11_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C11E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C11E_boundaries,
      point.Expected clear_C11E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C11E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 11 clear_C11E.before (clear_C11E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 11 15 clear_C11E.before (clear_C11E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 11 15 clear_C11E.before)
          (boundaryRegisters 11 15 (clear_C11E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C11E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C12_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C12_boundaries,
      point.Expected clear_C12.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C12_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 12 clear_C12.before (clear_C12.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 12 clear_C12.before (clear_C12.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 12 15 clear_C12.before (clear_C12.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 12 15 clear_C12.before)
          (boundaryRegisters 12 15 (clear_C12.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C12_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C12E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C12E_boundaries,
      point.Expected clear_C12E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C12E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 12 clear_C12E.before (clear_C12E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 12 15 clear_C12E.before (clear_C12E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 12 15 clear_C12E.before)
          (boundaryRegisters 12 15 (clear_C12E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C12E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C13_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C13_boundaries,
      point.Expected clear_C13.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C13_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 13 clear_C13.before (clear_C13.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 13 clear_C13.before (clear_C13.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 13 15 clear_C13.before (clear_C13.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 13 15 clear_C13.before)
          (boundaryRegisters 13 15 (clear_C13.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C13_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C13E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C13E_boundaries,
      point.Expected clear_C13E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C13E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 13 clear_C13E.before (clear_C13E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 13 15 clear_C13E.before (clear_C13E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 13 15 clear_C13E.before)
          (boundaryRegisters 13 15 (clear_C13E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C13E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C14_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C14_boundaries,
      point.Expected clear_C14.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C14_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 14 clear_C14.before (clear_C14.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 14 clear_C14.before (clear_C14.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 14 15 clear_C14.before (clear_C14.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 14 15 clear_C14.before)
          (boundaryRegisters 14 15 (clear_C14.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C14_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C14E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C14E_boundaries,
      point.Expected clear_C14E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C14E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 14 clear_C14E.before (clear_C14E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 14 15 clear_C14E.before (clear_C14E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 14 15 clear_C14E.before)
          (boundaryRegisters 14 15 (clear_C14E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C14E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C15_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C15_boundaries,
      point.Expected clear_C15.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C15_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 15 clear_C15.before (clear_C15.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 15 15 clear_C15.before (clear_C15.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 15 15 clear_C15.before)
          (boundaryRegisters 15 15 (clear_C15.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C15_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C15E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C15E_boundaries,
      point.Expected clear_C15E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C15E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 15 15 clear_C15E.before (clear_C15E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 15 15 clear_C15E.before)
          (boundaryRegisters 15 15 (clear_C15E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C15E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem all_partial_clear_boundaries_are_literal (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ pair ∈ partialClearBoundaries, ∀ point ∈ pair.2,
      point.Expected pair.1.toClosedFixture (step caller) value ctx := by
  intro pair member
  simp only [partialClearBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact clear_C00_boundaries_are_actual caller value ctx
  · exact clear_C00E_boundaries_are_actual caller value ctx
  · exact clear_C01_boundaries_are_actual caller value ctx
  · exact clear_C01E_boundaries_are_actual caller value ctx
  · exact clear_C02_boundaries_are_actual caller value ctx
  · exact clear_C02E_boundaries_are_actual caller value ctx
  · exact clear_C03_boundaries_are_actual caller value ctx
  · exact clear_C03E_boundaries_are_actual caller value ctx
  · exact clear_C04_boundaries_are_actual caller value ctx
  · exact clear_C04E_boundaries_are_actual caller value ctx
  · exact clear_C05_boundaries_are_actual caller value ctx
  · exact clear_C05E_boundaries_are_actual caller value ctx
  · exact clear_C06_boundaries_are_actual caller value ctx
  · exact clear_C06E_boundaries_are_actual caller value ctx
  · exact clear_C07_boundaries_are_actual caller value ctx
  · exact clear_C07E_boundaries_are_actual caller value ctx
  · exact clear_C08_boundaries_are_actual caller value ctx
  · exact clear_C08E_boundaries_are_actual caller value ctx
  · exact clear_C09_boundaries_are_actual caller value ctx
  · exact clear_C09E_boundaries_are_actual caller value ctx
  · exact clear_C10_boundaries_are_actual caller value ctx
  · exact clear_C10E_boundaries_are_actual caller value ctx
  · exact clear_C11_boundaries_are_actual caller value ctx
  · exact clear_C11E_boundaries_are_actual caller value ctx
  · exact clear_C12_boundaries_are_actual caller value ctx
  · exact clear_C12E_boundaries_are_actual caller value ctx
  · exact clear_C13_boundaries_are_actual caller value ctx
  · exact clear_C13E_boundaries_are_actual caller value ctx
  · exact clear_C14_boundaries_are_actual caller value ctx
  · exact clear_C14E_boundaries_are_actual caller value ctx
  · exact clear_C15_boundaries_are_actual caller value ctx
  · exact clear_C15E_boundaries_are_actual caller value ctx

end CleanupBoundaryConnections

end Examples.RotationCertificateFrontEndStreamMachine

