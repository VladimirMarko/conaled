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

theorem cleanupC00Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC00Boundaries,
      point.Expected cleanupC00.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC00Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 0 cleanupC00.before (cleanupC00.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 0 cleanupC00.before (cleanupC00.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 0 15 cleanupC00.before (cleanupC00.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 0 15 cleanupC00.before)
          (boundaryRegisters 0 15 (cleanupC00.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC00_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC00EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC00EBoundaries,
      point.Expected cleanupC00E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC00EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 0 cleanupC00E.before (cleanupC00E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 0 15 cleanupC00E.before (cleanupC00E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 0 15 cleanupC00E.before)
          (boundaryRegisters 0 15 (cleanupC00E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC00E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC01Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC01Boundaries,
      point.Expected cleanupC01.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC01Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 1 cleanupC01.before (cleanupC01.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 1 cleanupC01.before (cleanupC01.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 1 15 cleanupC01.before (cleanupC01.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 1 15 cleanupC01.before)
          (boundaryRegisters 1 15 (cleanupC01.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC01_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC01EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC01EBoundaries,
      point.Expected cleanupC01E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC01EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 1 cleanupC01E.before (cleanupC01E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 1 15 cleanupC01E.before (cleanupC01E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 1 15 cleanupC01E.before)
          (boundaryRegisters 1 15 (cleanupC01E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC01E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC02Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC02Boundaries,
      point.Expected cleanupC02.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC02Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 2 cleanupC02.before (cleanupC02.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 2 cleanupC02.before (cleanupC02.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 2 15 cleanupC02.before (cleanupC02.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 2 15 cleanupC02.before)
          (boundaryRegisters 2 15 (cleanupC02.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC02_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC02EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC02EBoundaries,
      point.Expected cleanupC02E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC02EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 2 cleanupC02E.before (cleanupC02E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 2 15 cleanupC02E.before (cleanupC02E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 2 15 cleanupC02E.before)
          (boundaryRegisters 2 15 (cleanupC02E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC02E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC03Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC03Boundaries,
      point.Expected cleanupC03.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC03Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 3 cleanupC03.before (cleanupC03.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 3 cleanupC03.before (cleanupC03.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 3 15 cleanupC03.before (cleanupC03.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 3 15 cleanupC03.before)
          (boundaryRegisters 3 15 (cleanupC03.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC03_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC03EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC03EBoundaries,
      point.Expected cleanupC03E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC03EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 3 cleanupC03E.before (cleanupC03E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 3 15 cleanupC03E.before (cleanupC03E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 3 15 cleanupC03E.before)
          (boundaryRegisters 3 15 (cleanupC03E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC03E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC04Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC04Boundaries,
      point.Expected cleanupC04.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC04Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 4 cleanupC04.before (cleanupC04.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 4 cleanupC04.before (cleanupC04.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 4 15 cleanupC04.before (cleanupC04.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 4 15 cleanupC04.before)
          (boundaryRegisters 4 15 (cleanupC04.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC04_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC04EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC04EBoundaries,
      point.Expected cleanupC04E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC04EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 4 cleanupC04E.before (cleanupC04E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 4 15 cleanupC04E.before (cleanupC04E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 4 15 cleanupC04E.before)
          (boundaryRegisters 4 15 (cleanupC04E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC04E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC05Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC05Boundaries,
      point.Expected cleanupC05.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC05Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 5 cleanupC05.before (cleanupC05.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 5 cleanupC05.before (cleanupC05.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 5 15 cleanupC05.before (cleanupC05.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 5 15 cleanupC05.before)
          (boundaryRegisters 5 15 (cleanupC05.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC05_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC05EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC05EBoundaries,
      point.Expected cleanupC05E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC05EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 5 cleanupC05E.before (cleanupC05E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 5 15 cleanupC05E.before (cleanupC05E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 5 15 cleanupC05E.before)
          (boundaryRegisters 5 15 (cleanupC05E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC05E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC06Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC06Boundaries,
      point.Expected cleanupC06.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC06Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 6 cleanupC06.before (cleanupC06.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 6 cleanupC06.before (cleanupC06.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 6 15 cleanupC06.before (cleanupC06.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 6 15 cleanupC06.before)
          (boundaryRegisters 6 15 (cleanupC06.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC06_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC06EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC06EBoundaries,
      point.Expected cleanupC06E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC06EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 6 cleanupC06E.before (cleanupC06E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 6 15 cleanupC06E.before (cleanupC06E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 6 15 cleanupC06E.before)
          (boundaryRegisters 6 15 (cleanupC06E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC06E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC07Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC07Boundaries,
      point.Expected cleanupC07.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC07Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 7 cleanupC07.before (cleanupC07.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 7 cleanupC07.before (cleanupC07.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 7 15 cleanupC07.before (cleanupC07.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 7 15 cleanupC07.before)
          (boundaryRegisters 7 15 (cleanupC07.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC07_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC07EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC07EBoundaries,
      point.Expected cleanupC07E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC07EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 7 cleanupC07E.before (cleanupC07E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 7 15 cleanupC07E.before (cleanupC07E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 7 15 cleanupC07E.before)
          (boundaryRegisters 7 15 (cleanupC07E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC07E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC08Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC08Boundaries,
      point.Expected cleanupC08.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC08Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 8 cleanupC08.before (cleanupC08.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 8 cleanupC08.before (cleanupC08.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 8 15 cleanupC08.before (cleanupC08.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 8 15 cleanupC08.before)
          (boundaryRegisters 8 15 (cleanupC08.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC08_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC08EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC08EBoundaries,
      point.Expected cleanupC08E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC08EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 8 cleanupC08E.before (cleanupC08E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 8 15 cleanupC08E.before (cleanupC08E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 8 15 cleanupC08E.before)
          (boundaryRegisters 8 15 (cleanupC08E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC08E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC09Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC09Boundaries,
      point.Expected cleanupC09.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC09Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 9 cleanupC09.before (cleanupC09.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 9 cleanupC09.before (cleanupC09.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 9 15 cleanupC09.before (cleanupC09.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 9 15 cleanupC09.before)
          (boundaryRegisters 9 15 (cleanupC09.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC09_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC09EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC09EBoundaries,
      point.Expected cleanupC09E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC09EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 9 cleanupC09E.before (cleanupC09E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 9 15 cleanupC09E.before (cleanupC09E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 9 15 cleanupC09E.before)
          (boundaryRegisters 9 15 (cleanupC09E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC09E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC10Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC10Boundaries,
      point.Expected cleanupC10.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC10Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 10 cleanupC10.before (cleanupC10.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 10 cleanupC10.before (cleanupC10.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 10 15 cleanupC10.before (cleanupC10.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 10 15 cleanupC10.before)
          (boundaryRegisters 10 15 (cleanupC10.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC10_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC10EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC10EBoundaries,
      point.Expected cleanupC10E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC10EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 10 cleanupC10E.before (cleanupC10E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 10 15 cleanupC10E.before (cleanupC10E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 10 15 cleanupC10E.before)
          (boundaryRegisters 10 15 (cleanupC10E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC10E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC11Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC11Boundaries,
      point.Expected cleanupC11.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC11Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 11 cleanupC11.before (cleanupC11.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 11 cleanupC11.before (cleanupC11.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 11 15 cleanupC11.before (cleanupC11.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 11 15 cleanupC11.before)
          (boundaryRegisters 11 15 (cleanupC11.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC11_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC11EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC11EBoundaries,
      point.Expected cleanupC11E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC11EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 11 cleanupC11E.before (cleanupC11E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 11 15 cleanupC11E.before (cleanupC11E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 11 15 cleanupC11E.before)
          (boundaryRegisters 11 15 (cleanupC11E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC11E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC12Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC12Boundaries,
      point.Expected cleanupC12.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC12Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 12 cleanupC12.before (cleanupC12.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 12 cleanupC12.before (cleanupC12.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 12 15 cleanupC12.before (cleanupC12.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 12 15 cleanupC12.before)
          (boundaryRegisters 12 15 (cleanupC12.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC12_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC12EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC12EBoundaries,
      point.Expected cleanupC12E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC12EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 12 cleanupC12E.before (cleanupC12E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 12 15 cleanupC12E.before (cleanupC12E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 12 15 cleanupC12E.before)
          (boundaryRegisters 12 15 (cleanupC12E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC12E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC13Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC13Boundaries,
      point.Expected cleanupC13.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC13Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 13 cleanupC13.before (cleanupC13.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 13 cleanupC13.before (cleanupC13.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 13 15 cleanupC13.before (cleanupC13.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 13 15 cleanupC13.before)
          (boundaryRegisters 13 15 (cleanupC13.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC13_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC13EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC13EBoundaries,
      point.Expected cleanupC13E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC13EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 13 cleanupC13E.before (cleanupC13E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 13 15 cleanupC13E.before (cleanupC13E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 13 15 cleanupC13E.before)
          (boundaryRegisters 13 15 (cleanupC13E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC13E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC14Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC14Boundaries,
      point.Expected cleanupC14.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC14Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 14 cleanupC14.before (cleanupC14.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 14 cleanupC14.before (cleanupC14.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 14 15 cleanupC14.before (cleanupC14.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 14 15 cleanupC14.before)
          (boundaryRegisters 14 15 (cleanupC14.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC14_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC14EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC14EBoundaries,
      point.Expected cleanupC14E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC14EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 14 cleanupC14E.before (cleanupC14E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 14 15 cleanupC14E.before (cleanupC14E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 14 15 cleanupC14E.before)
          (boundaryRegisters 14 15 (cleanupC14E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC14E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC15Boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC15Boundaries,
      point.Expected cleanupC15.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC15Boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 15 cleanupC15.before (cleanupC15.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 15 15 cleanupC15.before (cleanupC15.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 15 15 cleanupC15.before)
          (boundaryRegisters 15 15 (cleanupC15.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC15_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem cleanupC15EBoundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ cleanupC15EBoundaries,
      point.Expected cleanupC15E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [cleanupC15EBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 15 15 cleanupC15E.before (cleanupC15E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 15 15 cleanupC15E.before)
          (boundaryRegisters 15 15 (cleanupC15E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (cleanupC15E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem all_partial_clear_boundaries_are_literal (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ pair ∈ partialClearBoundaries, ∀ point ∈ pair.2,
      point.Expected pair.1.toClosedFixture (step caller) value ctx := by
  intro pair member
  simp only [partialClearBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cleanupC00Boundaries_are_actual caller value ctx
  · exact cleanupC00EBoundaries_are_actual caller value ctx
  · exact cleanupC01Boundaries_are_actual caller value ctx
  · exact cleanupC01EBoundaries_are_actual caller value ctx
  · exact cleanupC02Boundaries_are_actual caller value ctx
  · exact cleanupC02EBoundaries_are_actual caller value ctx
  · exact cleanupC03Boundaries_are_actual caller value ctx
  · exact cleanupC03EBoundaries_are_actual caller value ctx
  · exact cleanupC04Boundaries_are_actual caller value ctx
  · exact cleanupC04EBoundaries_are_actual caller value ctx
  · exact cleanupC05Boundaries_are_actual caller value ctx
  · exact cleanupC05EBoundaries_are_actual caller value ctx
  · exact cleanupC06Boundaries_are_actual caller value ctx
  · exact cleanupC06EBoundaries_are_actual caller value ctx
  · exact cleanupC07Boundaries_are_actual caller value ctx
  · exact cleanupC07EBoundaries_are_actual caller value ctx
  · exact cleanupC08Boundaries_are_actual caller value ctx
  · exact cleanupC08EBoundaries_are_actual caller value ctx
  · exact cleanupC09Boundaries_are_actual caller value ctx
  · exact cleanupC09EBoundaries_are_actual caller value ctx
  · exact cleanupC10Boundaries_are_actual caller value ctx
  · exact cleanupC10EBoundaries_are_actual caller value ctx
  · exact cleanupC11Boundaries_are_actual caller value ctx
  · exact cleanupC11EBoundaries_are_actual caller value ctx
  · exact cleanupC12Boundaries_are_actual caller value ctx
  · exact cleanupC12EBoundaries_are_actual caller value ctx
  · exact cleanupC13Boundaries_are_actual caller value ctx
  · exact cleanupC13EBoundaries_are_actual caller value ctx
  · exact cleanupC14Boundaries_are_actual caller value ctx
  · exact cleanupC14EBoundaries_are_actual caller value ctx
  · exact cleanupC15Boundaries_are_actual caller value ctx
  · exact cleanupC15EBoundaries_are_actual caller value ctx

end CleanupBoundaryConnections

end Examples.RotationCertificateFrontEndStreamMachine

