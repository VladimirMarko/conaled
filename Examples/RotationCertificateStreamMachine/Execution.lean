import Examples.RotationCertificateStreamMachine.TraceBounds

/-!
# RotationCertificateStreamMachine: Execution
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

theorem a01_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a01.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a01 traceA01 rfl rfl
    (traceA01_steps caller regs ctx) traceA01_owned

theorem a01_literal_evaluation :
    evaluate a01.phase a01.before = ⟨a01.result, a01.after, a01.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a01
    (a01_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a01_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a01.start regs ctx) a01.ticks
      (a01.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA01
    4 0 (traceA01_steps caller regs ctx) traceA01_cells rfl

theorem a02_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a02 traceA02 rfl rfl
    (traceA02_steps caller regs ctx) traceA02_owned

theorem a02_literal_evaluation :
    evaluate a02.phase a02.before = ⟨a02.result, a02.after, a02.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a02
    (a02_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a02_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a02.start regs ctx) a02.ticks
      (a02.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA02
    4 1 (traceA02_steps caller regs ctx) traceA02_cells rfl

theorem a03_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a03 traceA03 rfl rfl
    (traceA03_steps caller regs ctx) traceA03_owned

theorem a03_literal_evaluation :
    evaluate a03.phase a03.before = ⟨a03.result, a03.after, a03.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a03
    (a03_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a03_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a03.start regs ctx) a03.ticks
      (a03.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA03
    5 2 (traceA03_steps caller regs ctx) traceA03_cells rfl

theorem a04_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a04.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a04 traceA04 rfl rfl
    (traceA04_steps caller regs ctx) traceA04_owned

theorem a04_literal_evaluation :
    evaluate a04.phase a04.before = ⟨a04.result, a04.after, a04.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a04
    (a04_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a04_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a04.start regs ctx) a04.ticks
      (a04.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA04
    7 7 (traceA04_steps caller regs ctx) traceA04_cells rfl

theorem a05_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a05.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a05 traceA05 rfl rfl
    (traceA05_steps caller regs ctx) traceA05_owned

theorem a05_literal_evaluation :
    evaluate a05.phase a05.before = ⟨a05.result, a05.after, a05.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a05
    (a05_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a05_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a05.start regs ctx) a05.ticks
      (a05.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA05
    9 12 (traceA05_steps caller regs ctx) traceA05_cells rfl

theorem a06_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a06.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a06 traceA06 rfl rfl
    (traceA06_steps caller regs ctx) traceA06_owned

theorem a06_literal_evaluation :
    evaluate a06.phase a06.before = ⟨a06.result, a06.after, a06.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a06
    (a06_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a06_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a06.start regs ctx) a06.ticks
      (a06.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA06
    4 4 (traceA06_steps caller regs ctx) traceA06_cells rfl

theorem a07_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a07 traceA07 rfl rfl
    (traceA07_steps caller regs ctx) traceA07_owned

theorem a07_literal_evaluation :
    evaluate a07.phase a07.before = ⟨a07.result, a07.after, a07.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a07
    (a07_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a07_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a07.start regs ctx) a07.ticks
      (a07.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA07
    5 3 (traceA07_steps caller regs ctx) traceA07_cells rfl

theorem a08_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a08 traceA08 rfl rfl
    (traceA08_steps caller regs ctx) traceA08_owned

theorem a08_literal_evaluation :
    evaluate a08.phase a08.before = ⟨a08.result, a08.after, a08.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a08
    (a08_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a08_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a08.start regs ctx) a08.ticks
      (a08.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA08
    6 8 (traceA08_steps caller regs ctx) traceA08_cells rfl

theorem a09_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a09 traceA09 rfl rfl
    (traceA09_steps caller regs ctx) traceA09_owned

theorem a09_literal_evaluation :
    evaluate a09.phase a09.before = ⟨a09.result, a09.after, a09.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a09
    (a09_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a09_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a09.start regs ctx) a09.ticks
      (a09.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA09
    8 14 (traceA09_steps caller regs ctx) traceA09_cells rfl

theorem a10_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a10 traceA10 rfl rfl
    (traceA10_steps caller regs ctx) traceA10_owned

theorem a10_literal_evaluation :
    evaluate a10.phase a10.before = ⟨a10.result, a10.after, a10.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a10
    (a10_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a10_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a10.start regs ctx) a10.ticks
      (a10.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA10
    7 12 (traceA10_steps caller regs ctx) traceA10_cells rfl

theorem a11_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a11.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a11 traceA11 rfl rfl
    (traceA11_steps caller regs ctx) traceA11_owned

theorem a11_literal_evaluation :
    evaluate a11.phase a11.before = ⟨a11.result, a11.after, a11.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a11
    (a11_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a11_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a11.start regs ctx) a11.ticks
      (a11.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA11
    11 14 (traceA11_steps caller regs ctx) traceA11_cells rfl

theorem a12_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a12.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a12 traceA12 rfl rfl
    (traceA12_steps caller regs ctx) traceA12_owned

theorem a12_literal_evaluation :
    evaluate a12.phase a12.before = ⟨a12.result, a12.after, a12.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a12
    (a12_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a12_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a12.start regs ctx) a12.ticks
      (a12.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA12
    25 13 (traceA12_steps caller regs ctx) traceA12_cells rfl

theorem a13_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a13.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a13 traceA13 rfl rfl
    (traceA13_steps caller regs ctx) traceA13_owned

theorem a13_literal_evaluation :
    evaluate a13.phase a13.before = ⟨a13.result, a13.after, a13.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a13
    (a13_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a13_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a13.start regs ctx) a13.ticks
      (a13.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA13
    24 13 (traceA13_steps caller regs ctx) traceA13_cells rfl

theorem a14_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a14.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a14 traceA14 rfl rfl
    (traceA14_steps caller regs ctx) traceA14_owned

theorem a14_literal_evaluation :
    evaluate a14.phase a14.before = ⟨a14.result, a14.after, a14.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a14
    (a14_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a14_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a14.start regs ctx) a14.ticks
      (a14.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA14
    13 5 (traceA14_steps caller regs ctx) traceA14_cells rfl

theorem a15_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a15.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a15 traceA15 rfl rfl
    (traceA15_steps caller regs ctx) traceA15_owned

theorem a15_literal_evaluation :
    evaluate a15.phase a15.before = ⟨a15.result, a15.after, a15.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a15
    (a15_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a15_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a15.start regs ctx) a15.ticks
      (a15.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA15
    16 7 (traceA15_steps caller regs ctx) traceA15_cells rfl

theorem a16_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a16.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a16 traceA16 rfl rfl
    (traceA16_steps caller regs ctx) traceA16_owned

theorem a16_literal_evaluation :
    evaluate a16.phase a16.before = ⟨a16.result, a16.after, a16.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a16
    (a16_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a16_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a16.start regs ctx) a16.ticks
      (a16.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA16
    31 18 (traceA16_steps caller regs ctx) traceA16_cells rfl

theorem a17_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a17.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a17 traceA17 rfl rfl
    (traceA17_steps caller regs ctx) traceA17_owned

theorem a17_literal_evaluation :
    evaluate a17.phase a17.before = ⟨a17.result, a17.after, a17.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a17
    (a17_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a17_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a17.start regs ctx) a17.ticks
      (a17.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA17
    33 18 (traceA17_steps caller regs ctx) traceA17_cells rfl

theorem a18_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a18.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a18 traceA18 rfl rfl
    (traceA18_steps caller regs ctx) traceA18_owned

theorem a18_literal_evaluation :
    evaluate a18.phase a18.before = ⟨a18.result, a18.after, a18.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a18
    (a18_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a18_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a18.start regs ctx) a18.ticks
      (a18.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA18
    42 16 (traceA18_steps caller regs ctx) traceA18_cells rfl

theorem a19_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a19.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a19 traceA19 rfl rfl
    (traceA19_steps caller regs ctx) traceA19_owned

theorem a19_literal_evaluation :
    evaluate a19.phase a19.before = ⟨a19.result, a19.after, a19.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a19
    (a19_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a19_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a19.start regs ctx) a19.ticks
      (a19.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA19
    22 15 (traceA19_steps caller regs ctx) traceA19_cells rfl

theorem a20_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a20.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a20 traceA20 rfl rfl
    (traceA20_steps caller regs ctx) traceA20_owned

theorem a20_literal_evaluation :
    evaluate a20.phase a20.before = ⟨a20.result, a20.after, a20.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a20
    (a20_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a20_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a20.start regs ctx) a20.ticks
      (a20.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA20
    25 15 (traceA20_steps caller regs ctx) traceA20_cells rfl

theorem a21_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a21.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a21 traceA21 rfl rfl
    (traceA21_steps caller regs ctx) traceA21_owned

theorem a21_literal_evaluation :
    evaluate a21.phase a21.before = ⟨a21.result, a21.after, a21.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a21
    (a21_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a21_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a21.start regs ctx) a21.ticks
      (a21.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceA21
    24 11 (traceA21_steps caller regs ctx) traceA21_cells rfl

theorem d01_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d01.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d01 traceD01 rfl rfl
    (traceD01_steps caller regs ctx) traceD01_owned

theorem d01_literal_evaluation :
    evaluate d01.phase d01.before = ⟨d01.result, d01.after, d01.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d01
    (d01_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d01_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d01.start regs ctx) d01.ticks
      (d01.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD01
    4 8 (traceD01_steps caller regs ctx) traceD01_cells rfl

theorem d02_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d02 traceD02 rfl rfl
    (traceD02_steps caller regs ctx) traceD02_owned

theorem d02_literal_evaluation :
    evaluate d02.phase d02.before = ⟨d02.result, d02.after, d02.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d02
    (d02_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d02_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d02.start regs ctx) d02.ticks
      (d02.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD02
    9 11 (traceD02_steps caller regs ctx) traceD02_cells rfl

theorem d03_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d03 traceD03 rfl rfl
    (traceD03_steps caller regs ctx) traceD03_owned

theorem d03_literal_evaluation :
    evaluate d03.phase d03.before = ⟨d03.result, d03.after, d03.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d03
    (d03_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d03_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d03.start regs ctx) d03.ticks
      (d03.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD03
    6 3 (traceD03_steps caller regs ctx) traceD03_cells rfl

theorem d04_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d04.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d04 traceD04 rfl rfl
    (traceD04_steps caller regs ctx) traceD04_owned

theorem d04_literal_evaluation :
    evaluate d04.phase d04.before = ⟨d04.result, d04.after, d04.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d04
    (d04_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d04_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d04.start regs ctx) d04.ticks
      (d04.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD04
    7 9 (traceD04_steps caller regs ctx) traceD04_cells rfl

theorem d05_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d05.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d05 traceD05 rfl rfl
    (traceD05_steps caller regs ctx) traceD05_owned

theorem d05_literal_evaluation :
    evaluate d05.phase d05.before = ⟨d05.result, d05.after, d05.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d05
    (d05_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d05_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d05.start regs ctx) d05.ticks
      (d05.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD05
    13 11 (traceD05_steps caller regs ctx) traceD05_cells rfl

theorem d06_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d06.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d06 traceD06 rfl rfl
    (traceD06_steps caller regs ctx) traceD06_owned

theorem d06_literal_evaluation :
    evaluate d06.phase d06.before = ⟨d06.result, d06.after, d06.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d06
    (d06_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d06_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d06.start regs ctx) d06.ticks
      (d06.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD06
    30 18 (traceD06_steps caller regs ctx) traceD06_cells rfl

theorem d07_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d07 traceD07 rfl rfl
    (traceD07_steps caller regs ctx) traceD07_owned

theorem d07_literal_evaluation :
    evaluate d07.phase d07.before = ⟨d07.result, d07.after, d07.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d07
    (d07_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d07_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d07.start regs ctx) d07.ticks
      (d07.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD07
    29 18 (traceD07_steps caller regs ctx) traceD07_cells rfl

theorem d08_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d08 traceD08 rfl rfl
    (traceD08_steps caller regs ctx) traceD08_owned

theorem d08_literal_evaluation :
    evaluate d08.phase d08.before = ⟨d08.result, d08.after, d08.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d08
    (d08_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d08_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d08.start regs ctx) d08.ticks
      (d08.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD08
    7 6 (traceD08_steps caller regs ctx) traceD08_cells rfl

theorem d09_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d09 traceD09 rfl rfl
    (traceD09_steps caller regs ctx) traceD09_owned

theorem d09_literal_evaluation :
    evaluate d09.phase d09.before = ⟨d09.result, d09.after, d09.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d09
    (d09_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d09_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d09.start regs ctx) d09.ticks
      (d09.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD09
    5 0 (traceD09_steps caller regs ctx) traceD09_cells rfl

theorem d10_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d10 traceD10 rfl rfl
    (traceD10_steps caller regs ctx) traceD10_owned

theorem d10_literal_evaluation :
    evaluate d10.phase d10.before = ⟨d10.result, d10.after, d10.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d10
    (d10_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d10_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d10.start regs ctx) d10.ticks
      (d10.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD10
    4 0 (traceD10_steps caller regs ctx) traceD10_cells rfl

theorem d11_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d11.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d11 traceD11 rfl rfl
    (traceD11_steps caller regs ctx) traceD11_owned

theorem d11_literal_evaluation :
    evaluate d11.phase d11.before = ⟨d11.result, d11.after, d11.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d11
    (d11_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d11_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d11.start regs ctx) d11.ticks
      (d11.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD11
    3 1 (traceD11_steps caller regs ctx) traceD11_cells rfl

theorem d12_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d12.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d12 traceD12 rfl rfl
    (traceD12_steps caller regs ctx) traceD12_owned

theorem d12_literal_evaluation :
    evaluate d12.phase d12.before = ⟨d12.result, d12.after, d12.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d12
    (d12_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d12_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d12.start regs ctx) d12.ticks
      (d12.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD12
    2 1 (traceD12_steps caller regs ctx) traceD12_cells rfl

theorem d13_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d13.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d13 traceD13 rfl rfl
    (traceD13_steps caller regs ctx) traceD13_owned

theorem d13_literal_evaluation :
    evaluate d13.phase d13.before = ⟨d13.result, d13.after, d13.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d13
    (d13_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d13_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d13.start regs ctx) d13.ticks
      (d13.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceD13
    1 3 (traceD13_steps caller regs ctx) traceD13_cells rfl

theorem r01_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r01.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r01 traceR01 rfl rfl
    (traceR01_steps caller regs ctx) traceR01_owned

theorem r01_literal_evaluation :
    evaluate r01.phase r01.before = ⟨r01.result, r01.after, r01.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r01
    (r01_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r01_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r01.start regs ctx) r01.ticks
      (r01.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR01
    7 13 (traceR01_steps caller regs ctx) traceR01_cells rfl

theorem r02_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r02 traceR02 rfl rfl
    (traceR02_steps caller regs ctx) traceR02_owned

theorem r02_literal_evaluation :
    evaluate r02.phase r02.before = ⟨r02.result, r02.after, r02.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r02
    (r02_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r02_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r02.start regs ctx) r02.ticks
      (r02.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR02
    4 15 (traceR02_steps caller regs ctx) traceR02_cells rfl

theorem r03_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r03 traceR03 rfl rfl
    (traceR03_steps caller regs ctx) traceR03_owned

theorem r03_literal_evaluation :
    evaluate r03.phase r03.before = ⟨r03.result, r03.after, r03.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r03
    (r03_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r03_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r03.start regs ctx) r03.ticks
      (r03.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR03
    17 16 (traceR03_steps caller regs ctx) traceR03_cells rfl

theorem r04_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r04.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r04 traceR04 rfl rfl
    (traceR04_steps caller regs ctx) traceR04_owned

theorem r04_literal_evaluation :
    evaluate r04.phase r04.before = ⟨r04.result, r04.after, r04.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r04
    (r04_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r04_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r04.start regs ctx) r04.ticks
      (r04.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR04
    27 15 (traceR04_steps caller regs ctx) traceR04_cells rfl

theorem r05_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r05.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r05 traceR05 rfl rfl
    (traceR05_steps caller regs ctx) traceR05_owned

theorem r05_literal_evaluation :
    evaluate r05.phase r05.before = ⟨r05.result, r05.after, r05.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r05
    (r05_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r05_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r05.start regs ctx) r05.ticks
      (r05.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR05
    6 7 (traceR05_steps caller regs ctx) traceR05_cells rfl

theorem r06_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r06.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r06 traceR06 rfl rfl
    (traceR06_steps caller regs ctx) traceR06_owned

theorem r06_literal_evaluation :
    evaluate r06.phase r06.before = ⟨r06.result, r06.after, r06.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r06
    (r06_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r06_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r06.start regs ctx) r06.ticks
      (r06.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR06
    6 7 (traceR06_steps caller regs ctx) traceR06_cells rfl

theorem r07_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r07 traceR07 rfl rfl
    (traceR07_steps caller regs ctx) traceR07_owned

theorem r07_literal_evaluation :
    evaluate r07.phase r07.before = ⟨r07.result, r07.after, r07.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r07
    (r07_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r07_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r07.start regs ctx) r07.ticks
      (r07.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR07
    22 14 (traceR07_steps caller regs ctx) traceR07_cells rfl

theorem r08_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r08 traceR08 rfl rfl
    (traceR08_steps caller regs ctx) traceR08_owned

theorem r08_literal_evaluation :
    evaluate r08.phase r08.before = ⟨r08.result, r08.after, r08.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r08
    (r08_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r08_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r08.start regs ctx) r08.ticks
      (r08.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR08
    41 17 (traceR08_steps caller regs ctx) traceR08_cells rfl

theorem r09_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r09 traceR09 rfl rfl
    (traceR09_steps caller regs ctx) traceR09_owned

theorem r09_literal_evaluation :
    evaluate r09.phase r09.before = ⟨r09.result, r09.after, r09.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r09
    (r09_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r09_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r09.start regs ctx) r09.ticks
      (r09.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR09
    40 17 (traceR09_steps caller regs ctx) traceR09_cells rfl

theorem r10_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r10 traceR10 rfl rfl
    (traceR10_steps caller regs ctx) traceR10_owned

theorem r10_literal_evaluation :
    evaluate r10.phase r10.before = ⟨r10.result, r10.after, r10.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r10
    (r10_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r10_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r10.start regs ctx) r10.ticks
      (r10.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx traceR10
    20 15 (traceR10_steps caller regs ctx) traceR10_cells rfl

theorem every_fixed_literal_evaluation_is_exact :
    ∀ c ∈ allCases, evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩ := by
  intro c member
  simp only [allCases, initialCases, postReadCases, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a01_literal_evaluation
  · exact a02_literal_evaluation
  · exact a03_literal_evaluation
  · exact a04_literal_evaluation
  · exact a05_literal_evaluation
  · exact a06_literal_evaluation
  · exact a07_literal_evaluation
  · exact a08_literal_evaluation
  · exact a09_literal_evaluation
  · exact a10_literal_evaluation
  · exact a11_literal_evaluation
  · exact a12_literal_evaluation
  · exact a13_literal_evaluation
  · exact a14_literal_evaluation
  · exact a15_literal_evaluation
  · exact a16_literal_evaluation
  · exact a17_literal_evaluation
  · exact a18_literal_evaluation
  · exact a19_literal_evaluation
  · exact a20_literal_evaluation
  · exact a21_literal_evaluation
  · exact d01_literal_evaluation
  · exact d02_literal_evaluation
  · exact d03_literal_evaluation
  · exact d04_literal_evaluation
  · exact d05_literal_evaluation
  · exact d06_literal_evaluation
  · exact d07_literal_evaluation
  · exact d08_literal_evaluation
  · exact d09_literal_evaluation
  · exact d10_literal_evaluation
  · exact d11_literal_evaluation
  · exact d12_literal_evaluation
  · exact d13_literal_evaluation
  · exact r01_literal_evaluation
  · exact r02_literal_evaluation
  · exact r03_literal_evaluation
  · exact r04_literal_evaluation
  · exact r05_literal_evaluation
  · exact r06_literal_evaluation
  · exact r07_literal_evaluation
  · exact r08_literal_evaluation
  · exact r09_literal_evaluation
  · exact r10_literal_evaluation

theorem every_original_and_post_read_fixture_is_an_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ allCases, c.RunExpected (step caller) regs ctx := by
  intro c member
  simp only [allCases, initialCases, postReadCases, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a01_actual_first_run caller regs ctx
  · exact a02_actual_first_run caller regs ctx
  · exact a03_actual_first_run caller regs ctx
  · exact a04_actual_first_run caller regs ctx
  · exact a05_actual_first_run caller regs ctx
  · exact a06_actual_first_run caller regs ctx
  · exact a07_actual_first_run caller regs ctx
  · exact a08_actual_first_run caller regs ctx
  · exact a09_actual_first_run caller regs ctx
  · exact a10_actual_first_run caller regs ctx
  · exact a11_actual_first_run caller regs ctx
  · exact a12_actual_first_run caller regs ctx
  · exact a13_actual_first_run caller regs ctx
  · exact a14_actual_first_run caller regs ctx
  · exact a15_actual_first_run caller regs ctx
  · exact a16_actual_first_run caller regs ctx
  · exact a17_actual_first_run caller regs ctx
  · exact a18_actual_first_run caller regs ctx
  · exact a19_actual_first_run caller regs ctx
  · exact a20_actual_first_run caller regs ctx
  · exact a21_actual_first_run caller regs ctx
  · exact d01_actual_first_run caller regs ctx
  · exact d02_actual_first_run caller regs ctx
  · exact d03_actual_first_run caller regs ctx
  · exact d04_actual_first_run caller regs ctx
  · exact d05_actual_first_run caller regs ctx
  · exact d06_actual_first_run caller regs ctx
  · exact d07_actual_first_run caller regs ctx
  · exact d08_actual_first_run caller regs ctx
  · exact d09_actual_first_run caller regs ctx
  · exact d10_actual_first_run caller regs ctx
  · exact d11_actual_first_run caller regs ctx
  · exact d12_actual_first_run caller regs ctx
  · exact d13_actual_first_run caller regs ctx
  · exact r01_actual_first_run caller regs ctx
  · exact r02_actual_first_run caller regs ctx
  · exact r03_actual_first_run caller regs ctx
  · exact r04_actual_first_run caller regs ctx
  · exact r05_actual_first_run caller regs ctx
  · exact r06_actual_first_run caller regs ctx
  · exact r07_actual_first_run caller regs ctx
  · exact r08_actual_first_run caller regs ctx
  · exact r09_actual_first_run caller regs ctx
  · exact r10_actual_first_run caller regs ctx

theorem every_fixed_original_and_post_read_run_has_its_exact_inclusive_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ allCases, c.Expected (step caller) regs ctx := by
  intro c member
  refine ⟨every_original_and_post_read_fixture_is_an_actual_first_run caller regs ctx c member, ?_⟩
  simp only [allCases, initialCases, postReadCases, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a01_actual_exact_peak caller regs ctx
  · exact a02_actual_exact_peak caller regs ctx
  · exact a03_actual_exact_peak caller regs ctx
  · exact a04_actual_exact_peak caller regs ctx
  · exact a05_actual_exact_peak caller regs ctx
  · exact a06_actual_exact_peak caller regs ctx
  · exact a07_actual_exact_peak caller regs ctx
  · exact a08_actual_exact_peak caller regs ctx
  · exact a09_actual_exact_peak caller regs ctx
  · exact a10_actual_exact_peak caller regs ctx
  · exact a11_actual_exact_peak caller regs ctx
  · exact a12_actual_exact_peak caller regs ctx
  · exact a13_actual_exact_peak caller regs ctx
  · exact a14_actual_exact_peak caller regs ctx
  · exact a15_actual_exact_peak caller regs ctx
  · exact a16_actual_exact_peak caller regs ctx
  · exact a17_actual_exact_peak caller regs ctx
  · exact a18_actual_exact_peak caller regs ctx
  · exact a19_actual_exact_peak caller regs ctx
  · exact a20_actual_exact_peak caller regs ctx
  · exact a21_actual_exact_peak caller regs ctx
  · exact d01_actual_exact_peak caller regs ctx
  · exact d02_actual_exact_peak caller regs ctx
  · exact d03_actual_exact_peak caller regs ctx
  · exact d04_actual_exact_peak caller regs ctx
  · exact d05_actual_exact_peak caller regs ctx
  · exact d06_actual_exact_peak caller regs ctx
  · exact d07_actual_exact_peak caller regs ctx
  · exact d08_actual_exact_peak caller regs ctx
  · exact d09_actual_exact_peak caller regs ctx
  · exact d10_actual_exact_peak caller regs ctx
  · exact d11_actual_exact_peak caller regs ctx
  · exact d12_actual_exact_peak caller regs ctx
  · exact d13_actual_exact_peak caller regs ctx
  · exact r01_actual_exact_peak caller regs ctx
  · exact r02_actual_exact_peak caller regs ctx
  · exact r03_actual_exact_peak caller regs ctx
  · exact r04_actual_exact_peak caller regs ctx
  · exact r05_actual_exact_peak caller regs ctx
  · exact r06_actual_exact_peak caller regs ctx
  · exact r07_actual_exact_peak caller regs ctx
  · exact r08_actual_exact_peak caller regs ctx
  · exact r09_actual_exact_peak caller regs ctx
  · exact r10_actual_exact_peak caller regs ctx


end Examples.RotationCertificateStreamMachine
