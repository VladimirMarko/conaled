# Accumulated-work draft: starting state and agreed interface

Recorded 2026-11-02 before any repository implementation for FDSA-XW01.

- Frozen requirements: `accumulated-work-requirements.md`, SHA-256
  `85c651891cf8c8ee016706bf8baad7711dbd9965eb20ad5c6e96d2ab112728e1`.
- Worktree: `conaled-accumulated-work`.
- Branch: `work/fdsa-accumulated-work`.
- Starting HEAD: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Index, tracked worktree and nonignored untracked status: clean.
- This base is the unvalidated Chapter 1 repair, not an accepted dependency.
- Shared dependency-package symlink only; no shared project build outputs.
- No source implementation or compiler invocation had occurred at this record.

Root owns the connected examples, research explanation, public imports and
commit. The architecture contributor owns only
`Applications/Probability/AccumulatedWork.lean`. All work remains in the
existing book workflow; final review is pending validation of an immutable
candidate. No additional compiler or mutation of the active old Chapter 1
checkout is authorized by this assignment.

## Mathematical choice

The source preflight illustrates the argument with finite real-valued sums on
a probability space. The API preflight exposes the direct, more general
nonnegative extended-real route through existing countable lower-integral
identities. The frozen unit adopts that route. Absorbed finite source
executions are ordinary specializations, with a separate proof that their
actual observed cost equals the sum. This avoids turning nonintegrable or
infinite work into a totalized real zero. Neither source note supplies an
algorithm's conditional sampling or cost correspondence.

## Agreed proposed interface

Namespace: `Applications.Probability.AccumulatedWork`.
Common explicit arguments: `(μ : Measure Ω)` and
`(X : Nat → Ω → ℝ≥0∞)`; implicit `{q N : ℝ≥0∞}`.

The contributor supplied these names and argument orders before source work:

- `lintegral_le_geometric μ X initial drift t`
- `lintegral_tsum_shift_le μ X measurable initial drift w`
- `lintegral_tsum_le μ X measurable initial drift`
- `lintegral_tsum_lt_top μ X measurable initial drift hq hNtop`
- `measure_tsum_ge_le μ X measurable initial drift w hq hNzero hNtop prefix`
- `measure_tsum_ge_le_of_stage_le μ X measurable initial drift w hq hNzero hNtop stageBound`

Here `measurable` means `∀t, AEMeasurable (X t) μ`, `initial` bounds the
zero-time integral by N, and `drift` bounds each successor integral by q
times its predecessor. The prefix and stage premises are almost-everywhere
bounds from the frozen requirements. These are proposed interfaces for
coordinated drafting, not inspected elaborated theorem signatures or evidence
that proofs exist. Any later material signature correction must be recorded
without weakening the requirements.

The first connected case was fixed independently as uniform Fin 8 with stage
means `1,1/2,1/4,1/8`, actual total mean `15/8`, and a nonempty threshold-three
tail of mass `1/4`. The generic bounds are two and one-half respectively.
The independent calculation file, q=0 case, zero-cap failure and prefix-cap
failure are retained in the requirements. A passing finite calculation is
not a Lean validation result.
