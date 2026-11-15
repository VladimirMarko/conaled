# Shared accumulated random-work requirements

Recorded 2026-11-02 before implementation. This is FDSA-XW01, a bounded
cross-cutting unit under the user's explicit exception for shared concerns.
The governing request is `../REQUEST.md`; no chapter is accepted. Chapter 1
must still pass its repaired-candidate gates before later chapter activation.

## Origin, base and scope

The source needs are the distinct random-execution obligations retained for
Chapters 2, 3 and 10, especially C03-068 through C03-075. Their exact laws,
conditional sampling and algorithm/cost correspondences remain chapter work.
Read `../research/probability-api-preflight.md` (SHA-256
`eacc4181f3cb9e49598521be8149c65fab306a5c288ddd04e5bfeff6cccfe396`) and the
coordinated `../research/probability-source-preflight.md` when available.
These preparation notes do not alter any frozen chapter requirement.

Start in an isolated development worktree from the committed Chapter 1 repair
`a14977b9e316cc484ffad8a470d26b15615956c0`, with its own project build directory.
That base is an unvalidated draft, not an accepted dependency. The existing
old-candidate check in `conaled-ch01-review` remains unchanged. Do not start
an additional compiler while that gate is running. Save new source as an
explicitly uncompiled draft and preserve it in a durability checkpoint.

The unit supplies ordinary analytic theorems over an existing measure and a
sequence of nonnegative observations. Reuse Mathlib's measure, lower integral,
infinite sum, geometric series and Markov inequality. Existing conaled
`Table`/kernel and `ProbabilityProgress.Execution` interfaces continue to supply
their established semantics; no new probability carrier, expectation operator,
random executor, filtration record or resource monad is justified here.
Uniform finite-ranking restriction is a separate queued combinatorial concern.

Suggested module: `Applications/Probability/AccumulatedWork.lean`, with
connected clients in `Examples/AccumulatedWork.lean`. Keep the core independent
of finite sampling, kernel construction and measured-program modules unless
its statements actually use them. Namespace and helper naming are routine
implementation choices, subject to the existing public layout.

## Required mathematical statements

Let `μ : Measure Ω`, with the ambient measurable space, and
`X : Nat → Ω → ℝ≥0∞`. Let `q,N : ℝ≥0∞`. Write
`E_t = ∫⁻ ω, X t ω ∂μ` and `W ω = ∑' t, X t ω` here only as explanatory
notation. Nonnegativity is intrinsic; no distribution normalization or finite
payload space is part of the generic analytic statement.

1. From `E_0 ≤ N` and `∀ t, E_(t+1) ≤ q*E_t`, derive
   `∀ t, E_t ≤ q^t*N`. This is a bound on actual supplied observations under
   the same law. It needs neither measurability nor strict contraction nor
   finiteness merely for this ordered-integral induction. Do not replace the
   one-step premise by the desired whole-run bound.
2. Under `∀ t, AEMeasurable (X t) μ`, derive for every natural `w`

   `∫⁻ ω, (∑' j, X (w+j) ω) ∂μ ≤ q^w*N/(1-q)`.

   Derive the total-work specialization at `w=0`. Use the existing countable
   sum/integral interchange and geometric sum. Extended nonnegative values
   retain infinite work honestly; no totalized real integral or `toReal`
   conversion may silently turn infinity into zero.
3. Under `q<1` and `N≠∞`, establish a finite total-work integral from that
   bound. Preserve the `N=0` and `q=0` cases. The general theorem must not
   acquire `0<q` simply to permit division by q. Finite accumulated work by
   itself is not a theorem that the execution has finitely many steps.
4. For a given natural `w`, assume the almost-everywhere prefix bound

   `∑ t∈range w, X t ω ≤ (w : ℝ≥0∞)*N`.

   With `N≠0`, `N≠∞`, and `q<1`, prove the non-strict tail statement

   `μ {ω | (w : ℝ≥0∞)*N + N/(1-q) ≤ W ω} ≤ q^w`.

   Derive the event inclusion from the actual prefix/remaining-sum
   decomposition. Prove positivity and finiteness of `N/(1-q)` and the
   finite-prefix cancellation hypotheses before using division-form Markov.
   For this theorem, the single-prefix premise is sufficient; do not force
   an unnecessary all-times bound. A useful derived specialization may accept
   `∀ t, X t ≤ᵐ[μ] (fun _ => N)` and discharge that prefix premise.

No independence, Markov property, global `Fintype`, `Countable` or `Inhabited`
assumption on Ω/payloads, finite-measure assumption, or probability-measure
instance belongs in a theorem that does not use it. An example's finite sample
space and normalization are local to that example. Almost-everywhere
measurability and inequalities must not be strengthened gratuitously to
everywhere measurability or inequalities.

The aggregate integral recurrence does not establish an algorithm's
conditional pivot or priority law. Later consumers must prove that law and
derive the recurrence under the same joint distribution, using the existing
kernel or conditional-expectation interfaces where appropriate. They must also
prove that the sum is their actual observed work. No theorem in this unit
certifies randomized quicksort, selection or treap complexity by itself.

## Connected cases and independently expected results

The independent arithmetic is recorded in
`../research/probability-work-calculations.json`. It is calculation evidence,
not kernel validation. Develop the cases alongside the theorem family and
retain their connections to its public results.

### Dependent finite stages and actual measured work

Use the standard uniform law on `Fin 8`. Four stages charge one unit always,
one on `ω.val<4`, one on `ω.val<2`, and one on `ω.val<1`; later charges are
zero. The means are `1,1/2,1/4,1/8`, so the integrated drift uses `q=1/2`
with initial/per-stage cap `N=1`.

Define an actual ordinary `Resources.bind` or `Resources.run` computation at
each environment, retain an independently specified returned value, and prove
that its measured cost is this accumulated work. Merely assigning the desired
sum as the cost of an unrelated extensional program is insufficient.

Prove the exact mean `15/8` and obtain its upper bound `2` through the generic
result. At `w=1`, work at least three occurs on exactly `ω.val<2`; prove its
mass `1/4`, then obtain the generic upper bound `1/2`. The event is nonempty.
The first two nonconstant active-stage events have intersection mass `1/4`,
while their marginal-product mass is `1/8`; retain this distinction to make
the shared environment explicit.

If an affine-cost composition is used, employ the existing measured
reweighting/sequencing interface and prove its actual observation. The
independent optional target `2*W+3` has mean `27/4≤7`, with mass `1/4` at
threshold nine. No additional generic expectation framework is needed for it.

### Consequential boundaries

- A one-stage deterministic computation with work three and no later work
  demonstrates `q=0`, finite total bound three, and the distinction between
  `w=0` (where `q^0=1`) and positive w.
- Zero observations satisfy the mean and total-work conclusions with `N=0`.
  On a probability space, the proposed non-strict tail with zero threshold,
  `q=1/2` and `w=1` instead has left side one and right side one-half.
  Retain a checked counterexample and the explicit positive-N tail hypothesis.
- The prefix hypothesis cannot be inferred from integrated drift. On the
  uniform law of `Fin 3`, take `X_0=3` at one outcome and zero at the other
  two; take all later observations zero. Then `N=1,q=0` satisfy the mean
  premises, but at `w=1` work at least two has mass `1/3>0=q^1`.
  Retain this checked boundary for the missing prefix premise.
- Explain the noncontracting boundary `q=1`: constant positive observations
  satisfy the one-step premise but need not have finite accumulated work.
  If this explanation introduces a new formal counterexample, include it in
  the normal build/audit and statement review; it is not a reason to strengthen
  the harmless general mean/extended-integral inequalities.

## Statement review, validation and completion

Review quantifier order, the common law μ, measure versus probability,
extended-real arithmetic, measurability, prefix/tail direction, threshold
positivity, zero/one contraction boundaries and actual observation bridges.
Preserve all meaningful existing probability/resource clients. Use only the
project's allowed axioms and the pinned toolchain; no admission, unsafe/partial
definition or proof-checking bypass is permitted.

Integrate the examples through the public root and provide a concise research
record explaining source use and the remaining chapter-specific obligations.
Capture an immutable candidate with these frozen requirements outside its
diff. Focused validation, the full applicable guarded candidate build and
exhaustive audit, both independent review axes and immediate final candidate
verification remain mandatory. A source preflight, uncompiled commit or
durability checkpoint supplies no acceptance credit. Integrate only after
the repaired Chapter 1 base and this shared unit have passed their gates.
