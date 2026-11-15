# Finite execution and probability continuation

Prepared 2026-11-04. Everything in `drafts/` remains **uncompiled**, with no
candidate, validation or review credit. The two tracked first-step files are
held at the separately recorded candidate. Root is the sole compiler owner.

## Preserved source drafts

`RandomSelectionRun-before-core-validation.lean` defines one well-founded
recursive PMF. Each active invocation binds the accepted uniform occurrence
sampler, executes `stepRun`, follows only its selected strict child, and records
the active size and sampled index. Its result combines the optional value,
that actual trace, and the accumulated source calls. The empty extension pays
one entry and one empty length call. `select` preserves the existing one-based
public boundary, with rank zero returning `none` directly.

Its intended theorems cover all supported outcomes: value agreement with
sorted indexing, correct failure/rank contracts, at most n active calls,
initial scan n, scan volume at most n(n+1)/2, valid recorded indices and sizes,
and `W ≤ T ≤ 9*W+2`. Both scalar work projections have bounded finite support.
The proofs depend only on the first-step facts and strict size decrease; no
expectation or almost-sure termination premise is assumed. Actual Lean
elaboration remains to be established, especially dependent pattern-match
equations and the two well-founded theorem proofs.

`RandomSelectionRun-examples-before-validation.lean` retains independently
chosen exact cases. A singleton returns after one active step with W=1,T=9.
On `[0,1]` at zero-based rank0, initial occurrence0 gives trace `[(2,0)]`, W=2,
T=11; occurrence1 gives `[(2,1),(1,0)]`, W=3,T=20. The value is0 in both cases.
The invalid singleton extension has T=11, including its reached empty call.
Examples invoke the generic value, scan and resource theorems; finite examples
do not discharge the later general probabilistic bounds.

## Duplicate-aware drift route

The accepted `RandomQuickSort.occurrenceRank id xs` uses `Tuple.sort` from
the exact pinned Mathlib source. The full 210-line `Data/Fin/Tuple/Sort.lean`
was read (`191765`). Its graph order is lexicographic in `(value,index)`, so
its existing permutation already resolves ties by original occurrence index.
No new tagged sorting algorithm or unaccepted XU draft is needed.

`Tuple.monotone_sort` implies: if occurrence j has strictly smaller value than
occurrence i, then its permuted rank is strictly smaller. Injectivity of the
permutation maps the lower-filter indices into `Finset.Iio (rank i)`, giving
lower length ≤ rank i; the upper-filter indices similarly map into `Ioi`, giving
upper length ≤ n-1-rank i. Mathlib's `Fin.card_Iio` and `Fin.card_Ioi` give the
exact cardinalities. The existing occurrence-rank module's local list-filter
to index-cardinality bridge is private; either reuse a suitable public standard
lemma or prove the small needed correspondence locally, without changing the
already accepted source merely for convenience. `Tuple.eq_sort_iff` provides
the stable equal-key index-order statement when that interface is needed.

For the finite arithmetic sum
`S(n) = sum (r in range n) max(r,n-1-r)`, remove the two endpoints and shift the
interior to prove `S(n+2)=S(n)+3*n+2`. Two-step induction from S(0)=S(1)=0
then proves `4*S(n)≤3*n*n`. This derives the bound from the actual finite sum;
it does not assign a desired recurrence to the selection cost. Permutation
reindexing of the uniform occurrence law gives the actual next-size drift,
including duplicates and immediate equal-block termination.

## Remaining execution proofs

The same-run expected scan bound is `n≤E[W]≤4n`. Define absorbing size X_j
from the j-th trace entry, with zero after termination, and residual work from
the dropped trace. Fresh conditional draws and the one-child run equation
give `E[X_j]≤(3/4)^j*n` and residual expectation ≤`4*(3/4)^j*n`. The recorded
per-entry size bound gives prefix work≤w*n. Markov at positive threshold4*n
then yields `Pr[W≥(4+w)*n]≤(3/4)^w` for natural w and n>0. Scalar PMF
projections supply the standard expectation/measure correspondence and
integrability. Successive sizes are dependent; no independence premise belongs
to these theorems. The resource bridge gives expected source work≤36*n+2 and
the corresponding threshold `9*(4+w)*n+2`, with the lower expectation n.

The distinct-input bad-endpoint proof must retain each sampled index in the
trace: choose minima while the requested rank is positive, then maxima, so
one non-target occurrence disappears each time until a singleton. The root
index distinguishes branches of the PMF sum, giving the specific trace mass
`1/n!`. An all-equal input instead stops after one partition. General minimum
pivot, outside-range nontermination and halving-pivot statements C03-078–080
remain required; they are not implied by the random-step examples.

All nineteen current public statement inputs and prior failed logs remain
preserved. The full Chapter3 inventory has83 IDs, including the separate
coordinate-query model C03-081–083, which belongs to the coordinator's wider
chapter assignment rather than this probability author scope.
