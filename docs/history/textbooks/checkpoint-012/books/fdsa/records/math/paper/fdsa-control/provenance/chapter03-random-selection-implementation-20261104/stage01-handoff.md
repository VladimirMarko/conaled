# Randomized selection: first source slice

Candidate `be1bf8de03554faea7beef0a25d01c40091d33b3`, based exactly on accepted
Chapter 2 `2da5708478a1d943a9214b5b386ec2db16cd9eca`. This is **uncompiled
source preparation**, not accepted coverage of Chapter 3 or its random algorithm.
Root owns every compiler, full audit and independent review gate.

## Intended mathematics and checked-use targets

The pinned July 27, 2026 book's printed page 35 was read directly from the local
PDF (`research-source/functional_data_structures_algorithms.pdf`, source digest
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`). The complete
83-row inventory and selection proof plan were read. This slice supports
C03-059–062, C03-073–074 and C03-077; none is marked complete merely by this slice.
The original probabilistic targets and all C03-059–080 obligations remain open.

`pivotRun` consumes `ListCalls.lookupRun` and eliminates its impossible failure
branch using the valid occurrence index. It introduces no default payload and
requires neither `Inhabited` nor value equality. Its cost is the actual index
plus one. `pivotLaw` pushes the accepted `RandomQuickSort.uniformIndex` through
that value. Its event formula counts occurrences; it does not sample distinct
payload values.

`stepRun` executes the input-length traversal, measured pivot lookup, accepted
single-pass `Partition.partitionRun`, the left-length traversal and, only when
the left test fails, the equal-length traversal. One source selection entry is
charged. Primitive arithmetic/comparisons and the abstract uniform choice add
no charge. The local formulas are `2*n+i+left+5` and
`2*n+i+left+equal+6`. All costs arise from the actual helper results.
The semantic action selects one child or returns the pivot directly. This does
not claim equal cost for the older two-pass partition operation.

The independent expected cases are: singleton rank zero returns 7 with cost 9;
rank one of `[0,0,1]` with occurrence index one returns 0 with cost 15; rank zero
of `[0,1,2,3,4]` with occurrence index one selects `[0]`, whereas the larger side
has size 3. Uniform occurrences of `[0,0,1]` induce value probabilities 2/3 and
1/3. The retained examples invoke the general source/semantic/event theorems;
they do not just recalculate detached arithmetic.

## Author statement review

The step semantic theorem uses zero-based `RankedAt`/sorted-index meaning. The
existing positive one-based public selector is unchanged. Child validity is an
implication from `k < xs.length`; strict decrease comes from actual sampled-pivot
membership. There is no `Nodup` premise. The equal-branch helper retains the
branch inequalities that make its bucket index valid. Its correctness is valid
even if an outer rank was not previously declared valid, because reaching that
middle branch itself establishes validity.

The 1-to-9 size cost estimate is local, input independent, and includes actual
lookup/length operations. It is not yet a pathwise resource theorem. The event
law needs no measurable payload space, and the count denominator is positive
because the sampler operates on a syntactically nonempty list. There is no
expectation, tail, native evaluation, elapsed-time or random-bit claim here.

`Statements19.lean` contains all 19 explicit public declarations (11 core,
8 examples) with the requested full pretty-printing options; its separate
manifest binds exact source and candidate identities. The private equal-bucket
helper remains part of source/audit review. Its omission from the public check
program does not remove it from the audit.

## Validation and next work

Only `git diff --cached --check` has run, with actual exit 0. No Lean/Lake,
dependency hydration, cache manipulation, full check or audit was performed by
this author. The recorded two-module focused check must establish elaboration.
Potential API/elaboration risks remain in dependent lookup, product/sum case
reduction, and finite-event simplification. The public entrypoint was not edited
concurrently; eventual integration requires `import Examples.RandomSelection`.

The next importing module constructs the actual well-founded finite PMF and
records each active size and sampled index, together with total source calls.
It will prove value correctness, at most n active calls, the triangular scan
bound and an actual source-cost bridge. Expected drift, residual-work tails,
endpoint-path probabilities and deterministic-policy claims remain later
required proofs over that same execution.
