# Stage04: actual selected-child drift and linear expected work

Candidate `eec2172f7296b6bfcd13533aadb68bd9d11c4a32`, tree `5825b981990e3b7d331d66abe3b9550c0ac4a7ff`, parent `bf6e86970ea873d8b890cdceedcfd262bbacbb80`.
Branch `work/fdsa-ch03-random-selection`; clean worktree.
Commit `feat(selection): bound actual random selection means (#174)`.
The new stage is **uncompiled**. Root alone owns compiler and full acceptance gates.

## Exact checked base preserved

The previous mean pair passed at the parent: owned session 25034, actual exit 0,
terminal `bcf60e`, complete root closure `978382`. The entire log and closure
were read in `64c842`, alongside checkpoint 0127's successful durability record.
The outer log has 5,671 bytes, SHA-256
`6c071e09164203cad30644ad49b394995f3f7c85b9d101cf8165a9953d94528f`.
All six prior source files, all 108 public targets and 13 authored private
helpers, all 97 prior author records, and all 14 passing-focus records remain
unchanged. Earlier failed attempts and their correction records are retained.
That focused pass does not validate this new stage or close a chapter gate.

## Additive proof route

`Applications/Resources/RandomSelectionDrift.lean` adds the following proposed
results, without changing the actual execution or its cost tariff:

1. The existing `RandomQuickSort.occurrenceRank id` permutation preserves strict
   value ordering and stable equal-value occurrence ordering. Its pushforward of
   the actual uniform occurrence sampler is uniform even with duplicates.
2. Injective refined-rank images of the actual strict partition occurrences
   lie in the lower/upper rank intervals. Their cardinalities are bounded by r
   and n-1-r. This proof uses standard Tuple.sort and Finset APIs, without Nodup.
3. `nextSize` observes the actual child selected by `stepRun`, or zero on its
   direct equal return. It is at most max(r,n-1-r). This maximum remains only
   a pointwise majorant, never the definition of a replacement execution.
4. `rankSideSum` sums those maxima. Endpoint/interior decomposition proves
   S(n+2)=S(n)+3*n+2, and natural two-step induction gives4*S(n)<=3*n*n.
   Finite uniform averaging yields actual conditional drift <=3*n/4.
5. Well-founded induction on the actual strict child, using the already checked
   `scanExpectation_cons`, gives E[W]<=4*n. The existing initial scan lower bound
   gives n<=E[W]. Existing finiteness justifies the real-mean transport.
6. The unchanged same-run W<=T<=9*W+2 bridge yields n<=E[T]<=36*n+2 in both
   lower-expectation and real-mean interfaces.

The rank sort is proof-only reindexing; no sorting operation is inserted into
selection or omitted from an execution cost. All rank parameters remain the
zero-based worker ranks. The stronger arbitrary-rank bounds retain the actual
invalid extension; one-based `select` and its free rank-zero boundary are intact.
No independence of successive sizes, input distribution, inhabited/finite
payload assumption, or desired complexity bound is supplied as a hypothesis.

## Cases and declaration inventory

The independently recorded expectations precede source creation in
`starting-state.json`. `Examples/RandomSelectionDrift.lean` connects them to
public results: rank-side values0,0,2,5,10,16; stable and uniform duplicate ranks;
all-rank singleton next size zero; actual next sizes1,1,0 on [0,0,1] at rank2,
with weighted expectation2/3 and general upper9/4; the preserved selected size1
versus majorant3 counterexample; generic/valid-answer expected bounds; and empty
means0 and2 matching the corresponding linear upper bounds.

There are two new source files and 450 inserted lines. New scope has 31 public
names (20 core,11 example) and two authored private helpers. Cumulative scope is
**139 public targets and15 authored private helpers across eight files**.
These are assignment inventory counts, not whole-project audit counts or
completed book-obligation counts. Full headers, every claim/case group and
connections to the retained execution are in `precommit-assessment.json`.
The private filter-count helper follows the accepted private quicksort-rank
pattern because that helper is not public; standard list/cardinality APIs are
otherwise reused. No accepted source, environment or dependency file changed.

## Root-only focused check and complete type input

```text
lake build Applications.Resources.RandomSelectionDrift Examples.RandomSelectionDrift
```

`Statements139-stage04.lean` retains all old 108 explicit-@ targets in exact order
and appends all 31 new public names, with full printing. It imports the original
step and mean examples and the new drift examples. Its SHA-256 is
`11642119a2fafb69c23bc1e16d41fe82a34cc8d0319d7256eb6717bcaba35084`. The preparation JSON binds it to this exact candidate/tree
and all eight source blobs. It is prepared only; no new type-output credit exists.

Complete new sources were read in `3c6bbc`. Precommit preservation and inventory
checks exited 0 in `d3d06a`. Staging, staged whitespace check and commit exited 0
in `5bd3bf`, with staged diff byte-identical to `source.diff`. The two
`git diff --no-index` exits1 are explicitly recorded as expected new-file
differences, not build failures. No author compiler or runtime action occurred.
Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

## Hold and remaining obligations

All eight sources and own provenance are held for root's actual focused terminal
or explicit release. No new acceptance, finding closure or independent-review
outcome is claimed. Root still owns full candidate/audit verification and both
review axes.

The exact natural-w >= tail, absorbing trace sizes, residual expectations,
positive-probability endpoint path1/n! and quadratic attainment, all-equal
behavior and remaining source transports still need proof. The tail retains
n>0 and the explicit n=0 countercase; changing >= to > is not a substitute.
C03-078/079/080 policy source ownership has moved to root/values, with no overlap
here. The original 83 Chapter3 obligations remain; inaccessible Karp1994 source
wording remains unverified and no quotations were invented.
