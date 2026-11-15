# FDSA Chapter 3: selection correspondence and resource models

This note maps all **83 Chapter 3 obligations, C03-001–083**, to conaled
source and connected examples. It includes the exercises, the chapter's
random-pivot assertions, and the explicit coordinate-query model needed for
its optimality comparison. The chapter's order organizes the correspondence;
Lean modules remain organized by selection, sequences, resources and probability.

**Source correspondence — 4 November 2026.** Named definitions and theorems
below refer to the immutable author sources listed next. Some of these sources
are awaiting assembly into the accepted branch. This document does not accept
the chapter, certify a combined candidate, or substitute source inspection for
actual elaborated-type inspection and the complete build/audit/review gates.

The universal random endpoint-path witness in C03-064 and its dependent
quadratic source-cost family in C03-075 remain **pending**. The new general
all-equal core has built, but its example module still has a failed focused
check at the recorded source. Those boundaries remain visible throughout the
map; finite examples and intended future declarations are not counted as the
missing universal results.

## Source identity and attribution

The source is the July 27, 2026 edition of
[Functional Data Structures and Algorithms: A Proof Assistant Approach](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
Chapter 3 printed pp. 31–44 (PDF pp. 37–50), with Appendix B.1–B.2 printed
pp. 347–348 for the auxiliary time functions. The inspected PDF SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The [official manuscript site](https://fdsa-book.net/) and its PDF URL are
mutable; the version and digest identify the inspected bytes. The companion
revision below is separately pinned and is not claimed to have generated that
PDF. The manuscript is a research input, not a repository source dependency.

The companion
[Selection.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Selection.thy)
is pinned at Isabelle mirror commit
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, file SHA-256
`c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8`.
It names Manuel Eberl, TU München, and imports `Complex_Main`,
`HOL-Library.Time_Functions` and `Sorting`. Its heading notes related AFP
Median-of-Medians work; that development is not substituted for this pinned
chapter theory. Isabelle's pinned `COPYRIGHT` supplies the BSD-3-Clause terms;
the source notice is retained below. These are proof/source references, not
Lean axioms or evidence of an Isabelle rebuild.

The cited Karp primary paper was inaccessible during the recorded research.
The project supplies an original elementary proof of the displayed scan tail
for a natural excess parameter. It does not claim verification of that
inaccessible paper's full theorem. The precise distribution, metric and
quantifiers are stated below.

## Immutable source and validation snapshot

The following identifiers name source slices, not independently accepted
Chapter 3 units. `Q` is the accepted Chapter 2 predecessor. The separately
accepted integration tip before Chapter 3 is shared XR
`c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5`. Prior acceptance and its native
fresh evidence remain valid; they do not validate new Chapter 3 sources.

| Source key | Scope | Immutable commit |
|---|---|---|
| `Q` | Accepted Chapter 2 prerequisites | `2da5708478a1d943a9214b5b386ec2db16cd9eca` |
| `V` | Rank, chunks, pivots, exercises and paid policies | `27281919b9edd31a53336cbb5583ebc17632247e` |
| `S` | Rounded/scalar/group recurrences, cutoff and outside pivots | `96c99a18a1f4ad28bbb8d13a17cbefb1899d8ab9` |
| `M` | Actual nested selection, measured helpers and generic bounds | `1249f39968a44a25bfe3932d84a2cb44c6a83515` |
| `C` | Symbolic rank/map/actual-cost composition | `660f974640fb89a766b26a4d786ae7ed197cecf2` |
| `R` | Random execution, expectation, drift and tail | `0b8006f150cdb1aa9c76f5cf80eededca4417e81` |
| `E` | General all-equal random execution under correction | `0fa60badfd353bcd6e22177d852d8d6399a2e0fe` |
| `I` | Coordinate sensitivity, queries and actual paid acquisition | `569545102ff70697066de429eb02f9f47dffa07f` |

The generic actual-bound pair at `M`, the composition example at `C`, and the
coordinate acquisition/optimality pair at `I` have successful focused checks.
For `E`, the core `Applications.Resources.RandomSelectionEqual` built, while
`Examples.RandomSelectionEqual` failed at five concrete normalization sites;
that pair has no successful terminal result in this snapshot. Earlier failures
and their exact corrections remain recorded. The older random execution,
expectation, drift and tail sources at `R`, and the value/exercise/policy slices
at `V`, retain their separately recorded focused evidence.

No complete Chapter 3 actual-type program, exhaustive candidate audit,
independent Standards/Spec acceptance, or immediate candidate verification is
claimed here. A previous XR verification record copied into a development
checkout is not Chapter 3 verification. Final assembly must select exact
sources and include every new example and private helper in the required
entry-point/audit closure.

## Occurrences, ranks and failure boundaries

For a finite list `xs`, write `n = xs.length`, `L(xs,a)` for the number of
occurrences strictly below `a`, and `G(xs,a)` for the number strictly above it.
`Applications.Selection.RankedAt xs k a` describes a permutation
`pre ++ a :: post`, with `pre.length = k`, prefix values at most `a`, and
suffix values at least `a`. The main count equivalence is

```text
RankedAt xs k a ↔ L(xs,a) ≤ k ∧ G(xs,a) < n−k.
```

The strict second inequality itself implies `k<n`; adding `Nodup` would lose
the required occurrence semantics. The result identifies the selected value,
not a unique occurrence among equal entries. A sublist/filter argument proves
the required multiset inclusion and complementary counts without discarding
multiplicities.

The book and the measured workers use zero-based `k`. Existing public
`selectWith` and `sortSelect` use one-based ranks, so the adapter is `k+1`.
Their public rank0 remains failure; it is not identified with the valid book
minimum rank. `Option` gives an explicit empty/out-of-bounds extension without
adding an arbitrary inhabitant to the payload type. The measured deterministic
worker checks validity using its actually observed entry length and returns
`none` at cost `n+2` for invalid ranks. The random worker and public random
wrapper have separately stated failure costs; value equivalence does not make
these extensions identical.

`ordered` is a specification witness for a sorted permutation, not the
resource implementation of every selector. Equal input multisets give equal
ordered lists and equal Option selections at every index. Cross-ordered
concatenation gives the expected left/right index split without assuming that
each input list is already sorted.

Partition semantics permit an arbitrary pivot. A valid index in the equal
block proves its indexed element equals the pivot, so direct middle return
needs no prior pivot-membership assumption. Termination is different: a pivot
in the input makes the equal block nonempty and both strict blocks shorter.
An outside-range pivot can preserve an entire strict block. The proof and
failure examples retain this distinction.

The lower median uses zero-based index `(n−1)/2`. On nonempty input its strict
lower and upper counts are bounded by `(n−1)/2` and `n/2` respectively, including
ties. Even central occurrences may have the same value. No global bottom,
top, finite payload universe or `Inhabited` assumption is introduced.

## Chunks and the mathematical pivot

The pure `Sequences.Chunks.chop` adapter reuses standard list splitting while
exposing the source equations: size0 returns `[]`; empty input returns `[]`;
positive size on nonempty input prepends `take d xs` to chopping `drop d xs`.
For `d>0`, every chunk is nonempty and has length at most `d`, chunk count is
`ceil(n/d)`, and flattening returns the complete input. Count sums, multiset
sums and the union of memberships therefore preserve every occurrence. The
aligned-append, full-block and replicate laws support the exercise family.

Chunk medians carry their nonempty witnesses. `medianOfMedians d xs` returns
an Option pivot and, for positive `d` and nonempty input, belongs to the
original list. This is the mathematical pivot specification. The fast worker
below obtains that value through nested recursion, rather than defining the
large-input pivot operation as a full sort of all chunk medians.

For either strict orientation, partition chunks by whether their own median
bears that relation to the final pivot. The complement is relative to that
chosen relation. The group multiset decomposition and the non-strict bound
`bad ≤ floor(m/2)` hold for `m=ceil(n/d)`, including repeated medians. Put
`q=floor(d/2)`. Each strict side of the original input satisfies

```text
side ≤ q*m + (d−q)*floor(m/2),       d>0.
```

The argument includes a short final chunk. At `d=5` it gives
`2*m+3*floor(m/2)` and the exact source ceiling `ceil(7*n/10+3)` for both sides.
Decimal source coefficients are exact rationals. Natural division is not
performed prematurely inside a real ceiling, and empty strict counts are
handled explicitly.

## Actual nested selection and the source tariff

The resource programs use the existing `Measured`, ordinary bind and call-count
operations. Their values come from the actual returned subcomputations; the
cost field is not an assigned complexity attached to an independently computed
answer. Primitive comparisons, arithmetic, constructor/projection operations
and proof arguments have the declared zero tariff unless a measured source
operation explicitly charges them. These are mathematical source calls, not
machine instructions, allocation, stack usage, elapsed time or random-bit cost.

The actual auxiliary contracts are:

| Operation | Observation and bound |
|---|---|
| One-pass `partitionRun p xs` | Exact `n+1` calls. This is distinct from the existing two-stage pure partition implementation. |
| `slowSelectRun k xs` | Actual insertion sort followed by actual lookup; valid rank cost at most `n²+3n+1`. |
| `slowMedianRun xs` | Actual length plus slow selection at `(n−1)/2`; nonempty cost at most `n²+4n+2`, hence at most47 for a chunk of size≤5. |
| `chopRun d xs` | Actual take and drop are both paid. For positive d, exact `2n+3ceil(n/d)+1`; for all d, at most `5n+1`. |
| `mapSlowMedianRun` | Sum of actual callback costs plus `m+1`; size-five chunks give at most `48m+1≤10n+48`. |
| `chunkMediansRun 5 xs` | The actual chop followed by the actual median map; at most `15n+49`. |

`Resources.Selection.selectRunWith` implements the nested algorithm for
group size `d≥2` and cutoff≥1. Its private dependent `selectWorker` returns a
payload carrying membership in its own input. The first recursive medians
list is shorter; the resulting pivot's membership gives strict decrease of
both later sides before the full correctness or cost theorem is invoked.
This avoids circular use of selection correctness to justify its own recursion.
Invalid ranks are rejected at entry; valid ranks remain valid in the selected
child. The book wrapper `selectRun` fixes size5 and cutoff20.

For a valid rank in the small branch, the exact cost is
`1 + lengthRun(xs).cost + slowSelectRun(k,xs).cost`. In the large branch, let
`medians` be the actual prepared list, `p` its recursively selected median,
and `(ls,es,gs)` the actual measured partition. With `C` denoting the actual
worker cost, define the already reached work

```text
common = 1 + Tlength(xs) + TchunkMedians(d,xs)
           + C((ceil(n/d)−1)/2, medians)
           + Tpartition(p,xs) + Tlength(ls).

C(k,xs) = common + C(k,ls)                              if k < length ls
        = common + Tlength(es)                        if k < length ls+length es
        = common + Tlength(es) + C(k−length ls−length es,gs) otherwise.
```

The left branch does not pay an equal-block length traversal; the equal branch
does not make a second recursive selection. Each actual recursive invocation
pays its own entry observation. Caching the current entry length avoids an
extra adapter traversal inside that invocation; it does not erase separate
source observations in parent and child calls.

At the cutoff, the simple bound `n²+4n+3` is at most483. The exact scalar majorant
is

```text
F n = 483,                                                   n≤20
F n = F(ceil(n/5)) + F(ceil(7*n/10+3)) + 19*n + 54,            n>20.
```

Its child descent, lower bound483 and monotonicity precede resizing actual
child costs. The actual local bound and pivot-size laws then prove
`selectRun(k,xs).cost≤F n`. The rounded recurrence proof uses contracting
coefficients `a,c>0`, `a+c<1`, arbitrary signed offsets `b,d`, nonnegative
linear toll and arbitrary signed constant toll. It handles natural-ceiling
zero truncation, constructs finite-prefix constants, and proves the full
real affine bound without assuming nonnegative values of the recurrence.
The natural-valued corollary follows from that real theorem.

Substitution `a=1/5,b=0,c=7/10,d=3,C1=19,C2=54` yields an affine bound on `F`,
then on actual book work. The constants precede payload types/orders, input
lists and ranks. `Examples.SelectionComposition` additionally combines the
rank certificate, a possibly noninjective monotone map and both actual cost
bounds. Its constant-map example changes the size21 last-rank work from266
to239 while preserving transported correctness; it makes no equal-cost claim.

## Exercises, cutoffs and general grouping

The minimum exercise uses an actual tail-recursive single-pass accumulator
with exact measured work `n+1`. The separate second-minimum loop is proved
equal to fixed rank one after proving the bounded sorted-prefix construction.
It preserves duplicate occurrences. The actual general fixed-rank worker
traverses the input once, with a sorted accumulator of width `k+1`; bounded
accumulator traversals are charged. Its explicit bound
`2*k*n+6*n+k+4` has constants independent of input and rank, including `k=0`.
Value equality with the specialized minimum does not equate their different
actual source costs.

The rank-to-median reduction finds the input extrema rather than assuming
bottom/top elements. For valid `k<n`, it pads with
`A=n−1−2*k` copies of the minimum and `B=2*k+1−n` copies of the maximum,
using natural truncated subtraction. The output is nonempty, odd, has length
at most `2n−1`, and its lower median is the original selected value. Both
extrema scans, the original length, replicas and concatenations are paid.
The exact valid cost is `4n+2A+B+8`, bounded by `6n+6`; the invalid-rank
counterexample prevents extending this bound beyond its stated domain.

Three cutoff statements have different roles:

| Cutoff | Precise meaning |
|---|---|
| Actual minimum1 | For every fixed `d≥2`, the guarded first pivot call decreases for all recursive inputs. At cutoff0 a valid singleton recurses to the same singleton; the analytical call relation is not well-founded. Invalid guards still stop. |
| Scalar minimum13 | `pivotSize n<n` iff `1<n`, and `sideSize n<n` iff `13<n`. Thus the displayed two-child upper recurrence decreases above a cutoff exactly when that cutoff is at least13. |
| Book cutoff20 | It satisfies scalar and actual descent and admits the displayed uniform base483. This evidence explains its mathematical convenience without asserting a uniquely established author motive. |

The grouping analysis proves, for positive `d`,

```text
1/d + (d+floor(d/2))/(2*d) < 1  ↔  d−floor(d/2)>2.
```

This holds for odd sizes at least5 and even sizes at least6. Sizes3 and4 give
coefficient1. The chosen actual algorithm is nevertheless correct and
terminating for every `d≥2` with cutoff≥1; failure of this particular sufficient
linear argument is not a lower-bound theorem about all grouping strategies.
Size1 has an actual self-recursive medians call at arbitrarily large lengths;
size0 belongs to the separate empty-chop convention, not this worker domain.

The sufficient-group actual bound uses the generic pivot size envelope,
measured local toll, a uniform finite-prefix bound and the monotone scalar
majorant. The prefix covers the maximum of actual and scalar cutoffs, including
both orderings of those cutoffs. Constants precede payloads and valid ranks,
so an infinite payload domain introduces no hidden finite-search premise.
The examples cover both odd and even sufficient groups and the first genuinely
recursive scalar budgets.

Exercise3.7 supplies an actual universal counterfamily. There are `i` blocks
`[0,0,0,1,1]`, `i+1` blocks `[1,1,1,1,1]`, then a final `[0]`. Its length is
`10i+6`, its actual size-five pivot is0, and it has `7i+5` entries greater than
the pivot. Thus `10*Ngt=7*n+8>7*n` at every natural index. Lengths strictly
increase and denominators are positive. This preserves the ceiling allowance
and disproves dropping it; a finite sample is not used in place of the family.

## Actual random execution, scan work and source work

`Resources.RandomSelection.run` performs a fresh uniform occurrence-index
choice at each nonempty conditional state, then partitions and follows only
the rank-selected strict side or stops in the equal block. It is a finite
well-founded PMF execution. Duplicates affect the index-to-value pushforward:
`[0,0,1]` chooses values0 and1 with masses2/3 and1/3. It is not uniform choice
among distinct values, and a fixed deterministic pivot policy is not this law.

The actual trace records each active length and chosen occurrence index.
`W` is the sum of the positive active lengths; `T` is the source-call
observation of that same execution. Termination gives at most `n` active
invocations and the uniform upper bound `W≤n(n+1)/2`. A supported two-element
path attains its triangular bound. **Still pending** is a specified path for
every distinct input and every valid target rank, exact mass `1/n!`, triangular
attainment, and an unbounded natural/integer family. No declaration for that
future universal result is assumed in this correspondence.

Stable occurrence ranks remain uniform even with ties. The actual next size is
bounded by `max(r,m−1−r)` and the exact finite average is at most `3m/4`.
For a fixed input and valid target, the proved expectation is
`n≤E[W]≤4n`. With absorbing zero after termination, for all natural `j,w`,

```text
E[X_j] ≤ (3/4)^j * n,
E[residual work after w steps] ≤ 4*(3/4)^w * n.
```

Successive active sizes are dependent. The proof uses the actual conditional
recurrence, not an independence assumption. The first `w` scans cost at most
`w*n`; the event `W≥(4+w)n` therefore forces residual work at least `4n`.
Nonnegativity, finite support/integrability and the actual residual-law bridge
justify Markov. For **n>0 and natural w**, the precise result is

```text
Pr[W ≥ (4+w)n] ≤ (3/4)^w.
```

The non-strict event and positive initial size matter: at `n=0` the threshold
is0 and the event has probability1. Exponential decay is in the excess
multiple `w`; fixing `w` gives a fixed probability bound, not an automatic
fixed-constant high-probability O(n) theorem as `n` grows. A logarithmic-excess
consequence is optional and does not replace the linear expectation.

The actual source bridge is `W≤T≤9W+2`. It charges occurrence retrieval,
partitioning, reached length observations and branch work; abstract uniform
sampling has no charged random-bit implementation. It yields

```text
n ≤ E[T] ≤ 36n+2,
Pr[T ≥ 9(4+w)n+2] ≤ (3/4)^w,       n>0, w:Nat.
```

A quadratic source upper bound is also present. Its universal lower/worst-case
family remains pending with C03-064. The larger-side probabilistic recurrence
is only a majorant: at size5, rank0 and pivot rank1, the actual next size is1
while that majorant is3.

The general all-equal core at `E` describes every valid supported outcome on
length `n>0`: one active invocation, trace `[(n,i)]`, value equal to the common
payload, `W=n`, and `T=3n+i+6`, where `0≤i<n`. Each indexed outcome has mass
`1/n`; identical payloads do not merge the distinct recorded indices/costs.
For invalid worker ranks the actual empty continuation adds2. The core also
states `scanLaw=pure n` and linear source bounds. This core built, but the
all-equal example pair remains failed at this snapshot; its general and
concrete cases must retain that qualification until their actual correction
passes. They delimit worst-case quantifiers rather than proving the missing
distinct-input worst family.

## Paid deterministic policies and coordinate optimality

The reusable measured policy executor observes actual pivot construction,
lengths, partition and reached branch work. With the actual single-pass
minimum constructor, distinct input and valid zero-based rank `k` give
`k+1` active invocations, `k` recursive edges and

```text
W = (k+1)n − k(k+1)/2,
T = 3W + 7(k+1) + 1.
```

Largest rank gives the triangular scan family and quadratic paid work; each
fixed rank is linear. Minimum rank0 stops after the first partition, and equal
inputs provide additional one-entry counterexamples to the unqualified
all-rank/all-input quadratic wording. Outside-range policies instead preserve
the selection state and fail at every finite fuel; they do not satisfy
`PivotValid`.

For a policy whose actual strict sides satisfy `2*child≤parent`, adequate-fuel
valid execution yields the `Halves` trace relation. It proves
`n≤W≤2n` and at most `ceil(log₂ n)` recursive edges, including early equal stops.
The generic actual tariff theorem consumes an actual uniform linear
pivot-construction bound. The concrete median policy pays its index-length
observation and the actual measured nested selector, then uses the median
value law for both side bounds. Its uniform paid linear result therefore does
not assume a free median. A singleton has one active invocation and zero
recursive edges; in this tariff its pivot construction costs10 and its full
policy execution costs19. These are distinct from the minimum-policy tariff.

The coordinate-query protocol makes the p.32 optimality comparison precise.
At fixed size and rank its next valid `Fin n` index or answer depends only on
the transcript of queried indices and returned values. It receives neither an
uncharged full-list argument nor input-dependent advice. Replay shows that
agreement on queried coordinates preserves a terminating transcript/output.
For every distinct integer input, changing any coordinate can change any
valid selected rank; the proof can derive a fresh replacement preserving
distinctness. A competitor correct on all length-n integer inputs must
therefore query every coordinate. Repeated queries count repeatedly.

The actual upper protocol `observedSelect` first executes the read-all protocol
and then runs measured selection on exactly the acquired answers. Its declared
work is `c*n + actual selection calls`, where `c` is the coordinate tariff.
Front-end transcript bookkeeping is outside this stated observation. The
successful value view supplies a total correct member of the competitor class;
its fallback value is not reached on a valid rank. Uniform upper/comparison
constants precede tariff, size, rank, input and competitor. With `c≥1`, the
actual upper work is bounded by a fixed multiple of every correct terminating
competitor's charged query work on a distinct input; totality supplies such
runs when needed. This is a coordinate-query/source-tariff comparison, not a
lower bound for free bulk primitives, randomized competitors or physical
runtime. The complete core/example pair at `I` has focused validation only.

## Declaration aliases

Each alias below is a reading aid for a source file, not a new Lean namespace.
For example, `Count.ranked_iff_count_bounds` means the declaration with that
spelling in `Applications/Selection/CountRank.lean`, whose namespace is
`Applications.Selection`. The listed source key resolves its immutable bytes.
Some explicitly cited helpers are private; those remain in full audit scope.

| Alias | Key | Source file | Namespace |
|---|---|---|---|
| `Rank` | `Q` | `Applications/Selection/Rank.lean` | `Applications.Selection` |
| `ThreeWay` | `Q` | `Applications/Selection/ThreeWay.lean` | `Applications.Selection` |
| `Partition` | `Q` | `Applications/Resources/Partition.lean` | `Resources.Partition` |
| `EPartition` | `Q` | `Examples/ThreeWayPartition.lean` | `ThreeWayPartitionExamples` |
| `Count` | `V` | `Applications/Selection/CountRank.lean` | `Applications.Selection` |
| `ECount` | `V` | `Examples/SelectionCountRank.lean` | `Examples.SelectionCountRank` |
| `Chunks` | `V` | `Applications/Sequences/Chunks.lean` | `Applications.Sequences.Chunks` |
| `EChunks` | `V` | `Examples/ListChunks.lean` | `Examples.ListChunks` |
| `Pivot` | `V` | `Applications/Selection/MedianOfMedians.lean` | `Applications.Selection` |
| `EPivot` | `V` | `Examples/MedianOfMedians.lean` | `Examples.MedianOfMedians` |
| `Fixed` | `V` | `Applications/Selection/FixedRank.lean` | `Applications.Selection.FixedRank` |
| `FixedCost` | `V` | `Applications/Resources/FixedRank.lean` | `Resources.FixedRank` |
| `EFixed` | `V` | `Examples/FixedRankSelection.lean` | `Examples.FixedRankSelection` |
| `Reduction` | `V` | `Applications/Selection/MedianReduction.lean` | `Applications.Selection.MedianReduction` |
| `ReductionCost` | `V` | `Applications/Resources/MedianReduction.lean` | `Resources.MedianReduction` |
| `EReduction` | `V` | `Examples/MedianReduction.lean` | `Examples.MedianReduction` |
| `Counter` | `V` | `Applications/Selection/MedianCounterfamily.lean` | `Applications.Selection.MedianCounterfamily` |
| `ECounter` | `V` | `Examples/MedianCounterfamily.lean` | `Examples.MedianCounterfamily` |
| `EGeneral` | `V` | `Examples/GeneralMedianBounds.lean` | `Examples.GeneralMedianBounds` |
| `Policy` | `V` | `Applications/Resources/SelectionPolicy.lean` | `Resources.SelectionPolicy` |
| `Minimum` | `V` | `Applications/Resources/MinimumPivot.lean` | `Resources.MinimumPivot` |
| `EMinimum` | `V` | `Examples/MinimumPivot.lean` | `Examples.MinimumPivot` |
| `Halving` | `V` | `Applications/Resources/HalvingSelection.lean` | `Resources.HalvingSelection` |
| `MedianPolicy` | `V` | `Applications/Resources/MedianPolicy.lean` | `Resources.MedianPolicy` |
| `EMedianPolicy` | `V` | `Examples/MedianPolicy.lean` | `Examples.MedianPolicy` |
| `Slow` | `M` | `Applications/Resources/SelectionAuxiliary.lean` | `Resources.SelectionAuxiliary` |
| `ESlow` | `M` | `Examples/SelectionAuxiliary.lean` | `Examples.SelectionAuxiliary` |
| `ChunkCost` | `M` | `Applications/Resources/Chunks.lean` | `Resources.Chunks` |
| `EChunkCost` | `M` | `Examples/ChunkCalls.lean` | `Examples.ChunkCalls` |
| `MediansCost` | `M` | `Applications/Resources/SelectionMedians.lean` | `Resources.SelectionMedians` |
| `EMediansCost` | `M` | `Examples/SelectionMedians.lean` | `Examples.SelectionMedians` |
| `Select` | `M` | `Applications/Resources/Selection.lean` | `Resources.Selection` |
| `ESelect` | `M` | `Examples/SelectionCosts.lean` | `Examples.SelectionCosts` |
| `Bounds` | `M` | `Applications/Resources/SelectionBounds.lean` | `Resources.Selection` |
| `EBounds` | `M` | `Examples/SelectionBounds.lean` | `Examples.SelectionBounds` |
| `GenericEnvelope` | `M` | `Applications/Resources/SelectionGenericEnvelope.lean` | `Resources.Selection` |
| `GenericBounds` | `M` | `Applications/Resources/SelectionGenericBounds.lean` | `Resources.Selection` |
| `EGenericBounds` | `M` | `Examples/SelectionGenericBounds.lean` | `Examples.SelectionGenericBounds` |
| `Rounded` | `S` | `Applications/Resources/RoundedRecurrence.lean` | `Resources.RoundedRecurrence` |
| `ERounded` | `S` | `Examples/RoundedRecurrence.lean` | `Examples.RoundedRecurrence` |
| `RoundedBounds` | `S` | `Applications/Resources/RoundedRecurrenceBounds.lean` | `Resources.RoundedRecurrence` |
| `ERoundedBounds` | `S` | `Examples/RoundedRecurrenceBounds.lean` | `Examples.RoundedRecurrenceBounds` |
| `F` | `S` | `Applications/Resources/SelectionRecurrence.lean` | `Resources.SelectionRecurrence` |
| `EF` | `S` | `Examples/SelectionRecurrence.lean` | `Examples.SelectionRecurrence` |
| `Groups` | `S` | `Applications/Resources/GroupSelectionRecurrence.lean` | `Resources.GroupSelectionRecurrence` |
| `EGroups` | `S` | `Examples/GroupSelectionRecurrence.lean` | `Examples.GroupSelectionRecurrence` |
| `Envelope` | `S` | `Applications/Resources/SelectionEnvelope.lean` | `Resources.SelectionEnvelope` |
| `Cutoff` | `S` | `Applications/Resources/SelectionCutoff.lean` | `Resources.SelectionCutoff` |
| `ECutoff` | `S` | `Examples/SelectionCutoff.lean` | `Examples.SelectionCutoff` |
| `Outside` | `S` | `Applications/Selection/OutsidePivot.lean` | `Applications.Selection.OutsidePivot` |
| `EOutside` | `S` | `Examples/OutsidePivot.lean` | `Examples.OutsidePivot` |
| `HalvingTrace` | `S` | `Applications/Resources/HalvingTrace.lean` | `Resources.HalvingTrace` |
| `Random` | `R` | `Applications/Resources/RandomSelection.lean` | `Resources.RandomSelection` |
| `ERandom` | `R` | `Examples/RandomSelection.lean` | `Examples.RandomSelection` |
| `RandomRun` | `R` | `Applications/Resources/RandomSelectionRun.lean` | `Resources.RandomSelection` |
| `ERandomRun` | `R` | `Examples/RandomSelectionRun.lean` | `Examples.RandomSelectionRun` |
| `RandomMean` | `R` | `Applications/Resources/RandomSelectionMean.lean` | `Resources.RandomSelection` |
| `ERandomMean` | `R` | `Examples/RandomSelectionMean.lean` | `Examples.RandomSelectionMean` |
| `Drift` | `R` | `Applications/Resources/RandomSelectionDrift.lean` | `Resources.RandomSelection` |
| `EDrift` | `R` | `Examples/RandomSelectionDrift.lean` | `Examples.RandomSelectionDrift` |
| `Tail` | `R` | `Applications/Resources/RandomSelectionTail.lean` | `Resources.RandomSelection` |
| `ETail` | `R` | `Examples/RandomSelectionTail.lean` | `Examples.RandomSelectionTail` |
| `Sensitivity` | `I` | `Applications/Selection/CoordinateSensitivity.lean` | `Applications.Selection.CoordinateSensitivity` |
| `ESensitivity` | `I` | `Examples/CoordinateSensitivity.lean` | `Examples.CoordinateSensitivity` |
| `Query` | `I` | `Applications/Selection/CoordinateQueries.lean` | `Applications.Selection.CoordinateQueries` |
| `EQuery` | `I` | `Examples/CoordinateQueries.lean` | `Examples.CoordinateQueries` |
| `ReadAll` | `I` | `Applications/Selection/CoordinateReadAll.lean` | `Applications.Selection.CoordinateQueries` |
| `EReadAll` | `I` | `Examples/CoordinateReadAll.lean` | `Examples.CoordinateReadAll` |
| `Coordinate` | `I` | `Applications/Selection/CoordinateSelection.lean` | `Applications.Selection.CoordinateSelection` |
| `ECoordinate` | `I` | `Examples/CoordinateSelection.lean` | `Examples.CoordinateSelection` |
| `Composition` | `C` | `Examples/SelectionComposition.lean` | `Examples.SelectionComposition` |
| `RandomEqual` | `E` | `Applications/Resources/RandomSelectionEqual.lean` | `Resources.RandomSelection` |
| `ERandomEqual` | `E` | `Examples/RandomSelectionEqual.lean` | `Examples.RandomSelectionEqual` |

## Complete obligation correspondence

All 83 frozen identifiers are retained. Each row names actual source and
connected cases; a name's presence is not an acceptance mark. The explicit
pending rows and the failed all-equal example-pair qualification must survive
assembly and review. The table records mathematical domains and source-model
limits rather than promoting a focused check to whole-chapter validation.


### Specification and elementary facts: pp. 31–32

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-001** — Duplicate-aware count characterization | `Count.ranked_iff_count_bounds`, `Count.RankedAt.count_bounds` | `ECount.duplicate_lower_rank`, `ECount.duplicate_upper_rank`, `ECount.duplicate_bounds`, `ECount.weak_upper_count_is_insufficient` | Exact Nlt≤k and Ngt<n−k, without Nodup; the strict upper count also rules out invalid ranks. |
| **C03-002** — Uniqueness of the selected value | `Count.count_bounds_unique`, `Rank.RankedAt.unique` | `ECount.duplicate_lower_rank`, `ECount.duplicate_upper_rank` | Uniqueness is of a value; tied occurrences can occupy different valid ranks. |
| **C03-003** — Strict/weak filter inclusion and complementary counts | `Count.filter_le_sublist_filter_lt`, `Count.count_le_add_count_gt` | `ECount.duplicate_bounds`, `ECount.weak_upper_count_is_insufficient` | The list-sublist fact implies the required submultiset statement and preserves multiplicity. |
| **C03-004** — Sorted-index selection and public rank bridge | `Rank.ranked_iff_index`, `Count.selectWith_succ_value`, `Count.selectWith_succ_some_iff_count_bounds` | `ECount.zero_book_rank_is_public_one`, `ECount.duplicate_public_selection`, `ECount.smallest_is_not_largest` | Book k is public k+1; existing public zero failure is unchanged. |
| **C03-005** — Sorted filter/take/drop bounds | `Count.sorted_filter_lt_sublist_take`, `Count.sorted_filter_gt_sublist_drop`, `Count.RankedAt.count_bounds` | `ECount.duplicate_bounds`, `ECount.invalid_count_bounds` | Helpers require a valid sorted index; duplicates are retained. |
| **C03-006** — Permutation determines the sorted list | `Count.ordered_eq_of_pairwise_perm`, `Count.ordered_eq_of_perm` | `ECount.ordered_blocks` | Equal multisets are represented by List.Perm, using the accepted sorting contract. |
| **C03-007** — Permutation determines every Option selection | `Count.ordered_getElem?_perm` | `ECount.ordered_blocks_invalid_index` | The Option equality holds at all indices, including out of bounds. |
| **C03-008** — Membership and rank-zero minimum | `Count.RankedAt.mem`, `Count.ordered_getElem?_mem`, `Count.ranked_zero_iff_min`, `Count.ordered_getElem?_zero_iff_min` | `EFixed.minimum_example`, `EFixed.minimum_duplicate`, `EFixed.minimum_empty` | The later actual single-pass implementation is separately mapped at C03-047. |

### Partition and divide-and-conquer semantics: pp. 34–36

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-009** — Sorting cross-ordered concatenations | `Count.ordered_append` | `ECount.ordered_blocks` | Only the cross-list order premise is needed; each input need not already be sorted. |
| **C03-010** — Selection from cross-ordered concatenations | `Count.ordered_getElem?_append` | `ECount.ordered_blocks`, `ECount.ordered_blocks_invalid_index` | The Option law retains failure behavior as well as the valid-index book cases. |
| **C03-011** — Three-way partition value contract | `ThreeWay.partition3_eq_filters`, `ThreeWay.partition3_perm`, `ThreeWay.partition_lengths`, `ThreeWay.partition_left_mem`, `ThreeWay.partition_equal_mem`, `ThreeWay.partition_right_mem` | `EPartition.mixed_run`, `EPartition.empty_run`, `EPartition.replicate_run` | Accepted prerequisite is reused; no extra Nodup or pivot-membership premise. |
| **C03-012** — Arbitrary-pivot selection dispatch | `Count.partition_equal_getElem?`, `Count.ordered_getElem?_partition`, `ThreeWay.dispatch_value` | `ECount.outside_pivot_equal_block`, `ECount.outside_pivot_value`, `ECount.equal_occurrence_branch` | A valid middle index yields some p without assuming p∈xs beforehand. |
| **C03-013** — Membership makes strict children smaller | `ThreeWay.partition_strict_sizes`, `ThreeWay.PivotValid`, `Outside.partition3_below`, `Outside.partition3_above` | `EOutside.below_dispatch_same_state`, `EOutside.above_dispatch_same_state`, `EOutside.below_policy_rejected` | Semantic dispatch with arbitrary pivots is distinguished from the termination contract. |
| **C03-014** — Lower median occurrence and duplicate-aware counts | `Count.lowerMedian_value`, `Count.lowerMedian_count_bounds`, `Count.lowerMedian_mem`, `Pivot.lowerMedianValue_count_bounds` | `ECount.duplicate_lower_median`, `EPivot.lower_even_value`, `EPivot.empty_pivot` | Uses index (n−1)/2; even central occurrences may have equal values. |

### Chunks and pivot balance: pp. 36–39

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-015** — Standard-compatible chop equations | `Chunks.chop`, `Chunks.chop_zero`, `Chunks.chop_nil`, `Chunks.chop_eq_cons` | `EChunks.zero_size_source_convention`, `EChunks.partial_final_chunk`, `EChunks.singleton_chunks` | The standard-library construction is bridged to the source take/drop recurrence, including d=0. |
| **C03-016** — Chop descent and empty-output boundary | `Chunks.drop_length_lt`, `Chunks.chop_eq_nil_iff`, `Chunks.chop_eq_cons` | `EChunks.zero_size_source_convention`, `EChunks.short_group_nonempty` | Positive d supplies strict remaining-length descent; empty output iff d=0 or xs=[]. |
| **C03-017** — Every produced chunk is nonempty and bounded | `Chunks.chop_mem_ne_nil`, `Chunks.length_mem_chop` | `EChunks.short_group_nonempty`, `EChunkCost.reached_chunks_are_valid` | Statements also apply vacuously to an empty original input. |
| **C03-018** — Exact ceiling chunk count | `Chunks.length_chop`, `Chunks.length_chop_eq_add_pred_div`, `Chunks.length_chop_le_iff` | `EChunks.partial_chunk_count`, `EChunks.repeated_five_blocks` | The positive-d count uses Nat.ceilDiv; no prior lossy natural division. |
| **C03-019** — Flattening, counts, multisets and membership | `Chunks.flatten_chop`, `Chunks.countP_chop`, `Chunks.sum_multiset_chop`, `Chunks.mem_chop_iff`, `Chunks.mem_of_mem_chop` | `EChunks.partial_chunks_flatten`, `EChunks.duplicate_counts`, `EChunks.duplicate_multiset` | Positive d recovers the complete list and therefore the required set union and multiset sum. |
| **C03-020** — Aligned append, full blocks and replication | `Chunks.chop_append`, `Chunks.chop_flatten`, `Chunks.chop_replicate_blocks`, `Chunks.chop_replicate` | `EChunks.aligned_append`, `EChunks.repeated_five_blocks`, `EChunks.repeated_occurrences` | These support the universal counterfamily, not a separate unrequired algorithm. |
| **C03-021** — Mathematical median-of-medians pivot | `Pivot.chunkMedians`, `Pivot.medianOfMedians`, `Pivot.medianOfMedians_mem`, `Pivot.medianOfMedians_pivot_valid` | `EPivot.two_full_chunk_medians`, `EPivot.two_full_chunk_pivot`, `EPivot.mathematical_policy_is_valid` | Proof-carrying nonempty chunk medians and Option pivot; distinct from the fast nested implementation. |
| **C03-022** — Both orientations of chunk-median grouping | `Pivot.chunkMedianGroups`, `Pivot.chunkMedianGroups_related_length` | `EPivot.greater_median_group_is_one`, `EPivot.complementary_group_is_one`, `EPivot.duplicate_groups` | The complement is relative to the selected relation; both strict orientations are supported. |
| **C03-023** — Chunk group multiset and cardinality decomposition | `Pivot.chunkMedianGroups_perm`, `Pivot.chunkMedianGroups_multiset`, `Pivot.chunkMedianGroups_lengths` | `EPivot.duplicate_groups_multiset`, `EChunks.duplicate_counts` | Multiplicity is preserved through grouping and the summed input counts. |
| **C03-024** — Correct weak half bound and strict-bound counterexample | `Pivot.medianOfMedians_median_counts` | `EPivot.strict_half_is_false`, `EPivot.corrected_non_strict_half` | Uses ≤floor(m/2); the source PDF strict claim is explicitly refuted. |
| **C03-025** — Good-chunk and arbitrary-chunk contributions | `Pivot.chunk_count_lt_of_median_ge`, `Pivot.chunk_count_gt_of_median_le`, `Pivot.medianOfMedians_count_bounds` | `EPivot.five_chunk_lower_contribution`, `EPivot.five_chunk_upper_contribution`, `EPivot.five_chunk_total_contribution` | Private sum_le_count_split/chunk_count_bound implement the actual two-group sum; they remain in audit scope. |
| **C03-026** — Exact size-five two-sided ceiling bound | `Pivot.size_five_count_arithmetic`, `Pivot.size_five_ceiling`, `Pivot.medianOfMedians_five_count_bounds`, `Pivot.medianOfMedians_five_ceil_bounds` | `EPivot.short_final_chunk_balance`, `EPivot.duplicate_strict_sides`, `EPivot.source_real_balance`, `EPivot.empty_strict_counts` | Both sides ≤ceil(7n/10+3), including ties and short final chunk; empty counts are handled explicitly. |

### Actual nested selector and Appendix B.2 calls

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-027** — Insertion-based slow selection and median values | `Slow.slowSelectRun`, `Slow.slowSelectRun_value`, `Slow.slowSelectRun_some_iff`, `Slow.slowSelectRun_public`, `Slow.slowMedianRun`, `Slow.slowMedianRun_value` | `ESlow.public_rank_bridge`, `ESlow.duplicate_occurrence_rank`, `ESlow.lower_even_median`, `ESlow.same_median_different_work` | Actual insertion execution is used; sorting value uniqueness does not substitute another sorter cost. |
| **C03-028** — Actual nested size-five/cutoff-twenty selection | `Select.selectRunWith`, `Select.selectRun`, `Select.selectRunWith_step`, `Select.selectRun_small`, `Select.selectRun_step` | `ESelect.cutoff_ascending`, `ESelect.cutoff_descending`, `ESelect.first_recursive_left`, `ESelect.first_recursive_equal`, `ESelect.first_recursive_right` | Private selectWorker executes one recursive median selection and at most one selected strict child; exact book specialization is 5/20. |
| **C03-029** — Correctness of the actual nested computation | `Select.selectRunWith_value`, `Select.selectRun_value`, `Select.selectRunWith_some_iff`, `Select.selectRunWith_public`, `Composition.monotone_ranked_costs` | `ESelect.one_based_public_bridge`, `ESelect.monotone_payload_selection`, `ESelect.collapsed_payload`, `Composition.constant_ranked_costs` | The total dependent well-founded construction combines source partial correctness and termination. The current symbolic consumer composes RankedAt, noninjective monotone transport and uniform bounds on both actual executions; its focused pass is development evidence only. |
| **C03-030** — Noncircular nested termination and total failure domain | `Select.selectWorker`, `Select.selectRunWith_exists`, `Select.selectRunWith_mem`, `Select.selectRunWith_none_iff`, `Select.selectRunWith_of_invalid`, `GenericEnvelope.chunkMediansRun_proper_size` | `ESelect.empty_arbitrary_rank`, `ESelect.singleton_invalid`, `ESelect.group_two_cutoff_one` | Private worker carries input membership before correctness/cost proofs; first child decreases for d≥2 and cutoff≥1, later children by pivot membership. Invalid entry guard returns none with n+2 cost. |
| **C03-031** — Actual one-pass partition and n+1 calls | `Partition.partitionRun`, `Partition.partitionRun_cons`, `Partition.partitionRun_value`, `Partition.partitionRun_cons_cost`, `Partition.partitionRun_cost` | `EPartition.mixed_run`, `EPartition.mixed_cost`, `EPartition.empty_run`, `EPartition.bind_returned_lower` | Accepted measured prerequisite; the recurrence is one pass rather than three independent filters. |
| **C03-032** — Slow selection exact cost and valid-index bound | `Slow.slowSelectRun_cost`, `Slow.slowSelectRun_cost_of_lt`, `Slow.slowSelectRun_cost_bound` | `ESlow.valid_selection_budget`, `ESlow.cutoff_sorted_last`, `ESlow.cutoff_descending_last`, `ESlow.singleton_invalid` | Actual insertion plus lookup; for k<n the bound is n²+3n+1. |
| **C03-033** — Slow median exact cost and small-chunk bound | `Slow.slowMedianRun_cost`, `Slow.slowMedianRun_cost_bound`, `Slow.slowMedianRun_small_bound` | `ESlow.ascending_five_median`, `ESlow.descending_five_median`, `ESlow.arbitrary_short_chunk`, `ESlow.median_value_and_budget` | Charges its length observation; nonempty bound n²+4n+2, hence 47 for size≤5. |
| **C03-034** — Measured chopping with both source traversals | `ChunkCost.chopRun`, `ChunkCost.chopRun_eq_cons`, `ChunkCost.chopRun_cost`, `ChunkCost.chopRun_cost_bound` | `EChunkCost.zero_size`, `EChunkCost.both_traversals_are_charged`, `EChunkCost.fused_first_step_is_not_source_count`, `EChunkCost.arbitrary_group_budget` | Positive-d exact cost 2n+3ceil(n/d)+1; all-d bound 5n+1. Take and drop are separately charged. |
| **C03-035** — Actual median-map callback sum and preparation bounds | `MediansCost.mapSlowMedianRun_cost`, `MediansCost.mapSlowMedianRun_small_bound`, `MediansCost.mapSlowMedianRun_chop_five_bound`, `MediansCost.chunkMediansRun_cost_split`, `MediansCost.chunkMediansRun_five_bound` | `EMediansCost.two_chunk_map`, `EMediansCost.short_final_chunk`, `EMediansCost.first_recursive_map_count`, `EMediansCost.book_map_budget`, `EMediansCost.book_preparation_budget` | Map cost is sum of actual callbacks plus m+1; ≤48m+1≤10n+48, and complete preparation≤15n+49. |
| **C03-036** — Exact branch-sensitive nested source equations | `Select.selectRunWith_small`, `Select.selectRunWith_step`, `Select.selectRunWith_cost_step`, `Select.selectRun_cost_step`, `MediansCost.chunkMediansRun_cost_split` | `ESelect.cutoff_ascending`, `ESelect.cutoff_descending`, `ESelect.first_recursive_left`, `ESelect.first_recursive_equal`, `ESelect.first_recursive_right`, `ESelect.all_equal_last` | Entry length is cached; left branch omits equal-length traversal and equal branch omits a second recursive call. Actual counts 83/273, 269/231/266 and 239 are distinct from scalar budgets. |
| **C03-037** — Exact monotone scalar F | `F.F`, `F.F_of_le_twenty`, `F.F_of_twenty_lt`, `F.base_le_F`, `F.F_monotone`, `F.pivotSize_lt_iff`, `F.sideSize_lt_iff`, `F.F_rounded` | `EF.scalar_cutoff_obstruction`, `EF.scalar_cutoff_fourteen`, `EF.F_twenty`, `EF.F_twenty_one`, `EF.resize_across_cutoff` | Base 483, cutoff20, toll19n+54; children ceil(n/5), ceil(7n/10+3), with strict descent and monotonicity proved before resizing. |
| **C03-038** — Actual book execution bounded by F | `Bounds.selectRun_pivot_size_bounds`, `Bounds.selectRun_local_cost_bound`, `Bounds.selectRun_cost_le_F_of_lt`, `Bounds.selectRun_cost_le_F` | `EBounds.cutoff_descending_budget`, `EBounds.first_left_budget`, `EBounds.first_equal_budget`, `EBounds.first_right_budget`, `EBounds.first_local_budget` | Actual recurrence induction combines measured auxiliaries, valid child ranks and F monotonicity; all-rank extension also handles the explicit invalid guard. |

### Rounded recurrence and linear bound: pp. 41–44

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-039** — Exact rounded real recurrence | `Rounded.recurrence_step_le`, `RoundedBounds.affine_bound_of_prefix`, `RoundedBounds.exists_affine_bound` | `ERounded.combined_signed_descent`, `ERoundedBounds.negative_constant_toll_affine_bound` | The two contraction coefficients are a and c; signed offsets b,d and signed C2 are retained. |
| **C03-040** — Ceiling descent with zero truncation | `Rounded.ceil_affine_lt_add_one`, `Rounded.ceil_affine_lt_of_threshold`, `Rounded.thresholds_of_combined_cutoff`, `Rounded.ceil_children_lt` | `ERounded.negative_argument_truncation`, `ERounded.signed_offset_descent`, `ERounded.combined_signed_descent` | Thresholds use max(0,b), max(0,d); zero-truncated natural ceiling is not replaced with untruncated real arithmetic. |
| **C03-041** — Nonstrict slope suffices; strict-choice error | `Rounded.slope_nonneg_and_margin`, `Rounded.sharp_affine_absorption` | `ERounded.strict_slope_choice_counterexample`, `ERounded.zero_recurrence_bound_step`, `ERoundedBounds.zero_source_witness_bound` | C3≥C1/(1−a−c) is sufficient; the source maximum may attain equality. |
| **C03-042** — Explicit constants and full strong induction | `Rounded.cutoff_denominator_pos`, `RoundedBounds.explicit_cutoff_bounds`, `RoundedBounds.affine_bound_of_prefix`, `RoundedBounds.bound_with_source_constants` | `ERoundedBounds.negative_intercept_all_inputs`, `ERoundedBounds.roundedQuarter_sharp_affine_bound` | Finite-prefix maximum, positive denominator, nonnegative slope and all natural inputs are connected in the proof. |
| **C03-043** — General real-valued affine existence | `RoundedBounds.exists_affine_bound` | `ERoundedBounds.negative_constant_toll_affine_bound`, `ERoundedBounds.roundedQuarter_real_affine_bound`, `ERoundedBounds.noncontracting_affine_step_impossible` | No f≥0 or C2≥0 hypothesis; only the sufficient theorem is claimed, not an unsupported converse. |
| **C03-044** — Natural-valued corollary from the real theorem | `RoundedBounds.exists_affine_bound_nat` | `ERoundedBounds.roundedQuarter_nat_affine_bound` | Casts and nonnegative ceilings produce natural constants without duplicating the real induction. |
| **C03-045** — Exact F specialization and affine growth | `F.pivotSize_eq_ceil`, `F.sideSize_eq_ceil`, `F.F_rounded`, `F.exists_affine_bound`, `F.F_isBigO` | `EGroups.exact_book_F_specialization`, `EF.zero_requires_intercept` | Uses a=1/5,c=7/10,b=0,d=3,C1=19,C2=54,n0=20. |
| **C03-046** — Uniform actual book source cost | `Bounds.selectRun_exists_uniform_affine_bound`, `Bounds.selectRun_exists_uniform_linear_bound`, `Bounds.selectRun_family_isBigO`, `Composition.monotone_ranked_costs` | `EBounds.duplicate_family_uniform`, `EBounds.descending_family_linear`, `Composition.collapsed_actual_work` | Constants precede payload types/orders, input and rank; positive length is needed only when absorbing the intercept. The noninjective composition client bounds both actual costs without equating them. C03-083 separately connects paid acquisition to coordinate-query competitors. |

### Exercises 3.1–3.8

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-047** — Actual one-pass minimum and its paid execution | `Fixed.minimumLoop`, `Fixed.select0`, `Fixed.select0_spec`, `Fixed.select0_value`, `FixedCost.minimumLoopRun`, `FixedCost.select0Run_cost`, `FixedCost.select0Run_exact` | `EFixed.minimum_example`, `EFixed.minimum_duplicate`, `EFixed.minimum_execution`, `EFixed.minimum_and_fixed_costs_differ` | Tail-recursive minimum has exact n+1 calls. Its value equality with general fixed-rank selection is not used to pretend equal costs. |
| **C03-048** — Actual one-pass second minimum with duplicates | `Fixed.secondLoop`, `Fixed.select1`, `Fixed.select1_some_iff_ranked`, `Fixed.select1_none_iff`, `Fixed.select1_spec` | `EFixed.second_duplicate`, `EFixed.second_distinct`, `EFixed.second_singleton`, `EFixed.second_exists` | Correctness is derived after the actual loop correspondence to fixed rank one; the second occurrence may equal the minimum. |
| **C03-049** — Actual bounded-prefix streaming fixed-rank selection | `Fixed.boundedInsert`, `Fixed.prefixLoop`, `Fixed.takeSort_value`, `Fixed.selectFixed_value`, `FixedCost.boundedInsertRun_cost_le`, `FixedCost.prefixLoopRun_cost_le` | `EFixed.duplicate_prefix`, `EFixed.zero_width_prefix`, `EFixed.prefix_with_history`, `EFixed.bounded_step_for_rank` | One traversal of the input, with bounded sorted accumulator width k+1 and per-step source cost linear in that width. |
| **C03-050** — Second-minimum loop equals fixed rank one | `Fixed.boundedInsert_two`, `Fixed.prefixLoop_two`, `Fixed.select1_eq_selectFixed` | `EFixed.two_loop_correspondence`, `EFixed.second_duplicate` | An actual algorithm/loop equality, not only common extensional correctness. |
| **C03-051** — Uniform fixed-rank source cost including k=0 | `FixedCost.selectFixedRun`, `FixedCost.selectFixedRun_cost_le`, `FixedCost.selectFixedRun_uniform_bound` | `EFixed.fixed_zero_execution`, `EFixed.fixed_zero_bound`, `EFixed.fixed_second_execution`, `EFixed.uniform_constants_include_minimum` | Explicit 2kn+6n+k+4 witnesses precede all inputs/ranks; the n-term remains at k=0. |
| **C03-052** — Every coordinate can affect every valid rank | `Sensitivity.ordered_index_injective`, `Sensitivity.exists_fresh_set_changes`, `Sensitivity.exists_set_changes`, `Sensitivity.exists_update_changes` | `ESensitivity.every_triple_coordinate`, `ESensitivity.triple_fresh_witness`, `ESensitivity.singleton_sensitive`, `ESensitivity.invalid_ranks_agree` | Int, distinct original input, valid k and i; a fresh replacement is derived and preserves distinctness, not assumed. Query lower bound is separate. |
| **C03-053** — Actual extrema-padding rank-to-median reduction | `Reduction.extrema`, `Reduction.extrema_spec`, `Reduction.reduceToMedian`, `Reduction.reduceToMedian_nonempty`, `Reduction.reduceToMedian_rank_shift`, `Reduction.reduceToMedian_value`, `Reduction.reduceToMedian_spec` | `EReduction.tied_padding_rank`, `EReduction.first_padding`, `EReduction.last_padding`, `EReduction.lower_middle_padding`, `EReduction.upper_middle_padding`, `EReduction.empty_median_failure` | No global extrema assumptions: actual input min/max. Valid output is odd, nonempty, length≤2n−1; duplicates and even original lengths are covered. |
| **C03-054** — Paid reduction including extrema and all construction | `ReductionCost.extremaRun_cost`, `ReductionCost.padExtremaRun_cost`, `ReductionCost.reduceToMedianRun_cost`, `ReductionCost.reduceToMedianRun_cost_le`, `ReductionCost.reduceToMedianRun_uniform_bound` | `EReduction.extrema_execution`, `EReduction.first_execution`, `EReduction.last_execution`, `EReduction.first_rank_attains_bound`, `EReduction.invalid_rank_cost_exceeds_valid_bound` | Charges both extrema scans, length, replicas and append: exact 4n+2A+B+8; valid-rank bound 6n+6. Invalid-rank countercase protects the domain. |
| **C03-055** — Least actual cutoff versus scalar cutoff | `Cutoff.FirstPivotCall`, `Cutoff.actual_cutoff_iff`, `Cutoff.zero_cutoff_self_call`, `Cutoff.zero_cutoff_not_wellFounded`, `Cutoff.recursive_children_decrease`, `Cutoff.scalar_cutoff_iff`, `Cutoff.twenty_actual_base_budget` | `ECutoff.singleton_guarded_self_call`, `ECutoff.singleton_positive_cutoff_stops`, `ECutoff.two_group_actual_children`, `ECutoff.twelve_fails_scalar`, `ECutoff.thirteen_suffices_scalar`, `ECutoff.descending_twenty_actual_budget` | Actual minimum cutoff1 for d≥2; scalar minimum13; cutoff20 accommodates scalar descent and 483 base. The analytical self-call relation is connected to actual guarded preparation, including invalid guard. No unique author motive is asserted. |
| **C03-056** — Universal growing family exceeding seventy percent | `Counter.family`, `Counter.family_lengths_strictMono`, `Counter.chop_family`, `Counter.chunkMedians_family`, `Counter.family_pivot`, `Counter.family_excess`, `Counter.infinite_family` | `ECounter.first_chops`, `ECounter.first_pivot`, `ECounter.second_has_duplicates`, `ECounter.growth_at_every_index`, `ECounter.positive_denominator_at_every_index`, `ECounter.dropping_allowance_fails` | All i: n=10i+6>0, actual pivot0, Ngt=7i+5, so 10Ngt=7n+8. This is an infinite strict family, not finite experimentation. |
| **C03-057** — General-group two-sided pivot bound | `Pivot.medianOfMedians_count_bounds`, `EGeneral.partition_bounds`, `EGeneral.nonempty_input_has_bounded_pivot` | `EGeneral.three_group_bounds`, `EGeneral.four_group_bounds`, `EGeneral.six_group_bounds`, `EGeneral.odd_partition_bounds`, `EGeneral.even_partition_bounds`, `EGeneral.integer_tie_bound` | For every d>0, q=floor(d/2), m=ceil(n/d), bound q*m+(d−q)*floor(m/2), including duplicates and short final chunk; connects to actual partition sizes. |
| **C03-058** — General groups: correctness, termination and sufficient linear costs | `Groups.fraction_sum_eq`, `Groups.contracts_iff_half_gap`, `Groups.contracts_iff_five_le`, `Groups.odd_contracts_iff`, `Groups.even_contracts_iff`, `Groups.majorant_affine_bound`, `Cutoff.group_one_not_wellFounded`, `Select.selectRunWith_value`, `GenericEnvelope.selectRunWith_uniform_prefix_bound`, `GenericBounds.selectRunWith_cost_le_groupMajorant`, `GenericBounds.selectRunWith_exists_uniform_affine_bound`, `GenericBounds.selectRunWith_family_isBigO` | `EGroups.groups_three_four`, `EGroups.groups_five_six`, `EGroups.all_odd_even_thresholds`, `EGenericBounds.book_recurses_inside_scalar_prefix`, `EGenericBounds.actual_cutoff_above_scalar`, `EGenericBounds.six_duplicate_integer_family` | Actual correctness and termination hold for d≥2 and cutoff≥1; d=1 has an actual self-call obstruction. For positive d the crude fraction contracts iff d−floor(d/2)>2 (odd≥5/even≥6), while d=3,4 gives1. The sufficient-group cost uses a uniform finite prefix covering both cutoffs, with constants before payloads and ranks. The generic core/example pair at M has a focused pass; complete chapter gates remain. |

### Random-pivot claims, actual expectations and tail

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-059** — Actual fresh uniform-occurrence random recursion | `Random.pivotRun`, `Random.stepRun`, `Random.pivotLaw`, `RandomRun.run`, `RandomRun.run_cons` | `ERandom.singleton_step`, `ERandom.duplicate_middle`, `ERandomRun.two_key_execution` | Each nonempty state uses a new finite uniform occurrence choice in PMF bind and follows only the rank-selected child. This is not one fixed deterministic policy. |
| **C03-060** — Duplicate-aware uniform value pushforward | `Random.pivotLaw`, `Random.pivotLaw_event`, `Random.pivotLaw_support` | `ERandom.duplicate_zero_probability`, `ERandom.duplicate_one_probability` | [0,0,1] has value masses 2/3 and1/3; uniform distinct-value choice is not substituted. |
| **C03-061** — Random termination, child validity and correct result | `Random.stepRun_child`, `Random.stepRun_ranked`, `RandomRun.run_value`, `RandomRun.run_ranked`, `RandomRun.run_valid`, `RandomRun.run_active_calls_le`, `RandomRun.select_some_iff` | `ERandom.selected_side_valid`, `ERandomRun.arbitrary_supported_rank`, `ERandomRun.rank_zero_public_failure` | Actual supported outcomes terminate within n active calls. Valid-rank correctness and public one-based bridge preserve explicit failure behavior. |
| **C03-062** — Actual trace scan-volume observation | `RandomRun.Trace`, `RandomRun.scanVolume`, `RandomRun.prepend`, `RandomRun.run_cons`, `Tail.scanVolume_eq_sum_activeSize` | `ERandomRun.same_value_different_scan`, `ETail.finite_trace_decomposition`, `ETail.actual_pair_trace_observations` | Each active positive length is observed; only the reached child is added, with absorbed zero after termination. |
| **C03-063** — Every path has triangular scan upper bound | `RandomRun.run_scanVolume_le`, `RandomRun.run_active_calls_le` | `ERandomRun.maximum_scan_on_pair`, `ERandomRun.bounded_actual_pair_calls` | Uniform bound n(n+1)/2 holds with duplicates and all ranks; it is separate from attainment. |
| **C03-064** — Universal bad-endpoint path and exact factorial mass | `RandomRun.run_scanVolume_le` | `ERandomRun.two_key_long_path`, `ERandomRun.maximum_scan_on_pair` | PENDING universal result. Present source proves the upper bound and an actual supported triangular path for n=2. Still required: every distinct input and every valid target rank, a specified endpoint sequence retaining the target until singleton, exact probability1/n!, triangular attainment, and an unbounded Nat/Int family. No future theorem name is assigned. |
| **C03-065** — Correct worst-case quantifiers and all-equal stopping | `RandomEqual.run_all_equal`, `RandomEqual.run_all_equal_summary`, `RandomEqual.run_all_equal_absorbed`, `RandomEqual.run_replicate_scan_lt_quadratic`, `Minimum.run_zero_rank` | `ERandomEqual.pair_both_valid_ranks`, `ERandomEqual.general_equal_execution`, `ERandomEqual.equal_family_below_quadratic`, `EMinimum.minimum_is_not_four_calls`, `EMinimum.duplicates_are_not_four_calls` | The current general all-equal core E built: every valid outcome has one active invocation, W=n and actual cost between3n+6 and4n+5. Its two-module check still failed at five example normalization sites, so the pair remains under correction. The paid minimum-rank-zero counterexample is already available. Neither family is a universal quadratic input claim. |
| **C03-066** — Stable occurrence-rank coupling and actual child dominance | `Drift.occurrenceRank_uniform`, `Drift.occurrenceRank_tie`, `Drift.strict_side_rank_bounds`, `Drift.nextSize_le_rankSide` | `EDrift.stable_duplicate_positions`, `EDrift.refined_duplicate_uniform`, `EDrift.duplicate_next_choices` | No global Nodup assumption. A stable rank distinguishes tied occurrences and the actual selected strict side is bounded by max(r,m−1−r). |
| **C03-067** — Exact three-quarter conditional drift | `Drift.rankSideSum_add_two`, `Drift.rankSideSum_bound`, `Drift.rankSideSum_mean_le`, `Drift.nextSize_drift` | `EDrift.rank_side_small_values`, `EDrift.singleton_next_size`, `EDrift.duplicate_next_expectation`, `EDrift.duplicate_drift_bound` | Finite rank sum and actual next-size expectation; singleton/parity are retained, without asserting independence between later sizes. |
| **C03-068** — Uniform expected scan work | `RandomMean.scanExpectation_cons`, `Drift.scanExpectation_linear_bounds`, `Drift.scanMean_linear_bounds` | `EDrift.arbitrary_expected_bounds`, `EDrift.valid_selection_expected_bounds`, `ERandomMean.actual_mean_bridge` | n≤E W≤4n for fixed input/rank; real and nonnegative-integral forms are connected and finite. Constants are independent of an input distribution. |
| **C03-069** — Absorbing active sizes and geometric expectation | `Tail.run_activeSize_zero`, `Tail.run_activeSize_eq_zero_iff`, `Tail.run_activeSize_zero_persists`, `Tail.run_activeSize_absorbed`, `Tail.sizeExpectation_geometric_le` | `ETail.singleton_absorption`, `ETail.invalid_singleton_absorption`, `ETail.two_key_size_expectations`, `ETail.arbitrary_absorption` | E X_j≤(3/4)^j n for all natural j, using the actual dependent recursion and zero after termination. |
| **C03-070** — Expected residual scan work | `Tail.residualExpectation_succ_cons`, `Tail.residualExpectation_geometric_le` | `ETail.two_key_residual_expectations`, `ETail.duplicate_after_first` | E residual after w steps≤4(3/4)^w n; actual state/trace conditioning is preserved. |
| **C03-071** — Exact non-strict scan tail with positive input size | `Tail.scanLaw_tail`, `Tail.scanLaw_empty_tail_bound_fails` | `ETail.positive_input_tails`, `ETail.zero_excess_tail`, `ETail.empty_tail_countercase` | For natural w and n>0, Pr[W≥(4+w)n]≤(3/4)^w. This is an original elementary proof of the displayed law, not verification of the inaccessible Karp paper. |
| **C03-072** — Actual prefix/residual decomposition and Markov premises | `Tail.scanVolume_take_add_residualWork`, `Tail.run_prefix_scan_le`, `Tail.run_tail_residual`, `Tail.residualLaw_integrable`, `Tail.residualLaw_markov` | `ETail.finite_trace_decomposition`, `ETail.arbitrary_residual_integrability`, `ETail.actual_pair_trace_observations` | First w scans≤wn; the tail event forces residual≥4n; nonnegativity and integrability belong to the actual residual law. |
| **C03-073** — Larger-side recurrence is only a majorant | `Drift.nextSize_le_rankSide`, `RandomMean.scanExpectation_cons` | `ERandom.selected_side_is_not_larger_side`, `EDrift.selected_branch_is_smaller` | Concrete n=5,k=0,pivot rank1 has actual next size1 versus upper majorant3; no equality is substituted. |
| **C03-074** — Pathwise source-cost/scan bridge | `Random.stepRun_cost_bounds`, `RandomRun.run_source_bridge` | `ERandom.duplicate_source_bound`, `ERandomMean.actual_mean_bridge` | W≤T≤9W+2 charges pivot retrieval, partition, length observations and reached branch work. Uniform sampling is abstract; no random-bit or physical-runtime claim. |
| **C03-075** — Actual expected/tail bounds and worst-case transfer | `Drift.sourceExpectation_linear_bounds`, `Drift.sourceMean_linear_bounds`, `Tail.sourceLaw_tail`, `RandomRun.run_source_quadratic` | `EDrift.valid_selection_expected_bounds`, `ETail.valid_answer_and_tails`, `ERandomRun.two_key_long_path` | Expected n≤E T≤36n+2, source tail threshold9(4+w)n+2 and uniform quadratic upper are present. PENDING: the general quadratic lower/worst-case family transported from the universal C03-064 path. All-equal core E has a contrasting linear family, not that missing distinct-input witness. |
| **C03-076** — Tail quantifiers and interpretation | `Tail.scanLaw_tail`, `Tail.sourceLaw_tail` | `ETail.zero_excess_tail`, `ETail.positive_input_tails`, `ETail.empty_tail_countercase` | Statement analysis: exponential decay is in the excess multiple w. Fixed w gives a fixed probability bound, not an automatic fixed-constant high-probability O(n) theorem as n grows. Optional logarithmic excess is not required. |
| **C03-077** — Connected random examples and positive finite worst path | `RandomRun.run_value`, `RandomRun.run_trace_entries` | `ERandomRun.singleton_execution`, `ERandomRun.duplicate_execution`, `ERandomRun.two_key_first_path`, `ERandomRun.two_key_long_path`, `ERandomRun.same_value_different_scan`, `ERandomRun.maximum_scan_on_pair`, `ERandomEqual.three_equal_first_atom`, `ERandomEqual.three_equal_last_atom` | Focused-passed earlier cases include singleton, duplicate equal block, valid rank0, endpoint-rank cases, different supported traces with the same result and a positive-probability triangular path on a pair. Additional all-equal atom/source cases belong to E and retain its failed-pair qualification. Finite cases do not discharge C03-064. |

### Deterministic pivot-policy claims

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-078** — Actual paid minimum-pivot path and corrected rank dependence | `Policy.runWith`, `Minimum.run`, `Minimum.active_calls`, `Minimum.recursive_edges`, `Minimum.scan_exact`, `Minimum.cost_exact`, `Minimum.fixed_rank_linear`, `Minimum.largest_cost_quadratic` | `EMinimum.middle_execution`, `EMinimum.minimum_is_not_four_calls`, `EMinimum.duplicate_execution`, `EMinimum.singleton_edges`, `EMinimum.range_worst_quadratic`, `EMinimum.fixed_third_linear` | Distinct valid input: k+1 active calls, k edges, W=(k+1)n−k(k+1)/2 and T=3W+7(k+1)+1. Actual pivot construction is paid. Largest rank is quadratic; each fixed rank is linear; duplicate countercase prevents overgeneralization. |
| **C03-079** — Outside-range pivot self-state and fuel obstruction | `Outside.dispatch_below`, `Outside.dispatch_above`, `Outside.runWith_step_below`, `Outside.runWith_step_above`, `Outside.runWith_below_none`, `Outside.runWith_above_none`, `Outside.not_pivotValid_below`, `Outside.not_pivotValid_above` | `EOutside.below_dispatch_same_state`, `EOutside.above_dispatch_same_state`, `EOutside.singleton_never_answers`, `EOutside.below_valid_answer_not_obtained`, `EOutside.above_valid_answer_not_obtained` | For nonempty valid ranks, all finite fuels fail while the reached strict child preserves the state; an equivalent iteration obstruction is established without pretending the invalid policy satisfies PivotValid. |
| **C03-080** — Actual paid halving policy, logarithmic edges and linear work | `Halving.runWith_trace`, `Halving.runWith_scan_bounds`, `Halving.runWith_edges_clog`, `Halving.runWith_tariff`, `Halving.runWith_linear_cost`, `MedianPolicy.pivotRun`, `MedianPolicy.pivot_halving`, `MedianPolicy.pivotRun_exists_uniform_linear_bound`, `MedianPolicy.run_exists_uniform_linear_bound` | `EMedianPolicy.eight_execution`, `EMedianPolicy.eight_edges_bound`, `EMedianPolicy.seven_edges_strict_clog`, `EMedianPolicy.early_equal_execution`, `EMedianPolicy.duplicate_trace_connected`, `EMedianPolicy.singleton_active_and_edges`, `EMedianPolicy.all_integer_inputs_linear` | Actual adequate-fuel execution yields Halves; n≤W≤2n and edges≤ceil(log2 n). Concrete median policy measures its index-length observation and actual selectRun; constants precede all payloads/inputs/ranks. Singleton is one entry/zero edges, pivot cost10 and execution19. |

### Coordinate-query optimality bridge

| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |
|---|---|---|---|
| **C03-081** — Adaptive coordinate-query protocol and replay | `Query.Protocol`, `Query.Runs`, `Query.Total`, `Query.Selects`, `Query.Runs.answers`, `Query.Runs.replay`, `Query.Runs.replay_update_of_not_mem`, `Query.Runs.deterministic` | `EQuery.repeatNegative_negative_run`, `EQuery.repeatNegative_nonnegative_run`, `EQuery.repeatNegative_total`, `EQuery.repeatNegative_correct`, `EQuery.unqueried_update_replays` | Protocol receives only prior index/value transcript, not an uncharged full input. Valid Fin indices and total/all-input correctness are explicit; repeated queries remain observable. |
| **C03-082** — Correct distinct-input runs query every coordinate | `Sensitivity.exists_update_changes`, `Query.Runs.queries_all`, `Query.Runs.length_lower_bound` | `EQuery.pairMinimum_distinct_coverage`, `EQuery.pairMinimum_distinct_lower_bound`, `EQuery.total_correct_protocol_has_witness` | All-input correctness plus replacement/replay gives the contradiction. Fresh replacement is actually proved, so no hidden restriction to replacement inputs that remain distinct. |
| **C03-083** — Charged-query lower bound and actual acquisition/optimality bridge | `Query.queryWork`, `Query.Runs.work_lower_bound`, `Query.linear_worst_case_bound`, `Query.linear_isBigO_of_query_bound`, `ReadAll.readAll_run_iff`, `ReadAll.readAll_work`, `Coordinate.work_exact`, `Coordinate.work_exists_uniform_linear_bound`, `Coordinate.competitor_query_work_lower_bound`, `Coordinate.exists_uniform_optimality` | `EQuery.repeated_negative_charges`, `EReadAll.repeated_plan_every_charge`, `ECoordinate.acquired_worker_execution`, `ECoordinate.concrete_every_work`, `ECoordinate.duplicate_every_work`, `ECoordinate.first_recursive_run`, `ECoordinate.pair_minimum_comparison` | Current I core/examples have a focused pass. Actual readAll acquires n coordinates, then actual selectRun consumes those acquired answers; work is c*n plus source calls. Uniform comparison constants precede c,n,k,input and competitor; c≥1 is required. Front-end bookkeeping is explicitly outside this tariff. No arbitrary-machine, randomized-competitor or runtime lower bound is claimed. |

## Source corrections retained by the formal correspondence

The mathematical source is interpreted with its exact intended domains and
with checked counterexamples to the incorrect statements. The pinned theory
and the explicit Lean statements determine the corrected claims; the PDF's
errors are not silently repeated or concealed.

| Source wording or omitted boundary | Corrected correspondence and witness |
|---|---|
| A weak `G≤n−k` in place of (3.1)'s strict upper count | `ECount.weak_upper_count_is_insufficient`: `[0,2]`, rank1, proposed value1 passes the weak counts but is not selected. |
| Strict half of chunk medians in (3.12) | `EPivot.strict_half_is_false`: `range 10` has medians `[2,7]`, lower pivot2 and one median above it. The valid bound is non-strict `≤floor(m/2)`. |
| Contracting coefficient letters a,b | `Rounded.recurrence_step_le` and `RoundedBounds.exists_affine_bound` use a,c; b,d are offsets. |
| Strict slope choice in (3.17), despite a maximum permitting equality | `ERounded.strict_slope_choice_counterexample` and `ERoundedBounds.zero_source_witness_bound` retain the zero-data equality case. Non-strict suffices. |
| Even central occurrences treated as different values | `ECount.duplicate_lower_median`, including `[1,1]`, retains tied central values. |
| “kth largest” wording against an ascending selector | `ECount.smallest_is_not_largest` and the zero/one-based adapter state the actual smallest-occurrence convention. |
| Equal bucket assumed to contain an arbitrary pivot | `ECount.outside_pivot_equal_block`; direct return of p is proved only after a valid middle index establishes an equal occurrence. |
| Minimum pivot described as quadratic at every rank/input | `Minimum.active_calls` states k+1 entries on distinct valid input; `EMinimum.minimum_is_not_four_calls` and the duplicate one-entry case delimit the worst claim. |
| Larger-side recurrence treated as the exact selected branch | `EDrift.selected_branch_is_smaller` gives next size1 versus majorant3. |

## Integration and acceptance still required

The local source correspondence preserves the complete chapter scope. The
remaining universal random witness and its source-cost consequence require
actual implementations, proof statements and connected examples. The all-equal
example corrections require their actual terminal validation. Documentation
of intended results cannot discharge either requirement.

The receiving candidate must select exact source revisions, update the real
public entry point and correspondence map, and account for every new example,
private helper and received dependency. The preassembly report found no
conflicting bytes among overlapping files in its five fixed snapshots; that
identity observation does not prove a later combined candidate builds. The
complete actual-type inventory must inspect universes, assumptions, failure
domains and existential constant placement with explicit `#check @name` inputs.

Follow the [README acceptance modes](../../README.md#build-and-audit) on a
stable isolated candidate. A focused module build is development evidence; it
does not replace source-policy/entry-point checks and the exhaustive kernel
axiom audit. Apply normal-versus-fresh triggers as written. The preserved
successful native fresh predecessor is not invalidated by workspace recovery,
and the explicit Nix waiver does not alter exact compiler/dependency pins,
proof restrictions or validation gates. The disclosed native launcher profile
remains part of the environment record.

Both independent Standards and Spec axes must assess the same final scope and
its actual closed validation evidence. Immediately before any local acceptance,
`./check.sh --verify-candidate HEAD` must match that exact approved candidate.
Only then may the accepted integration branch and accurate local coverage be
advanced. This documentation-only change makes no GitHub mutation and supplies
no whole-Chapter-3 type, audit, review or acceptance credit.

## Referenced companion source notice

The pinned Isabelle source names Manuel Eberl, TU München. The following
notice, already retained with the shared partition correspondence, accompanies
that source and its translated equations:

```text
ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```
