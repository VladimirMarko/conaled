from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re, subprocess
B=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
W=B/'conaled-ch02-quicksort'; P=B/'fdsa-control/provenance/chapter03-selection-documentation-implementation-20261104'
R=B/'fdsa-control/provenance/chapter03-coverage-preassembly-20261104'
HEAD='27281919b9edd31a53336cbb5583ebc17632247e'
def git(*args):return subprocess.check_output(['git',*args],cwd=W)
def sha(b):return hashlib.sha256(b).hexdigest()
def save(name,obj):(P/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
assert git('rev-parse','HEAD').decode().strip()==HEAD
rows=copy.deepcopy(json.loads((R/'coverage.json').read_text())['rows'])
old=json.loads((R/'inputs.json').read_text())
sources={
 'Q':('Accepted Chapter 2 prerequisites','2da5708478a1d943a9214b5b386ec2db16cd9eca'),
 'V':('Rank, chunks, pivots, exercises and paid policies',HEAD),
 'S':('Rounded/scalar/group recurrences, cutoff and outside pivots','96c99a18a1f4ad28bbb8d13a17cbefb1899d8ab9'),
 'M':('Actual nested selection, measured helpers and generic bounds','1249f39968a44a25bfe3932d84a2cb44c6a83515'),
 'C':('Symbolic rank/map/actual-cost composition','660f974640fb89a766b26a4d786ae7ed197cecf2'),
 'R':('Random execution, expectation, drift and tail','0b8006f150cdb1aa9c76f5cf80eededca4417e81'),
 'E':('General all-equal random execution','d82ee6286de99a032eaf5fd925e6b87f48e0fb36'),
 'I':('Coordinate sensitivity, queries and actual paid acquisition','569545102ff70697066de429eb02f9f47dffa07f')}
key_for={'base':'Q','values':'V','root':'S','mom':'M','random':'R','query':'I'}
aliases={a:{'source':key_for[m['snapshot']],'path':m['path']} for a,m in old['module_aliases'].items()}
aliases['Composition']={'source':'C','path':'Examples/SelectionComposition.lean'}
aliases['RandomEqual']={'source':'E','path':'Applications/Resources/RandomSelectionEqual.lean'}
aliases['ERandomEqual']={'source':'E','path':'Examples/RandomSelectionEqual.lean'}
texts={}
for alias,m in aliases.items():
 commit=sources[m['source']][1];b=git('show',commit+':'+m['path']);s=b.decode();texts[alias]=s
 m.update(candidate=commit,bytes=len(b),sha256=sha(b),git_blob=git('rev-parse',commit+':'+m['path']).decode().strip(),declared_namespaces=re.findall(r'(?m)^namespace\s+([^\n]+)',s))

def update(num,**kwargs):rows[num-1].update(kwargs)
update(29,declarations=rows[28]['declarations']+['Composition.monotone_ranked_costs'],connected_cases=rows[28]['connected_cases']+['Composition.constant_ranked_costs'],assessment='The total dependent well-founded construction combines source partial correctness and termination. The current symbolic consumer composes RankedAt, noninjective monotone transport and uniform bounds on both actual executions; its focused pass is development evidence only.',open_gap_ids=[])
update(46,declarations=rows[45]['declarations']+['Composition.monotone_ranked_costs'],connected_cases=rows[45]['connected_cases']+['Composition.collapsed_actual_work'],assessment='Constants precede payload types/orders, input and rank; positive length is needed only when absorbing the intercept. The noninjective composition client bounds both actual costs without equating them. C03-083 separately connects paid acquisition to coordinate-query competitors.',open_gap_ids=[])
update(58,assessment='Actual correctness and termination hold for d≥2 and cutoff≥1; d=1 has an actual self-call obstruction. For positive d the crude fraction contracts iff d−floor(d/2)>2 (odd≥5/even≥6), while d=3,4 gives1. The sufficient-group cost uses a uniform finite prefix covering both cutoffs, with constants before payloads and ranks. The generic core/example pair at M has a focused pass; complete chapter gates remain.',open_gap_ids=[])
update(64,assessment='PENDING universal result. Present source proves the upper bound and an actual supported triangular path for n=2. Still required: every distinct input and every valid target rank, a specified endpoint sequence retaining the target until singleton, exact probability1/n!, triangular attainment, and an unbounded Nat/Int family. No future theorem name is assigned.',open_gap_ids=['universal-endpoint-witness'])
update(65,declarations=['RandomEqual.run_all_equal','RandomEqual.run_all_equal_summary','RandomEqual.run_all_equal_absorbed','RandomEqual.run_replicate_scan_lt_quadratic','Minimum.run_zero_rank'],connected_cases=['ERandomEqual.pair_both_valid_ranks','ERandomEqual.general_equal_execution','ERandomEqual.equal_family_below_quadratic','EMinimum.minimum_is_not_four_calls','EMinimum.duplicates_are_not_four_calls'],assessment='The current all-equal core/example pair E has a focused pass: every valid outcome has one active invocation, W=n and actual cost between 3n+6 and 4n+5. Earlier failures and four example proof-body corrections remain recorded. The paid minimum-rank-zero counterexample is also available. Neither family is a universal quadratic input claim.',source_state='source-present',open_gap_ids=[])
update(75,assessment='Expected n≤E T≤36n+2, source tail threshold9(4+w)n+2 and uniform quadratic upper are present. PENDING: the general quadratic lower/worst-case family transported from the universal C03-064 path. All-equal core E has a contrasting linear family, not that missing distinct-input witness.',open_gap_ids=['universal-source-worst-family'])
update(77,connected_cases=rows[76]['connected_cases']+['ERandomEqual.three_equal_first_atom','ERandomEqual.three_equal_last_atom'],assessment='Focused-passed earlier cases include singleton, duplicate equal block, valid rank0, endpoint-rank cases, different supported traces with the same result and a positive-probability triangular path on a pair. Additional all-equal atom/source cases at E now also have a focused pair pass. These finite cases and the general linear equal family do not discharge C03-064; complete chapter gates remain.')
update(83,assessment='Current I core/examples have a focused pass. Actual readAll acquires n coordinates, then actual selectRun consumes those acquired answers; work is c*n plus source calls. Uniform comparison constants precede c,n,k,input and competitor; c≥1 is required. Front-end bookkeeping is explicitly outside this tariff. No arbitrary-machine, randomized-competitor or runtime lower bound is claimed.',open_gap_ids=[])
for row in rows:
 for ref in row['declarations']+row['connected_cases']:
  alias,name=ref.split('.',1)
  assert re.search(r'\b(?:def|theorem|lemma|abbrev|inductive|structure)\s+'+re.escape(name)+r'(?=[\s(:{])',texts[alias]),(row['id'],ref)
assert [r['id'] for r in rows]==[f'C03-{i:03d}' for i in range(1,84)]

prefix=r'''# FDSA Chapter 3: selection correspondence and resource models

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
quadratic source-cost family in C03-075 remain **pending**. The general
all-equal core/example pair now has a successful focused check after its
recorded corrections. That separate linear family does not supply the missing
distinct-input worst path. Finite examples and intended future declarations
are not counted as the missing universal results.

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
'''
parts=[prefix.rstrip()]
for key,(scope,commit) in sources.items():parts.append(f'| `{key}` | {scope} | `{commit}` |')
parts.append(r'''
The generic actual-bound pair at `M`, the composition example at `C`, and the
coordinate acquisition/optimality pair at `I` have successful focused checks.
The all-equal pair at `E` also has a successful focused check after four
example proof bodies corrected the five normalization errors recorded at
`0fa60badfd353bcd6e22177d852d8d6399a2e0fe`; its core and all statement headers
were preserved. Earlier failures and exact corrections remain recorded. The older random execution,
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

The pure `Applications.Sequences.Chunks.chop` adapter reuses standard list splitting while
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
        = common + Tlength(es)                        if length ls ≤ k < length ls+length es
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
states `scanLaw=pure n` and linear source bounds. The complete all-equal
core/example pair at `E` has now passed its focused check, preserving the
earlier failure records. These results delimit worst-case quantifiers rather
than proving the missing distinct-input worst family or completing the
chapter's acceptance gates.

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
''')
parts+=['| Alias | Key | Source file | Namespace |','|---|---|---|---|']
for alias,m in aliases.items():
 ns=', '.join('`'+n+'`' for n in m['declared_namespaces']) or 'root'
 parts.append(f"| `{alias}` | `{m['source']}` | `{m['path']}` | {ns} |")
parts.append('''
## Complete obligation correspondence

All 83 frozen identifiers are retained. Each row names actual source and
connected cases; a name's presence is not an acceptance mark. The explicit
pending rows and the distinction between focused passes and full candidate
validation must survive assembly and review. The table records mathematical domains and source-model
limits rather than promoting a focused check to whole-chapter validation.
''')
groups={1:'Specification and elementary facts: pp. 31–32',9:'Partition and divide-and-conquer semantics: pp. 34–36',15:'Chunks and pivot balance: pp. 36–39',27:'Actual nested selector and Appendix B.2 calls',39:'Rounded recurrence and linear bound: pp. 41–44',47:'Exercises 3.1–3.8',59:'Random-pivot claims, actual expectations and tail',78:'Deterministic pivot-policy claims',81:'Coordinate-query optimality bridge'}
for row in rows:
 n=int(row['id'][-3:])
 if n in groups:
  parts+=['\n### '+groups[n]+'\n','| Obligation | Source declarations | Connected cases | Domain, correspondence and remaining work |','|---|---|---|---|']
 refs=', '.join('`'+x+'`' for x in row['declarations']);cases=', '.join('`'+x+'`' for x in row['connected_cases'])
 parts.append(f"| **{row['id']}** — {row['requirement']} | {refs} | {cases} | {row['assessment']} |")
parts.append(r'''
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
actual implementations, proof statements and connected examples. The focused
all-equal pass supplies a separate linear-family result and does not discharge
those missing universal claims. Documentation of intended results cannot
replace their implementation and validation.

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
''')
notice=(W/'docs/research/fdsa-three-way-partition.md').read_text()
start=notice.index('```text\nISABELLE COPYRIGHT NOTICE')
end=notice.index('\n```',start+8)+4
parts.append(notice[start:end])
parts.append('')
doc='\n'.join(parts)
doc=re.sub(r'\b(rank|size|sizes|cutoff|minimum|scalar|book|base|bound|least|from|to|value|values|and|masses|probability|is|pivot|cost|costs|execution|gives|adds|most|Exercise|majorant)(?=[0-9])', r'\1 ', doc)
assert re.findall(r'^\| \*\*(C03-\d{3})\*\*',doc,re.M)==[r['id'] for r in rows]
assert 'Unfinished documentation draft' not in doc and 'Remaining documentation work at this save' not in doc
(W/'docs/research/fdsa-selection.md').write_text(doc)
source_manifest={'recorded_utc':datetime.now(timezone.utc).isoformat(),'documentation_source_base':HEAD,'sources':{k:{'scope':scope,'commit':c,'tree':git('rev-parse',c+'^{tree}').decode().strip()} for k,(scope,c) in sources.items()},'aliases':aliases,'canonical_rows':83,'source_reference_count':sum(len(r['declarations'])+len(r['connected_cases']) for r in rows),'lexical_reference_check':'Every mapped declaration/example was resolved in the exact bound immutable source; this is not actual elaborated-type capture.','open_universal_rows':['C03-064','C03-075'],'all_equal':'Core/examples focused-passed at E after preserved example proof corrections; no whole-chapter acceptance.','current_focused_passes':['generic M','composition C','query I','all-equal E'],'original_preassembly_report_unchanged':True}
save('source-bindings-v3.json',source_manifest)
save('correspondence-v3.json',{'rows':rows})
b=(W/'docs/research/fdsa-selection.md').read_bytes();print('DOC',len(b),sha(b));print('ROWS',len(rows),'REFERENCES',source_manifest['source_reference_count'],'ALIASES',len(aliases))
