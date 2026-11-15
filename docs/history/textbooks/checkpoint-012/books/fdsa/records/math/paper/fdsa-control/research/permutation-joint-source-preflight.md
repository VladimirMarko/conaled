# Disjoint relative orders: bounded joint-law source preflight

Prepared 2026-11-02. **Source/mathematical preparation only.** No scope is
frozen, no Lean implementation is authorized by this note, and no chapter
is activated or accepted. Control writes remained on hold until root released
the checkpoint 0022 capture. This note coordinates with
`permutation-joint-api-preflight.md`; earlier requirements, inventories and
reports are unchanged.

## 1. Proposed observation and precise hypotheses

Retain the existing complete, Nodup `positions : List I`, and the existing
`restrictedOrder` and `orders` definitions from XU02. Positions enumerates
priority-label indices. Under the original uniform global permutation law
μ₀, π maps keys to labels, so the actual ordered keys are `positions.map π.symm`.
Write `R_A π = restrictedOrder positions A π` and
`η_A = uniformOn (orders positions A : Set (List I))`.

For **fixed disjoint** finsets A and B, the desired conclusion is the actual
joint pushforward:

\[
\boxed{\mu_0.\operatorname{map}(\pi\mapsto(R_A\pi,R_B\pi))
       =\eta_A\mathbin{\operatorname{prod}}\eta_B.}
\]

Both components observe the **same** π. Separate equations for their two
marginals do not establish this statement. The conclusion proves that these
particular observations are independent; defining a fresh pair of independent
draws would omit the connection to the supplied experiment.

There is no requirement that A∪B cover the index universe, nor that either
subset be nonempty. Each order support is nonempty even for an empty subset,
whose sole order is `[]`. Off-support pair outcomes have mass zero. For
supported lists xs and ys the joint mass is `1 / (A.card! * B.card!)`, with
division in ENNReal/Real after casts and 0!=1. No order on keys or payloads,
nonempty index type, global Fintype or new ranking carrier is needed.
Completeness provides the finite index universe locally. Measure statements
use explicit measurable structures and measurable singletons on the sample
and list spaces, with the ordinary product measurable space.

### Generic current-observation form

Let Ω be any measurable environment, μ its current measure, and Y:Ω→List I
the actual current-order observation. For fixed S assume the existing
`HasLaw Y η_S μ`. For fixed disjoint A,B with A⊆S and B⊆S, the useful generic
result is

\[
\operatorname{HasLaw}
 \bigl(\omega\mapsto((Y\omega).\operatorname{filter}A,
                      (Y\omega).\operatorname{filter}B)\bigr)
 (\eta_A\mathbin{\operatorname{prod}}\eta_B)\;\mu.
\]

Here filter means ordinary membership filtering, and neither A∪B=S nor a
finite Ω is required. The complete positions list and the same prior list
measurability conventions suffice for the deterministic filter/pair map.
`HasLaw` gives a.e. measurability and the whole-list distribution. Since ηS
is a normalized finite law, source normalization follows; μ need not be
a uniform permutation environment. Valid list support is guaranteed only
almost everywhere for an arbitrary Y, not on every element of Ω.

Containment is a substantive premise. A label in A outside S cannot occur
in Y almost everywhere, although its target ηA order must contain it. Such
a filter cannot have that target law. With A=B=∅ the pair is ([],[]) with
mass one, including S=∅ and the empty index universe.

## 2. Source-faithful proof route and transport

The unconditional pair proof can reuse the equal-fiber mechanism of XU02.
Take supported pairs (xs,ys) and (xs',ys'). Disjointness makes both
concatenations xs++ys and xs'++ys' Nodup. Their lengths and key support agree.
Extend their positionwise correspondence to an ambient permutation σ, using
the existing finite extension construction. Equality of the two prefix
lengths gives `xs.map σ = xs'` and `ys.map σ = ys'` separately. Thus σ
preserves A and B individually.

The sample bijection `π ↦ π ∘ σ⁻¹` transports one pair fiber onto the other:
its inverse ordering is σ applied to the old ordered keys, and filtering
commutes with that relabeling on each preserved subset. Fixing all unused
labels pointwise is unnecessary. Nor must σ preserve an intermediate S for
this unconditional proof, which only observes A and B.

The pair fibers indexed by `orders positions A ×ˢ orders positions B` cover
the sample space and are disjoint. Their masses are equal. The target is
nonempty, so normalization gives the reciprocal of its cardinality. Existing
order-support cardinalities make this `1/(A.card! * B.card!)`. The ordinary
product of the two finite uniform laws has exactly those singleton masses.
Equality of the actual map and that product is then a finite-support measure
identity. A binomial/interleaving theorem or a new probability framework is
not necessary for this proof route.

For the generic statement, first obtain the canonical filter-pair law on ηS.
XU02 gives μ₀.map R_S=ηS. The existing nested-filter identity, with A,B⊆S,
identifies the pair of filters of R_S with (R_A,R_B) pointwise. Composing maps
therefore yields the canonical law on ηS. Compose this deterministic pair
map with the supplied `HasLaw Y ηS μ`. This transports the **actual** pair
observation to arbitrary μ without asserting that its environment is uniform.
The API preflight owns the exact Mathlib product/map/HasLaw assembly.

## 3. Reuse after the specified-head conditioning of XU03

Given a∈S, XU03 supplies, under `ν = μ[|firstEvent Y a]`, the law

`HasLaw (fun ω => (Y ω).tail) η_(S.erase a) ν`.

The head event has positive mass 1/S.card. Applying the proposed generic
joint law to fixed disjoint A,B⊆S.erase a yields the product law for the
**two actual tail filters** under this same ν. A and B may be determined
by the fixed revealed a and the fixed input data. They cannot depend on
additional unrevealed randomness without a new conditional argument.

For the original global projection, XU03's on-event value laws identify
these tail filters with R_A and R_B. For an arbitrary observed Y there is
no ambient π projection to substitute; the stated observations remain its
tail filters. The original complete positions list is retained. A partial
tail enumeration is not a complete enumeration of I.

This composition proves a particular one-step conditional independence
result. It does not give independence after arbitrary further observations.
In a history induction, the client must establish the actual current
`HasLaw`, its history measure and measurability, the program's tail/filter
update, and which subsets are fixed by the revealed history. A mixture over
different pivots is not automatically an unconditional product law.

## 4. Independently justified connected cases

These are small hand calculations by order-preserving interleavings, not
a rerun of the previous exhaustive enumeration campaigns. They should later
be connected to the joint law and, for the conditional case, XU03's actual
tail law.

| Case | Actual paired observation and independent count | Expected mass |
|---|---|---:|
| Fin4, A={0,2}, B={1,3} | Pair ([0,2],[1,3]); choose the two A-slots among four, giving six full orders out of 24. Each marginal order occurs in twelve of 24. | Joint 1/4; each marginal 1/2. Each of the four supported order pairs has the same six interleavings. |
| Fin5, A={0}, B={1,2,3}, with key 4 outside their union | Pair ([0],[1,2,3]); put keys 0 and 4 into two ordered distinct slots in 5·4=20 ways, then fill the other slots with the prescribed three-key order. | Joint 20/120=1/6; marginal masses 1 and 1/6. This tests unequal sizes and a proper union. |
| Fin4, A=∅, B=univ | Pair ([],xs), for one prescribed full order xs; exactly one of 24 samples. | Joint 1/24; the empty-coordinate marginal is 1. |
| A=B=∅ | The actual pair is always ([],[]), including an empty index universe with its identity-permutation sample. | 1, not a zero measure. |
| Fin5, full order conditioned first key 2; A={0,1}, B={3,4} | There are 24 conditional tails. Pair ([0,1],[3,4]) has six order-preserving interleavings, all following the exposed 2. | Conditional joint 1/4; each conditional marginal 1/2. The original head event has mass 1/5, and its joint event with the specified pair has mass 6/120=1/20. |
| Overlap Fin3, A={0,1}, B={1,2} | Pair ([1,0],[1,2]) occurs for global orders [1,0,2] and [1,2,0]. Equivalently, key 1 is first in the union. | Joint 2/6=1/3; product of the marginal masses is 1/4. |

Root's subsequent bounded independent calculation record is
`permutation-joint-calculations.json`, 7,281 bytes, SHA-256
`a7c8be932999da48c13c7291dbd68ee013d3ab1d7da65a978a2d7c8f9463bad4`.
It generates only the named populations n=0,3,4,5 once (151 tuples total),
then reuses them for these cases. Its results agree with the hand counts;
it also checks zero mass for an unsupported list in either coordinate and
the actual tail/projection equality on the Fin5 head event. That saved
record was read, not rerun or treated as Lean validation.

The Fin5 case should start from the actual full order, obtain its conditioned
tail HasLaw, and feed that law to the generic pair result. The conditioned
global environment has first-key-2 mass one instead of 1/5; it is not reused
as though it were still the original uniform environment.

Overlap is not universally independent. The last row shows why disjointness
cannot simply be omitted, while not claiming that every overlapping pair
must be dependent (constant singleton observations can be degenerate).
For a connected formal example, a finite supported-list table plus XU02
filter composition can identify this joint event with the actual full-order
`firstEvent` for key 1. XU03's head-mass theorem then gives 1/3; no new
minimum-law framework or independently resampled restrictions are needed.

Adaptivity is another independent issue. The earlier saved Fin3 boundary
chooses A to contain 0 and whichever of 1 or 2 occurs first. Let B be its
complement; these two sets are disjoint and have constant sizes two and one.
On the event A={0,1}, key 1 precedes key 2. The saved joint-order calculation
then gives probability 1/3 that 0 precedes 1, rather than the fixed-A uniform
probability 1/2. Thus sample-dependent disjointness and fixed cardinalities
do not establish the claimed conditional uniform product.

The product law concerns relative orders within the two subsets. Global
ordinal positions and raw assigned priorities retain their common
without-replacement constraints. Their independence is not a consequence;
this remains consistent with the XU04 placement boundary.

## 5. Exact book/AFP connection and retained bridges

The pinned FDSA book's §2.3, printed p.16, still has the literal first-pivot
two-way sorter: the left filter is y<x and the right filter is x≤y. That
page asserts both average-input and randomized-pivot O(n log n) behavior
while referring the probability proof elsewhere. C02-024 retains those
mathematical obligations. This preparation changes none of their domains.

The saved AFP source provides a precise use for the stronger joint result:

- `Quick_Sort_Average_Case.thy`, lines 103–105:
  `qs_cost_average_conv_rqs_cost` identifies the full cost distribution of
  the deterministic sorter on uniform permutations of a finite ordered set
  with `rqs_cost (card A)`. Its assumptions are finite A, `linorder_on B R`,
  and A⊆B. The uniform permutations of a set are distinct-key lists.
- Lines 117–124 first use `random_permutation_of_set` to expose a uniform
  head and a uniform remaining order. Lines 146–153 then explicitly use
  `partition_random_permutations` and `pair_pmf` for the **joint** law of
  the actual lower/complement filters. This is the proposed unit's direct
  correspondence point. The referenced helper's defining HOL theory was
  not newly fetched; this bounded reading verifies its actual use and
  input/output shape in the pinned AFP proof.
- `Randomised_Quick_Sort.thy`, lines 82–95, samples a uniform valid occurrence
  index, deletes that index, partitions the remainder and runs both recursive
  branches. `snd_rquicksort`, lines 200–202, connects its cost to the
  length-indexed law under ordered-domain, containment and distinctness
  assumptions. The recurrence at lines 186–189 samples a uniform pivot rank
  and combines two recursive cost laws. These are algorithm-specific laws,
  not conclusions supplied merely by the new pair of list restrictions.

After a specified pivot occurrence a, the lower and upper occurrence sets
are fixed by input data and a, are disjoint, and lie in S.erase a. Hence the
joint unit together with XU03 can supply the actual conditional partition
law needed for this AFP distribution route. Mapping the two coordinates
through their own deterministic recursive cost observations then transports
that pair law. The actual sorter recurrence, measurable/value correspondence
and induction are still required.

In particular, preserve these existing boundaries:

1. **Partitions and pivots.** The AFP uses membership in the reflexive
   order relation on the left; the book uses strict comparison. They agree
   on the pivot-deleted domain when keys are distinct. The bridge must be
   proved for the actual lists. Pivot rank is zero-based and must be related
   to the uniform occurrence index, not postulated independently.
2. **Occurrences and duplicates.** The shared theorem may index distinct
   occurrences carrying repeated values. Uniform occurrence selection is
   not uniform selection among distinct payload values. Mapping occurrence
   lists to payload lists can collapse outcomes. Revealing only a value
   can merge different occurrence-head events. The source two-way sorter's
   quadratic repeated-key family remains; the AFP's separate three-way
   duplicate variant does not silently replace it.
3. **Histories and executions.** A fixed initial permutation and fresh
   recursive pivot sampling need an actual execution-law/coupling proof
   if one is used to certify the other. Independence of the two list
   restrictions supports that proof; it does not establish all subsequent
   history laws or erase extra information observed by the program.
4. **Costs.** AFP `qs_cost` has empty cost 0 and adds the current tail length.
   FDSA Exercise 2.4 has its separate call/filter tariff, including empty
   cost 1. The retained pathwise target `T=4Q+4*length+1`, append association,
   pivot-selection work and other declared primitive costs still need
   their actual recurrence bridges. No arithmetic distribution for an
   unrelated recurrence is substituted for a measured execution.

For expected sums alone, correct conditional marginals already suffice;
linearity does not require this stronger independence theorem. The unit is
useful for the cited full distribution correspondence, not a reason to
enlarge the book's requested mean claims into unrelated distribution goals.

For C03-059–077, selection follows one retained branch, so the existing
conditional marginal law is normally sufficient. The new pair law is
available for disjoint occurrence partitions but supplies no new selection
rank, runtime, drift or tail proof. For C10-112–117 it can support fixed
disjoint relative-order observations after the corresponding treap
construction bridge. Actual operands may overlap; their shared-key
correlation remains. Cross-priority comparisons and global placement are
also not determined by separate internal orders. C10-117's conditional
depth, cluster continuation, Jensen and correlated weighted charging remain
open; the new law does not justify factoring E[dZ] without establishing
the relevant variables and independence/conditional bound.

## 6. Bounded recommendation and provenance

A small unit can comprise the actual global pair law, its generic observed-
order HasLaw transport, and connected composition with XU03 on the stated
cases. Ordinary product measures and deterministic filter/pair maps suffice.
A generalized sampler, random-execution framework, arbitrary-history
independence theorem or new algorithm is unnecessary. No proposed claim
here changes prior requirements or closes a source obligation.

Primary sources re-read locally:

- FDSA July 27, 2026, p.16 (PDF page 22),
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256
  `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
- `Sorting.thy`, lines 325–339, at Isabelle commit
  `f86f290225eebcc52c1ae7dba2e098f405f51c21`, SHA-256
  `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.
- Dated AFP archive
  <https://isa-afp.org/release/afp-Quick_Sort_Cost-2026-10-26.tar.gz>, SHA-256
  `cda7ed0a00991dcf8a5adff2d9909d6e761b2d8fb9501425ed8b93dbf462f457`.
  `Quick_Sort_Average_Case.thy`: SHA-256
  `bf8e889e3795d7951a096687deb297a7e74149e1e63157b0eeaa852d8a9e04f9`;
  `Randomised_Quick_Sort.thy`: SHA-256
  `c46c6a06cfd4612a634fa717d9403dc769a4f8b6ef6e266e4d3370d087f7d08f`.
  Retrieval metadata remains `../provenance/afp-quicksort-cost-source.json`.

Prior scope and calculation evidence reused:
`probability-source-preflight.md`, `quicksort-average-proof-plan.md`,
`permutation-order-source-preflight.md`, `permutation-tail-source-preflight.md`,
and `permutation-expectation-source-preflight.md`. The saved overlap/adaptive
calculations remain in `permutation-order-calculations.json`, SHA-256
`54163e6729373a9c78cd82432d48ae827498321c64e53e3c5160cebb54ca2f80`.

Only this requested note was written. No compiler, Git operation, project
hash helper, repository source, cache, configuration, gate, tracker or
requirements change occurred. No new primary-source retrieval or exhaustive
enumeration campaign was run. This source assessment supplies no validation
or final-review evidence.
