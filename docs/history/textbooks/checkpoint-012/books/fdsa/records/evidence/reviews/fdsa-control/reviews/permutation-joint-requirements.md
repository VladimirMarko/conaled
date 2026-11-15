# Shared disjoint relative-order requirements

Recorded 2026-11-02 before implementation. This is FDSA-XU05, a bounded
shared probability unit under the user's cross-cutting exception. The
governing request remains `../REQUEST.md`. Chapter 1 remains active; this
unit activates and accepts no chapter or appendix. Earlier requirements
and source inventories remain unchanged.

## Preparation, placement and baseline

The fixed disjoint pair law supports the actual partition-law step of a
quicksort cost-distribution correspondence and composition with the earlier
specified-head conditional law. Expected sums alone need only correct
marginals; this scope does not enlarge the book into full coverage of AFP
or claim that independence is required for linearity of expectation.

Inputs assessed before implementation:

- `../research/permutation-joint-api-preflight.md`, SHA-256
  `1de920cbde00e253d18bcdb98786559ea39005be05ba3a99d12e20b2c731feb4`.
- `../research/permutation-joint-source-preflight.md`, SHA-256
  `83bbceb6a6f74434b80e3eec13d3bc59a8f21025ae3a93b1f387b3a8ccf86f64`.
- `../research/permutation-joint-calculations.json`, SHA-256
  `a7c8be932999da48c13c7291dbd68ee013d3ab1d7da65a978a2d7c8f9463bad4`.
  This is one bounded calculation of the named n=0,3,4,5 populations,
  generated once each, 151 key-to-label tuples total. Reuse the saved
  independent expectations; do not repeat the earlier exhaustive campaign.

Use isolated checkout `conaled-permutation-joint`, branch
`work/fdsa-permutation-joint`, starting at the committed expectation draft
`11923e9ffd17246b6f22c5594002a1ba0434e43c`. Record its clean starting state
before source edits. Only unchanged pinned dependency packages are shared;
project outputs are separate. The predecessor drafts are unvalidated.
Do not alter the active Chapter 1 gate, its source or configuration, or run
another compiler/project hash helper while that gate runs. The initial
deliverable is an explicitly uncompiled source draft.

Extend `Applications/Probability/PermutationOrder.lean` in its existing
namespace. This is the actual pair of that module's existing observations;
the placement permits direct reuse of its private list-extension and
relabeling helpers. Preserve all old public statements and existing cases.
Do not expose proof-only helpers merely to cross a private-module boundary,
duplicate their machinery, or add an abstract group-action framework.
New pair-specific private helpers and narrow shared proof calculations are
routine choices; record any necessary change to an earlier proof.

Use ordinary pairs, existing finsets/permutations, `Measure.prod`, `HasLaw`
and ordinary list filters. There is no new order or ranking carrier,
probability wrapper, sampler, executor, independence predicate or generic
random-execution framework. The unconditional core must not import the
later conditional-tail module. Its connected examples may do so. Add only
directly relevant imports and update the module description to include the
new bounded joint law accurately.

## The actual joint source law

Retain `[DecidableEq I]`, complete Nodup `positions : List I`, and the
existing key-to-label permutation convention. For fixed finsets A and B,
the observation is the ordinary pair

```lean
fun π => (restrictedOrder positions A π,
          restrictedOrder positions B π)
```

Both components observe the same sample. Under
`μ0 := uniformOn (Set.univ : Set (Equiv.Perm I))` and `hAB : Disjoint A B`,
prove the universal fiber formula, for every xs and ys:

```lean
μ0 {π | (restrictedOrder positions A π,
          restrictedOrder positions B π) = (xs, ys)} =
  if xs ∈ orders positions A ∧ ys ∈ orders positions B then
    ((Nat.factorial A.card * Nat.factorial B.card : ℕ) : ℝ≥0∞)⁻¹
  else 0
```

Tuple equality and the conjunction of the two component equations are
equivalent ordinary descriptions of this event; the tuple formulation
aligns with finite pair fibers. The scalar law needs measurable-space and
measurable-singleton instances only on the permutation sample. It requires
no measurable structure on output lists, their product, I or any payload.

Completeness supplies a local finite enumeration. Do not add public
Fintype I, Finite I, key order, Inhabited I, nonempty A/B or cover premises.
A∪B may be a proper subset of I. Empty A and B have their sole empty-list
orders; the factorial convention is 0!=1. Empty I still has its identity
permutation and normalized original law. Unsupported outcomes have mass
zero in either coordinate.

The substantive new argument is simultaneous relabeling of both supports.
Supported A/B orders have their exact corresponding key sets and lengths.
Disjointness makes their concatenations Nodup. The existing finite extension
helper yields one ambient permutation matching concatenated orders. Split
the mapped equality at the justified first-component length to obtain both
component maps and preservation of A and B separately. The established
sample bijection `π ↦ π * σ.symm` and existing relabeling law transport the
actual pair fibers. The unused complement need not be fixed pointwise.

Normalize those equal fibers over
`(orders positions A).product (orders positions B)`. The actual observation
always lies in that nonempty finite support; the disjoint fiber masses sum
to one. Its cardinal is A.card! * B.card!. Prove the formula from that actual
sample partition, not by defining an unrelated product draw or assuming
the desired independence. An interleaving-count framework is unnecessary.

## Product map and generic observed-order transport

Add caller-supplied measurable-space/singleton instances on `List I` for
the actual map theorem, using the canonical product measurable space:

```lean
μ0.map (fun π => (restrictedOrder positions A π,
                  restrictedOrder positions B π)) =
  (uniformOn (orders positions A : Set (List I))).prod
    (uniformOn (orders positions B : Set (List I)))
```

This product is the conclusion about the original joint observation. The
proof must establish the finite probability/SFinite instances for both
nonempty finite order supports before using product rectangle formulas.
`List I` is countable under the locally finite I, not generally finite.
Countable singleton extensionality, the scalar formula, existing uniform
finite-support probabilities and ordinary product singleton equations
suffice. Retain the finite/positive factorial-cast conditions needed by
ENNReal inverse multiplication. Do not rely on a totalized product outside
the applicable SFinite hypotheses.

For `{Ω : Type*} [MeasurableSpace Ω]`, current measure μ and actual
observation `Y : Ω → List I`, assume the existing whole-order law

```lean
hY : HasLaw Y (uniformOn (orders positions S : Set (List I))) μ
```

For fixed A,B with `hAS : A ⊆ S`, `hBS : B ⊆ S` and `hAB : Disjoint A B`,
prove

```lean
HasLaw
  (fun ω => ((Y ω).filter (fun a => decide (a ∈ A)),
             (Y ω).filter (fun b => decide (b ∈ B))))
  ((uniformOn (orders positions A : Set (List I))).prod
    (uniformOn (orders positions B : Set (List I)))) μ
```

Keep the same complete positions interface and list measurable assumptions.
The generic theorem must not require finite/countable/discrete Ω, measurable
singletons on Ω, a uniform environment μ, a stronger `Measurable Y` premise,
or a caller-supplied measurable structure on permutations. `HasLaw` supplies
a.e. measurability and the actual whole-observation map law. Its normalized
target supplies source normalization when a client needs it.

First prove privately the canonical pair-filter law on the existing whole-S
order measure: rewrite that measure as the old actual global projection,
compose maps, and use the two existing nested-filter identities. Then use
`HasLaw.fun_comp` with hY to obtain the actual pair under μ. A and B need
not cover S. Containment is consequential: a label outside S cannot occur
in Y almost everywhere although its target order would contain it. Valid
support of arbitrary Y is an a.e. fact, not a pointwise guarantee on Ω.

Use exactly these three new public results and explicit argument orders:

- `uniformOn_restrictedOrder_pair_eq positions hnd hcomplete A B hAB xs ys`.
- `map_restrictedOrder_pair_uniformOn positions hnd hcomplete A B hAB`.
- `hasLaw_filter_pair positions hnd hcomplete S hY A B hAS hBS hAB`.

I, Ω, universes, instances, μ and Y are inferred. The third name is the
shortened final name for the preflight's suggested `_of_hasLaw` result;
there is no additional alias. Existing `indepFun_iff_hasLaw_prodMk_prod`
supplies an independence client without a new public wrapper. No separate
conditional joint wrapper is needed: compose the generic theorem with the
existing conditional-tail HasLaw.

## Connected cases and expected values

Develop the source and these uses together. Use actual existing observations
and public laws in their derivations; independent arithmetic or a newly
defined product experiment alone does not establish the required connection.
Reuse the earlier public Fin4 fixture where it suffices. Keep main and
boundary modules connected through the public root.

### Two nontrivial disjoint restrictions

On Fin4 with positions [0,1,2,3], let A={0,2}, B={1,3}. Prove disjointness
and instantiate the universal joint law for ([0,2],[1,3]) to get 1/4.
Use XU02's old marginal laws to get the actual two marginal masses 1/2.
Instantiate the new pair-map law, assemble actual marginal/joint HasLaws
and derive the existing `IndepFun` proposition through
`indepFun_iff_hasLaw_prodMk_prod`. This proves independence of these
observations from the new joint law, rather than from the marginals alone.
The malformed left outcome [0,0] with a valid right outcome and the
malformed right outcome [1,1] with a valid left outcome each have mass zero
through the universal off-support formula.

### Unequal sizes, unused labels and empty boundaries

- On Fin5, A={0}, B={1,2,3}, key 4 is outside their union. The actual pair
  ([0],[1,2,3]) has mass 1/6 through the new law. Retain the proper-union
  fact, so no accidental cover premise is hidden by the examples.
- On Fin4, A=∅ and B=univ, the actual empty coordinate is [] and a prescribed
  full order paired with it has mass 1/24 through the new law.
- For I=Empty and complete positions [], the actual pair is ([],[]) and
  the original sample is normalized. Instantiate the generic pair-filter
  law on the actual empty whole-order observation as well as the scalar
  joint formula. No key or default member is manufactured. This exercises
  the S=A=B=∅ endpoint of the generic statement.

### Composition under an actual changed environment

On Fin5, let Y be the actual full order from positions [0,1,2,3,4], E its
first-key-2 event and ν=`μ0[|E]`. Start from the existing XU02 actual map law
to establish Y's whole-order HasLaw. XU03 gives μ0(E)=1/5 and the actual
tail's uniform law under ν on `univ.erase 2`.

Let A={0,1}, B={3,4}. Prove their disjointness and containment in that
remaining support, then feed the tail HasLaw into `hasLaw_filter_pair`.
The output law concerns the pair of actual tail filters under this same
ν. Establish conditional normalization from the positive head event. Use
the resulting product law to derive the supported pair ([0,1],[3,4]) mass
1/4. The existing conditional marginal HasLaws and independence equivalence
may additionally expose the corresponding existing IndepFun statement.

Connect both tail filters on E to the original same-sample A/B projections
through XU03's pointwise filter-tail bridges. Transport this pair equality
to ν-a.e. equality and the joint HasLaw. The actual projection-pair event
therefore has mass 1/4 as well. Retain the changed-environment fact ν(E)=1
versus μ0(E)=1/5; do not reuse ν as though it were the original uniform
permutation measure. All calls keep the original complete positions, never
an incomplete tail enumeration. No arbitrary-history theorem is claimed.

### Overlap invalidates the general product conclusion

On Fin3 with A={0,1}, B={1,2}, the actual paired event ([1,0],[1,2]) has mass
1/3, while each actual marginal has mass 1/2 and their product is 1/4.
Prove the joint-event connection, for example by XU02 nested filtering and
a finite supported-full-order table identifying it with actual full-order
`firstEvent` for key 1. XU03's head mass then supplies 1/3. Compare this
with the two old marginal probabilities. Do not assert that every possible
overlapping pair is dependent; this counterexample refutes dropping the
disjointness hypothesis from the general result.

## Source limits, review and acceptance

The pinned AFP quicksort proof uses `partition_random_permutations` and
`pair_pmf` at the joint-law step of its full cost-distribution correspondence.
This unit supports that specific method. Actual occurrence partitions,
pivot-deleted strict/non-strict agreement for distinct keys, pivot rank,
recursive program/value laws, complete histories, fresh-choice coupling and
the source's call/filter/append tariff bridges remain Chapter 2 work.
Uniform occurrences must not be replaced by uniform distinct payload values,
and the book's two-way repeated-key behavior remains separate from a
three-way algorithm. Selection normally follows one retained branch, for
which the earlier marginal law already suffices.

Fixed disjoint internal orders do not give independent global ordinal
positions, raw priorities, arbitrary adaptive subsets or overlapping treap
operands. Mixtures over revealed pivots need their own law. C10-117's
conditional depth, Jensen, actual work and correlated weighted charging
remain open; E[d] does not factor E[dZ] without the relevant established
variables and independence/conditional argument.

Statement review must cover actual shared-sample semantics, tuple versus
component events, fixed-set quantifier order, preservation of both disjoint
supports, concatenation lengths, correct inverse orientation, complete
finite support and its cardinality, empty endpoints, arbitrary list-space
measurability, SFinite/product normalization and generic a.e. transport.
Use only allowed project axioms; no admission, source axiom, unsafe/partial
definition, native_decide or skipped kernel checking is permitted.

Capture an immutable candidate with these requirements outside its diff.
All old and new connected cases remain in the normal public build/audit.
Matching focused compilation, full guarded candidate checks and exhaustive
audit, independent final Standards and Spec reviews, and immediate candidate
verification remain mandatory. Reconcile and accept the repaired Chapter 1
and preceding shared base before accepting this extension. No preflight,
finite calculation or durability checkpoint closes a formal gate.
