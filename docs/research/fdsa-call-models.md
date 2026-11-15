# Comparing the Chapter 1 call models

The FDSA source on printed pages 7–9 asserts three mathematical comparisons
in addition to its concrete recurrences: refining the local tariff preserves
asymptotic counts, a positive body cost absorbs an omitted nonrecursive entry,
and sharing may make demanded work cheaper than eager work. The original
Chapter 1 reconstruction recorded the conventions but omitted these comparisons.
The retained Spec review reopened them as SPEC-001, SPEC-002 and SPEC-003.

This repair gives those claims explicit conditional models. It remains a draft
until compilation, whole-candidate verification and independent final reviews
are recorded in `fdsa-control`. The previously checked append/reversal/induction
results retain their own evidence; that evidence does not validate these new
files.

## Source and architectural boundary

The source is the [official FDSA book](https://fdsa-book.net/), July 27, 2026
edition, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The frozen requirements addendum, original requirements, historical inventory
and corrected review are preserved outside the source diff in the checkpoint's
`fdsa-control` directory.

The book explicitly declines a proof connecting its mathematical observations
to a complete compiler/runtime/hardware stack. This repair keeps that boundary.
Neither calling a quantity work nor proving an asymptotic inequality establishes
a machine running time. The book's finite-word and RAM rationale remains a
conditional interpretation of its primitive-cost assumptions.

The constructions reuse ordinary lists and finite sums, `Resources.Measured`,
the existing `CallCount.tick`, Mathlib's asymptotic interface, and the existing
measured executor and potential laws. There is no new source-language compiler
or universal execution framework. Value agreement, resource observations,
validity and the external-program correspondence remain separate obligations.

## Fixed-program local tariff refinement

One trace element denotes one charged user-defined entry occurrence. The same
entry may have a nonnegative extra local charge for variable accesses,
constructors or the chosen primitives. `CallCount.refinedCost extra calls` is
the standard sum of `1 + extra i` over the actual occurrence list. Repeated
occurrences count repeatedly; there is no conversion of the trace to a set.
The coarse observation is its list length.

The public bounds establish

```text
calls.length <= refinedCost extra calls
refinedCost extra calls <= (K+1) * calls.length.
```

The second premise is a bound on each occurrence's local extra charge, not a
bound on total execution. The family-level theorem fixes K before quantifying
over inputs. `catalogue_refined_bounds` supplies that K from the supremum of
the extra charges over a finite fixed-program catalogue, independently of the
trace. Catalogue membership is a structural coverage premise: every local
body case in the trace must belong to that fixed catalogue. It does not require
finite data values, payload equality or payload inhabitance.

This is the precise content of the book's constant-per-equation explanation.
A fixed finite body has bounded local cases after recursive work is assigned
to its own charged entries. An actual application must supply that coverage
and its tariff, including any relevant external callbacks. Unbounded primitive
work or changing numeric bit widths are not silently assigned one constant
charge by this theorem.

An empty trace has both observations zero. When the trace represents evaluating
a user-defined function before optional inlining, its root is itself an entry.
Pure expression work with no enclosing charged entry needs an explicit root
or an additional boundary charge. The theorem does not infer that coverage
merely from a zero coarse observation.

`refinedCost_append` retains ordinary sequential trace composition.
`refinedCost_zero` recovers the original observation. `refinedCost_isBigO`
and `coarse_isBigO_refinedCost` give both standard real-cast asymptotic
comparisons for arbitrary input families and filters. The refined count retains
the original entries, so neither direction needs a positivity exception here.

### Actual append connection

`Examples.CallModels.appendEvents` records one cons branch for every source
element, followed by the terminal branch. Its empty and cons equations are
explicit, and `appendEvents_cost` equates its length to the existing measured
`ListReversal.appendRun` observation. The value and recurrence of that operation
were already established separately; a trace of unrelated length is not used
as its cost.

The illustrative refined tariff assigns one local variable access to the
terminal branch and four local operations to a cons body: three accesses and
one constructor. It therefore has exact observation `5*n+2`, whereas the
original count is `n+1`. The finite catalogue consists of the two Boolean
branch labels and has maximum extra charge 4. `append_refined_bounds` applies
the general catalogue theorem to obtain the factor 5 comparison, and
`append_refined_isBigO` uses the general asymptotic result.

For the input `[3,1,3]`, the observations are 4 and 17. Duplicate values remain
ordinary occurrences. The empty list still has one terminal call and refined
cost 2, even at the uninhabited payload type `Empty`. This tariff is specified
at the modeled source boundary; it is not a unique count of generated machine
instructions or variable loads chosen by an optimizing compiler.

## Omitting one nonrecursive entry

The source removes an entry unit from a nonrecursive time equation. For a
natural body observation T, the repair proves the unconditional `T <= T+1`
and the qualified `T+1 <= 2*T` when `1 <= T`. `tick_cost_comparison` connects
these inequalities to the actual existing `CallCount.tick`; its value remains
unchanged by `tick_value`.

For an input family, `add_entry_isBigO` requires eventual positivity in the
chosen filter. `cost_isBigO_add_entry` gives the unconditional reverse bound.
This states the needed quantifier order directly: a positive pointwise cost
or an eventually positive family can absorb the unit with one constant.

The zero exception is substantive. `zero_cost_entry_matters` refutes bounding
one by any natural multiple of zero. The retained intermittent family is zero
on every even input and n on odd inputs. It takes value 1 at input 1, but its
unit-added family is not Big-O of the original at infinity: after any proposed
cutoff, an even input still compares 1 to a multiple of 0. Thus being nonzero
somewhere does not justify an eventual-positive theorem.

These are comparisons at the specified entry boundary. They do not alone
verify an arbitrary multi-definition inlining transformation. Such a claim
would additionally need its fixed-program relation between retained and
eliminated entries, with root and zero-cost cases accounted for.

## Shared demand and an eager catalogue

The source's brief lazy-evaluation claim receives an explicit call-by-need
interpretation. Stable identities denote pure measured computations. An actual
request step checks an ordinary option cache; on a miss it computes and stores
the value and charges the callback's modeled work. On a hit it returns the
cached value without repeating that computation charge.

Cache validity says stored values agree with the corresponding pure callback.
It is established for the empty cache and preserved by requests. Demanded-value
laws connect each returned observation to that pure value, including requests
after arbitrary prefixes. Identity equality is needed by updates; payload
equality, ordering or inhabitance is not. Finite-catalogue assumptions belong
to the sum-of-work bound rather than the cache operation itself.

The public operations are `SharedDemand.request` and its cache-only projection
`SharedDemand.step`. `request_after_run_value` supplies the observation law for
any prefix of the existing `Resources.run`. `run_preserves_cached` shows that
intervening requests cannot remove an already stored result, while
`run_replicate_empty` gives the exact one-charge result for repeated demand.

The cost argument uses the remaining uncomputed catalogue work as a potential.
A miss spends precisely its computation's contribution, and a hit spends none.
The existing exact natural-potential theorem then yields conservation of
charged work plus final remaining work. Nonnegativity gives the upper bound
by the initially uncomputed work, and from an empty cache by the whole eager
catalogue sum. The final bound is derived from this transition, not assumed
as a simulation premise.

`remaining_store` and `step_potential` establish the local identity;
`run_work_remaining` connects it to `run_potential_exact`;
`run_cost_le_eager` gives the catalogue bound. The accounting identity does
not require cache validity. Validity is required separately when interpreting
stored payloads as the corresponding pure values.

The catalogue sum is an explicitly named specification. To apply it to an
external program, one must identify its eager computation occurrences,
preserve the relevant requested observations and stable sharing identities,
and prove that this sum matches that source program's eager observation.
The finite index denotes this execution catalogue, not all possible payloads.
The cache construction does not itself prove such a correspondence for every
program in an unspecified language.

The modeled charge is computation work supplied by the callback. It does not
include cache lookup/update/allocation or interpreter bookkeeping unless an
application introduces a tariff for those operations. This matches the
nonprimitive-call boundary being compared; it is not a runtime claim about
the function-map implementation of the cache.

The connected cases demand a cost-3 computation five times, charge only 3,
leave a cost-1000 computation uncached, and preserve the requested values.
Equal payloads at distinct identities retain separate charges; arbitrary
payloads and infinite identity types are also exercised where finiteness is
unnecessary. The empty catalogue case uses the uninhabited payload type
`Empty`.

The duplicated-let example uses actual shared and unshared measured layers
with matching values. `Duplication.sharedLayer` requests one cached result
twice, and `sharedLayer_eager` equates it with a single measured eager bind.
`unsharedLayer` evaluates the child twice through two measured binds. Their
recursive families have common value `2^n` and call counts `n+1` and
`2^(n+1)-1`, respectively. At depth four they return `(16, 5)` and `(16, 31)`.
This demonstrates why unshared call-by-name cannot be substituted for the
stated sharing model. It is a specified recurrence model, not automatic cost
inference for host-language syntax.

## Statement review and remaining validation

The source completeness repair retains the original algorithmic results and
narrows only unsupported interpretation claims. Its meaningful premises are
finite fixed-program local coverage, eventual positivity, stable pure
computation identities and a separate eager-catalogue correspondence. Those
premises do not assume any final total-cost bound. Empty/zero cases and repeated
uses are preserved rather than suppressed by incidental inhabitance or
distinctness assumptions.

The repair requirements were assessed as sufficient in principle by the
retained independent Spec reviewer. That assessment does not close the three
findings. The implementation, examples, elaborated assumptions, whole-project
compatibility and exhaustive axiom audit must still be checked on one committed
candidate, followed by both independent final review axes and final candidate
identity verification before Chapter 1 acceptance.
