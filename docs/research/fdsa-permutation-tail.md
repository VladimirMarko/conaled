# Conditional laws of an observed remaining order

Historical checkpoint and local-ticket references in this account resolve through
the [preserved FDSA records](../history/textbooks/checkpoint-012/books/fdsa/README.md).
Current coverage and follow-up belong to [#558](https://github.com/VladimirMarko/conaled/issues/558);
old process and tracking instructions describe the producing session.

This bounded shared unit
continues the [whole-order draft](fdsa-permutation-order.md). Its frozen
requirements, preflights, exact finite expectations, candidate identity and
eventual gates are retained in the local FDSA-56 checkpoint record. No
chapter or algorithm obligation is accepted by this source draft.

**Development validation — 4 November 2026.** The conditional-tail core and both example modules had individual compilation successes in development checks that failed overall. All 61 explicit public declarations from the corrected source were subsequently included in the successful 815-declaration type inspection at `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`; both independent reviewers assessed their complete printed types. These are historical results for that development candidate. Reuse requires matching integration-candidate evidence. The full acceptance gates below remain required.

## The observation and conditioning event

The existing operation `restrictedOrder positions S π` reads a global
key-to-label permutation in inverse label order and filters to the fixed
subset S. The new ordinary event is more general:

```lean
firstEvent (Y : Ω → List I) a := {ω | (Y ω).head? = some a}
```

It concerns the actual list-valued observation Y. The definition needs no
decidable equality, measurable space, order or default key. Absence remains
explicit as `none`; `List.tail` already supplies the total tail operation.

For any Y and output xs, the pointwise event identity is

```lean
firstEvent Y a ∩ {ω | (Y ω).tail = xs} = {ω | Y ω = a :: xs}
```

It is valid even when Y sometimes returns an empty list. Under the actual
projection's Nodup assumption, its tail equals the projection onto
`S.erase a` on the event that a is first. Outside that event, removing the
head and erasing a can remove different keys, so the equality is explicitly
restricted to that event. Filtering the tail further to a fixed
`T ⊆ S.erase a` gives the original T projection on the same event and sample.

The finite support remains the earlier ordinary `orders positions S`, the
finset of list permutations of the filtered base enumeration. The cons
support equivalence removes a from that support. Its deterministic proof
needs Nodup positions, a∈positions and a∈S; full completeness is required
only by the probability laws that enumerate the whole index universe.

## An observed law under a changing environment

Write ηS for `uniformOn (orders positions S : Set (List I))`. The central
premise is Mathlib's existing

```lean
HasLaw Y ηS μ
```

It records a.e. measurability of Y and equality `μ.map Y = ηS`. The
environment Ω can be any measurable space and μ can already be a changed
conditional measure. The premise specifies the entire observed-list law;
a head marginal alone would not suffice.

For complete, Nodup positions and a∈S, the generic results are:

| Public result | Meaning under the supplied environment μ |
|---|---|
| `head_mass_of_hasLaw` | The actual event that Y starts with a has mass 1/S.card. |
| `hasLaw_tail_cond_first` | The actual tail of Y has uniform law on the orders of S.erase a after conditioning on that event. |
| `hasLaw_filter_tail_cond_first` | Filtering that actual tail to a fixed T⊆S.erase a has the uniform T-order law under the same conditioned measure. |

The output space has the caller's existing measurable structure and
measurable singletons. Completeness supplies finite I and countable List I
locally. There is no finite/discrete-source, uniform-environment, index-order,
inhabited-index or index-measurable-space hypothesis. The finite nonempty
target uniform measure supplies normalization through the existing HasLaw
interface; it is not a new independent premise.

Ordinary conditioning is `ProbabilityTheory.cond`, written `μ[|E]`. The
transport used here is

```lean
(μ[|Y ⁻¹' H]).map Y = (μ.map Y)[|H]
```

for a.e. measurable Y and measurable output event H. Existing restriction,
map and scalar laws prove this identity even for null events. Conditioning
is absolutely continuous with respect to μ, so Y remains a.e. measurable.
Existing HasLaw composition then transports the canonical tail and filter
laws. No new conditional-probability record, sampling executor, ranking type
or conditional-distribution kernel is introduced.

The one-step conclusion is substantive: its premise is the current whole
order's law, and its conclusion is the tail law under a new measure. It does
not assume the desired conditional conclusion or that the full environment
returns to its original distribution.

## Connection to the original global permutation

For `μ0 := uniformOn Set.univ` on permutations and
`O := restrictedOrder positions S`, XU02 supplies the actual whole-order law.
The new source-event specialization states, for every xs and a∈S,

```lean
(μ0[|firstEvent O a]) {π | (O π).tail = xs} =
  if xs ∈ orders positions (S.erase a)
  then (Nat.factorial (S.erase a).card : ℝ≥0∞)⁻¹ else 0
```

This scalar formula and the head-mass specialization require measurable
structure only on the finite permutation sample space. Their map versions
add the List I measurable/singleton assumptions. The original uniform
environment conditioned on the first event is also exactly `uniformOn`
that event; this last identity is particular to the original uniform
experiment, not a formula for arbitrary μ.

The proof connects the old full-order fibers to the actual tail through
the cons event identity. Supported prefix fibers have mass 1/S.card!.
Their finite disjoint sum gives head mass 1/S.card. With
`(S.erase a).card + 1 = S.card`, factorial successor and ordinary conditional
normalization give the reciprocal factorial for the remaining support.
Positive membership and finite natural casts justify the cancellations;
the zero-length remainder uses 0!=1.

The fixed remaining-subset law composes existing maps and the earlier
nested-filter theorem. Every invocation keeps the original complete
positions. The tail enumerates only a subset of I and is never supplied as
a purported complete enumeration of I. Individual filtered laws do not
establish independence between multiple branches.

## Connected cases

`Examples.PermutationTail` reuses the Fin4 global experiment with positions
`[0,1,2,3]` and S=`{0,2,3}`. Its initial HasLaw is assembled from the actual
XU02 map theorem. The new generic head theorem gives first0 mass 1/3.

After conditioning first0, `tail_23_mass` obtains the mass of `[2,3]` from
the new universal source-fiber formula. `tail_32_mass` obtains the mass of
`[3,2]` through the generic conditional HasLaw and its finite target measure.
Both masses are 1/2; `[2,2]` has mass zero through the off-support formula.
The map specialization and conditional-uniform-environment identity are
also instantiated directly.

The actual tail is filtered to `{3}`. Its generic HasLaw gives the sole
output `[3]` with mass one; the public on-event bridge connects this filter
to the original same-sample projection. The corresponding conditional
projection map law is instantiated as well.

The environment has changed: first0 now has mass one, whereas it originally
had mass 1/3. Nevertheless, the actual tail has uniform law on the orders
of `{2,3}`. This HasLaw, under the changed measure, is reused to derive
next-head-2 probability 1/2 and then the sole further tail `[3]` with mass
one. The second measure is the actual nested conditional measure. This
case exercises the generic interface twice without asserting a full
execution-history theorem.

`Examples.PermutationTailBoundary` retains the following independent
expectations and source-level connections:

- The key-to-label swap of 0 and 1 gives inverse global order `[1,0,2,3]`
  but selected order `[0,2,3]`. First within a proper subset need not mean
  first globally.
- A singleton selected set has its sole conditional tail `[]` with mass
  one through the new general law. Empty selected sets instead have an
  always-absent optional head. Their some-a events, and actual outsider
  events, are empty; conditioning them yields the zero measure. An empty
  index universe still has its identity permutation and empty observation.
- On Fin3, condition on first0 in S=`{0,1}` and observe T=`{1,2}` under
  the same sample. The two T orders have masses 1/3 and 2/3. T excludes
  the exposed key, but is not a subset of S.erase0. This shows why the
  containment hypothesis cannot be replaced by nonmembership of a alone.

Exact finite enumeration and statement assessments do not supply kernel
validation or final review approval.

## Source scope and remaining obligations

The source is the July 27, 2026 edition of
[*Functional Data Structures and Algorithms: A Proof Assistant Approach*](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The saved preflights retain the pinned Mathlib APIs and the recovered AFP
quicksort source evidence.

For Chapter 2's FDSA-2-24, this unit supplies a specified-pivot remaining-order
law and separate filtered-branch marginals. The AFP joint partition law,
actual sorting recursion, source tariff and equivalence to fresh random
occurrence choices remain separate obligations.

For Chapter 3's FDSA-3-59 to FDSA-3-77, indices represent occurrences. Equal payload
values do not identify those indices, and revealing only a repeated value
can merge several different head events. A history induction must establish
the initial law, connect each actual program update to the tail/filter
observation, justify its retained subset and account for all revealed
information. A set can be fixed after fixing a history without being fixed
over the original experiment; that relationship needs its own proof.

Generic HasLaw gives support almost everywhere, not pointwise. Invalid
outputs on null sets do not contradict it. An outsider event for arbitrary
Y can therefore be nonempty but null, although the actual projection has
the stronger empty-event fact. Null conditioning must remain the zero
measure. The inspected successive-conditioning/intersection theorem also
requires measurable events; a.e. measurability alone does not discharge
that stronger premise. These examples keep nested conditioning explicit.

Full histories, selection value/rank/termination, fresh-choice coupling,
drift and tail-cost bounds, arbitrary adaptive subsets, joint independence,
expected positions and treap charging remain queued. Completion of this
shared unit still requires its immutable-candidate compilation, guarded full
check, exhaustive audit, both independent final review axes and immediate
candidate verification. The prerequisite minimum-law and whole-order units
require their own recorded acceptance.
