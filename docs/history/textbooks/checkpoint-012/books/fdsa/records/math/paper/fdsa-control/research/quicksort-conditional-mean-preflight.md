# Average-input quicksort: conditional mean bridge

Prepared 2026-11-02 by root while the original Chapter 1 candidate gate runs.
This is bounded read-only mathematical/API preparation. No Lean declaration,
compiler run, chapter activation, requirement change or acceptance is supplied.
Proposed proof steps below remain future Chapter 2 work.

## Scope and evidence

This note refines `quicksort-average-proof-plan.md` using the subsequently saved
whole-order and conditional-tail drafts. It concerns the mean of the actual
first-pivot source execution on a uniform ordering of distinct keys. The
separate random-pivot execution still needs its own construction and proof.

The book, Sorting.thy, AFP Quick_Sort_Cost archive and source metric identities
remain those in the original plan. In particular the source exercise count has
empty cost 1 and nonempty toll `4*(n-1)+3`, with append traversal uncharged.
The literal append-inclusive and random-choice work qualifications remain.

Inspected new primary code:

- Saved XU02/XU03 drafts at `a0597381f02eddd074ee96cabaa974f2062285f8`:
  `Applications/Probability/PermutationOrder.lean` and `PermutationTail.lean`.
  These are unaccepted source drafts, not certified dependencies.
- Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`:
  `Probability/HasLaw.lean`, `Probability/ConditionalProbability.lean`,
  `MeasureTheory/Integral/Bochner/Set.lean` and `Basic.lean`,
  `MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`,
  `Data/Finset/Sort.lean`, `Order/Interval/Finset/Fin.lean`, and
  `Algebra/BigOperators/Intervals.lean`.

The later joint-law draft is unnecessary for this mean-only route. The sum of
two conditional expectations requires each marginal law and integrability;
it does not require independence or equality of the entire cost distributions.

## 1. One finite environment, actual recursive input

Use a finite key type I with a complete Nodup enumeration `positions`. Let
`mu` be `uniformOn Set.univ` on `Equiv.Perm I`, and write `O_S` for the
existing `restrictedOrder positions S`. For a fixed finite key subset S,
the actual input is `O_S pi`, not an independently sampled replacement list.
The current Order draft supplies its Nodup, exact support, length and whole
uniform-order law. Enumeration order need not be the key's comparison order.

The source's arbitrary finite input list need not have a globally finite
payload type. For a Nodup list, use its finite membership subtype and a
complete attached enumeration, then prove the value/cost map correspondence
back to the original payloads. For keyed data, the source average domain
requires distinct keys on this actual input. Do not replace that hypothesis
by a distribution on all payload values or silently impose a global finite
payload type. Local classical equality decisions in a probability proof are
separate from the executable sorter's supplied comparison operation.

Let `T` be the already connected source cost projection of the measured
two-way quicksort. The desired induction quantity is

```text
F(S) = integral (fun pi => (T (O_S pi) : Real)) mu.
```

For S empty, `O_S pi=[]` pointwise and `F(S)=1`. Prove and use that base
explicitly; there is no positive-cardinality conditioning or pivot at zero.

## 2. Expose the first key without resetting the environment

For nonempty S and a in S, let `E_a = firstEvent O_S a`. The saved Tail draft
supplies `mu E_a = (S.card : ENNReal)^(-1)` and the conditional law of the
actual tail under `mu[|E_a]`. The key a is fixed throughout the proof for this
event. The new environment is the same original environment conditioned on
E_a; it is not asserted to be uniform on all permutations again.

Define the fixed children, in mathematical notation,

```text
A_a = {b in S.erase a | b < a}
B_a = {b in S.erase a | a <= b}.
```

Under a lawful linear order, these partition the erased support. Since a has
been removed and keys are distinct, the right predicate is also `a < b` on
that support. The explicit strict/reflexive partition correspondence remains
necessary when comparing the AFP source with the book.

On E_a, prove that the book's actual filtered tail is exactly `O_(A_a) pi`
on the left and `O_(B_a) pi` on the right. The saved
`filter_tail_restrictedOrder_eq` supplies the membership-filter identity;
the source comparator filters still need their on-support predicate bridges.
No such equality is asserted off E_a.

After that bridge, the actual measured source recurrence gives, on E_a,

```text
T (O_S pi) = T (O_(A_a) pi) + T (O_(B_a) pi) + 4*(S.card-1)+3.
```

This statement must come from the measured execution, including its actual
recursive values and charged filter calls. A postulated scalar recurrence or
an equality of sorted outputs cannot substitute for it.

## 3. Transport each conditional expectation

For either fixed child C contained in S.erase a, the saved public theorem
`map_restrictedOrder_cond_first` gives

```text
(mu[|E_a]).map O_C = uniformOn (orders positions C).
```

The earlier `map_restrictedOrder_uniformOn` gives the same target law for
the unconditional O_C. Construct the two ordinary `HasLaw` witnesses using
the corresponding measurable maps; the saved convenience HasLaw helper is
private, so a client must not attempt to import it by name.

At this Mathlib pin, `HasLaw.integral_comp` takes an
`AEStronglyMeasurable` cost function under the target law and equates its
composite expectation with the target integral. Use it once for the
conditional map and once for the unconditional map. Hence the conditional
child expectation equals F(C), without asserting that the whole environment
has its old law or that the two child observations are independent.

Measurability and integrability must remain visible. The permutation domain
is finite, so its actual functions are measurable with measurable singletons,
and `Integrable.of_finite` applies under the finite probability measures.
The list domain is countable for finite I; the pinned
`AEStronglyMeasurable.of_discrete` requires Countable and measurable
singletons and supplies the needed cost measurability. No finiteness of all
lists is asserted. Install the conditional probability instance using
`cond_isProbabilityMeasure` and the positive head-event mass before using
finite-measure integrability or integrating the constant toll.

Transport the pointwise on-event source recurrence using
`ae_cond_of_forall_mem`, then apply ordinary integral addition with the
actual integrability proofs. This yields

```text
integral (T o O_S) (mu[|E_a]) = F(A_a) + F(B_a) + 4*(S.card-1)+3.
```

The generic Tail theorem `hasLaw_filter_tail_cond_first` is an alternative
if the client keeps the actual filtered-tail observations instead of O_C.
It requires the fixed subset inclusion C ⊆ S.erase a and the actual whole
order HasLaw hypothesis under the current environment. It is not a theorem
about unrestricted adaptive subsets or arbitrary revealed histories.

## 4. Recover the original expectation from the head partition

For nonempty S, the measurable E_a are pairwise disjoint and cover the finite
permutation environment. Prove coverage from `restrictedOrder_length` and
membership of its actual optional head; disjointness follows from injectivity
of `Option.some`. There is no default key and no empty-head contribution.

The pinned `integral_biUnion_finset` takes the finite index set, measurable
events, their pairwise disjointness and integrability on each event. It gives
the sum of the restricted integrals. The exact conditioning definition is

```text
mu[|E_a] = (mu E_a)^(-1) • mu.restrict E_a.
```

The pinned `integral_smul_measure` rewrites a scaled integral using the
scalar's `toReal`. Since `0 < mu E_a < infinity`, cancellation gives the
restricted integral as `(mu E_a).toReal` times the conditional integral.
Record nonzero/finiteness and the natural-cardinality cast; do not cancel an
arbitrary null/infinite event or rely on totalized real division at zero.

Consequently, for n=S.card>0,

```text
F(S) = (1/n) * sum_(a in S) (F(A_a) + F(B_a) + 4*n-1).
```

The natural toll was first `4*(n-1)+3`. Rewriting it as the displayed real
expression uses n>0 and a checked cast/subtraction identity.

## 5. Rank bijection and the numerical recurrence

The missing bridge from a uniform key to a uniform rank is an actual finite
order equivalence, not the claim that enumeration positions are sorted.
The pinned `Finset.orderIsoOfFin S rfl : Fin S.card ≃o S` and its
`orderEmbOfFin` provide that equivalence. At index k, the lower child is the
image of `Finset.Iio k` under the embedding; prove this set equality using
the order equivalence and membership in S. Then `Finset.card_map` and
`Fin.card_Iio` give its cardinality k. The complementary child has
cardinality n-1-k, also obtainable from `Fin.card_Ioi` after the matching
image equality.

Reindex the finite sum through this equivalence. Once the child induction
has shown that each child mean is the numerical value A at its cardinality,
`Finset.sum_range_reflect` from `Algebra.BigOperators.Intervals` equates
the reflected sum of A_(n-1-k) with the forward sum. Its additive theorem
is generated from the inspected `prod_range_reflect` declaration. Thus

```text
A_0 = 1
A_n = (2/n) * sum_(k<n) A_k + 4*n-1       for n>0.
```

The original plan derives `A_n = 8*(n+1)*harmonic n - 12*n + 1` and its
logarithmic bound. There are two valid organization choices: prove the
connected means obey the recurrence and then its solution, or first verify
that this numerical expression satisfies the recurrence and use strong
induction on S.card with the actual conditional equation. The latter avoids
pretending a fixed finite environment contains subsets of every natural
size. A numerical helper alone supplies no algorithm-coverage credit.

The size-one case has two empty children and cost 5; it must agree with both
the exact algorithm and harmonic formula. Preserve the existing independent
size-three mean 71/3 and duplicate-key quadratic counterexample as connected
eventual Lean cases. Existing finite calculations need not be rerun merely
to restate them.

## Acceptance and scope boundary

This route uses the minimum/whole-order/conditional-tail accepted prefix when
available, plus actual Chapter 2 sorter, partition, rank and cost bridges.
It does not use XU04 or XU05, assert their acceptance, or change their retained
dependencies. The explicit random-pivot execution remains a separate book
obligation; a direct expectation induction can prove it without claiming a
full distribution identity. Append traversal, selection/removal work and
duplicate limitations remain exactly as recorded in the original plan.

No project source, ref, compiler, cache, gate or requirements were changed by
this note. All cited new draft declarations still require their own gates.
