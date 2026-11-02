# Preceding counts and actual first positions

Status: **source draft, not compiled or accepted**. This shared unit uses the
[minimum-event draft](fdsa-permutation-minimum.md). Its conditional boundary
example also uses the [whole-order](fdsa-permutation-order.md) and
[conditional-tail](fdsa-permutation-tail.md) drafts. The local FDSA-XU04
record retains frozen requirements, prior source/API assessments, independent
expectations, the immutable candidate and subsequent validation. No chapter
or algorithm obligation is accepted by this draft.

## The actual observation

The operation in `Applications.Probability.PermutationExpectation` is

```lean
beforeCount priority S π :=
  Set.ncard {b | ∀ a ∈ S, priority (π b) < priority (π a)}
```

Here π assigns a priority label to each key and S is a fixed finite subset
of keys. The observation counts keys that strictly precede every member of
S. It needs only a strict relation on the priority target. It does not need
a key order, a finite enumeration, decidable equality, a measurable priority
target or an inhabited key type.

`Set.ncard` is the ordinary totalized natural cardinality: it is zero on an
infinite set. Consequently the finite-population interpretation is used
under the explicit `Finite I` assumptions of the population laws. At an
empty subset the predicate is vacuous, and `beforeCount_empty` gives
`Nat.card I` without a finiteness premise.

For finite I and a preorder on priorities, `beforeCount_le` states

```lean
beforeCount priority S π ≤ Nat.card I - S.card
```

No member of S can precede itself, so the counted set is contained in the
complement. This value bound has no injectivity or probability assumption.
Tied priorities can satisfy it even when the exact expectation law fails.

## The fixed-subset count mean

Put `μ0 := uniformOn (Set.univ : Set (Equiv.Perm I))`. For finite I, a linear
order on the priority target and an injective `priority : I → P`, the two
mean laws give

```lean
(∫⁻ π, (beforeCount priority S π : ℝ≥0∞) ∂μ0) =
  ((Nat.card I - S.card : ℕ) : ℝ≥0∞) / ((S.card + 1 : ℕ) : ℝ≥0∞)

(∫ π, (beforeCount priority S π : ℝ) ∂μ0) =
  ((Nat.card I - S.card : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ)
```

The subtraction is in Nat before casting; division is in the displayed
scalar type. The successor denominator is positive and finite. S may be
empty, and I may be empty: the permutation sample still contains the
identity and its uniform measure is normalized. Only the permutation
sample has measurable-space and measurable-singleton assumptions. The
priority target can be infinite and need not carry a measurable structure.

For each b outside S, the actual strict-before event equals the existing
minimum event on `insert b S` with distinguished member b. The reverse
implication uses injectivity to eliminate equality with a member of S.
That event has mass `1 / (S.card + 1)` by the earlier minimum theorem.
The proof connects the actual counted set to the finite sum of these
outsider indicators, integrates the sum and counts the complement. It
uses no independence assumption.

The real proof establishes finite-sample integrability through
`Integrable.of_finite`, consumes it in the `ENNReal.ofReal` integral
transport, and justifies the finiteness of the displayed ratio. Its
expectation is not an interpretation of a totalized nonintegrable integral.

## The actual ordinal minimum

For `rank : I ≃ Fin U` and `hS : S.Nonempty`, `beforeCount_rank_eq` states

```lean
beforeCount rank S π =
  ((S.image (fun a => rank (π a))).min'
    (hS.image (fun a => rank (π a)))).val
```

The minimum is the actual finite-image minimum on its proved nonempty
domain. The composed equivalence `π.trans rank` carries the counted set
onto the initial segment below that minimum. Its cardinality is the
minimum's zero-based value. Rank supplies the finite population locally;
this pointwise result needs neither a separate finite-type assumption nor
probability premises. Rank need not respect the keys' search order.

Adding one to that actual minimum, `integral_firstPosition_uniformOn`
gives mean `(U + 1) / (S.card + 1)` in ℝ. The proof uses the count bridge,
finite integrability and normalization, then justifies `S.card ≤ U` and
the subtraction casts. Nonemptiness remains essential for this minimum
interpretation. When S is empty, count+1 is a sentinel beyond the universe;
there is no first selected key.

These statements observe ordinal positions. They do not assert a universal
formula for the numerical value of an arbitrary injective priority.

## Connected examples and boundary cases

`Examples.PermutationExpectation` specializes the new laws as follows:

| Population and selected keys | Mean count before S | Mean actual one-based position |
|---|---:|---:|
| Fin3, S={0,1}, identity rank | 1/3 | 4/3 |
| Fin4, S={0,3}, identity rank | 2/3 | 5/3 |

Both ENNReal and real count results are used for the Fin3 case, together
with the deterministic count bound. A nonidentity rank swapping labels 0
and 2, at the identity sample with S={0,1}, has count 1, actual minimum
rank 1 and one-based position 2 through the generic pointwise bridge.

For the injective Int-valued priority `j ↦ 100 + 10*j.val`, the general
count theorem still gives 1/3. The raw numeric observation is defined as
the actual minimum of the selected finite image. The existing monotone
image-minimum theorem and the rank bridge establish that this raw minimum
equals `100 + 10*beforeCount` pointwise. Only then does justified finite
integration give its real mean 310/3, different from ordinal mean 4/3.
The minimum is not defined to be the desired affine expression.

`Examples.PermutationExpectationBoundary` retains these consequential cases:

- Empty S on Fin3 has count and mean 3; count+1=4 is only a sentinel.
  Empty I has mean count 0 through the general law, without a selected key.
- A singleton on Fin3 has mean count 1 and first-position mean 2. A full
  Fin3 subset has actual count 0 and first-position mean 1.
- Constant priorities on Fin2 and proper subset {0} have actual count and
  mean 0. The formula with its injectivity premise removed would give 1/2.
  The deterministic complement bound remains applicable.
- The sample-dependent singleton `{π.symm 0}` on Fin3 always has cardinality
  one but count 0, so its mean is 0. Fixed cardinality does not replace the
  requirement that S be fixed before sampling.

The same boundary module keeps the actual Fin3 global order observed from
positions `[0,1,2]`, conditions it to start with key 0, and observes the
fixed singleton {1}. The event has original mass 1/3. The two remaining
orders `[1,2]` and `[2,1]` each have conditional mass 1/2 through the earlier
head/tail laws, and the actual preceding count is respectively 1 or 2.

Its pointwise bridge uses the new rank theorem and the actual order, then
passes the on-event equality to almost-everywhere equality under the
conditioned measure. Finite integrability and the proved conditional
probability measure give mean 3/2, while the new original-global-law theorem
gives mean 1. The actual singleton relative-order observation has the same
`HasLaw` under both measures, through the earlier original and conditional
projection map laws. Thus that relative-order law alone cannot justify the
global-placement mean. There is one original sample and its actual
conditional measure throughout.

These expected values and source-written proofs remain uncompiled; exact
finite arithmetic and source inspection do not supply kernel validation.

## Source use and remaining chapter work

The book source is the July 27, 2026 edition of
[*Functional Data Structures and Algorithms: A Proof Assistant Approach*](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The frozen preflights retain the pinned Mathlib APIs and the source evidence
for Chapter 10's shared-priority treap argument, including its cited
[joinable-trees paper](https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf).

For operand sets A and B with |B|≤|A|=s>0 and universe A∪B, the fixed-set
ordinal formula entails an expected one-based root position below 2 after
the canonical treap root/minimum correspondence has been proved. That
correspondence remains an algorithm obligation. The mean law itself does
not establish conditional depth, Jensen's hypotheses, rank-cluster
continuation, adaptive histories or actual expected work.

In particular C10-117's correlated weighted-charging argument remains
open. A bound on E[d] does not factor E[dZ]; overlapping operands share
the same global permutation. The conditional-placement example also shows
why an unchanged relative-order law cannot silently stand in for the
original global-placement law. No quicksort or selection cost bound is
claimed by these scalar observations.

Acceptance still requires an immutable candidate, focused compilation, the
applicable full guarded build and exhaustive audit, independent Standards
and Spec reviews with findings resolved, and immediate candidate
verification. The repaired Chapter 1 and preceding shared base retain
their own pending gates.
