# Uniform minima under one global ranking

Historical checkpoint and local-ticket references in this account resolve through
the [preserved FDSA records](../history/textbooks/checkpoint-012/books/fdsa/README.md).
Current coverage and follow-up belong to [#558](https://github.com/VladimirMarko/conaled/issues/558);
old process and tracking instructions describe the producing session.

This bounded shared
unit supports the FDSA reconstruction. It closes no chapter or randomized
algorithm obligation. Its immutable candidate, exact requirements, independent
calculations and eventual validation/review results are retained in the local
durability checkpoint's FDSA-XU01 record.

**Validation snapshot — 4 November 2026.** A successful focused check covered
the minimum-law core and both example modules. A separate successful
inspection printed 37 public types from this unit. These are historical
results; reuse requires matching candidate evidence, and complete unit
acceptance was still outstanding in this snapshot. The full acceptance gates
below remain required.

## Mathematical interface

`Applications.Probability.PermutationMinimum.minimumEvent priority S a`
is a set of ordinary permutations of the index type I. A permutation π
belongs exactly when a is in the fixed finset S and

`∀ b ∈ S, priority (π a) ≤ priority (π b)`.

Thus π maps key indices to priority labels. A source list which instead maps
priority positions to keys has the inverse orientation. Every subset observes
the same π. The event definition needs only the target's order relation;
injectivity, finiteness and linear order belong to the probability law.

`uniformOn_minimumEvent priority hinj S a ha` states that, under the uniform
measure on all permutations, this event has mass `(S.card : ℝ≥0∞)⁻¹`.
The hypotheses are:

- I is finite; no public enumeration, index order or index measurable space
  is required.
- P is linearly ordered and `priority : I → P` is injective. P need not be
  finite or measurable, and priority need not be monotone in an index order.
- The permutation sample space has a measurable space with measurable
  singletons. These explicit hypotheses justify ordinary finite event
  probabilities; the unit installs no global measurable-space instance.
- `ha : a ∈ S` supplies membership and hence nonemptiness. The index type
  itself need not be inhabited: the permutation type has its identity even
  when I is empty.

The reciprocal is not a formula for the minimum of an empty set. The event
includes membership precisely so that outsiders and an empty S have empty
minimum events. In contrast, an outsider can satisfy all the raw priority
comparisons without being a member of the subset.

## Why the uniform law follows

For a nonempty S, finite minimum existence gives a minimum priority. The
injectivity of priority and the sampled permutation makes its attaining member
unique. Consequently, the member events are disjoint and cover the sample
space.

Exchanging two indices in S on the right of π exchanges their minimum events.
This transformation is a bijection of the whole permutation sample space.
Mathlib's existing finite uniform/counting measure laws show that the two
events have equal mass. Summing those equal masses over the disjoint cover
gives `S.card * p = 1`, and hence the reciprocal formula. No factorial
calculation, independent subset draw or selector is needed.

This is a small combinatorial connection over existing interfaces. The local
`Table`, finite-kernel and measured-execution developments keep their current
semantics; they need no new probability carrier, ranking record or executor.
The event and its elementary laws remain separate from normalization and
uniqueness assumptions. The finite-bijection machinery is a proof helper,
not a replacement invariance framework.

## Connected examples

`Examples.PermutationMinimum` uses the same uniform permutation of Fin 3 for
the subsets `{0,1}` and `{1,2}`. The public theorem gives index one's minimum
mass as one-half in each subset. The public event-intersection law identifies
the joint event with its minimum event in their union, the whole universe.
The same probability theorem then gives mass one-third. The product of the
marginal masses is one-quarter, and the example proves the inequality.

This matters for shared priorities: correct uniform marginals alone do not
license replacing the joint law by independent draws. The full-universe and
singleton specializations also connect to the generic probability theorem.

`spacedPriority` assigns the three indices the integer values `-7,100,4`.
Its injectivity and failure of monotonicity in the index order are proved.
The same public minimum theorem still gives a two-member subset probability
one-half. The target is infinite, its values have gaps, and its numeric values
are not ordinal positions. No mean numeric priority is inferred.

`Examples.PermutationMinimumBoundary` retains the consequential boundaries:

- The empty subset has an empty event. The permutation law on an empty index
  universe is nevertheless normalized.
- On Fin 2, candidate zero is an outsider of `{1}`, so its membership-aware
  event has mass zero. Its raw comparison has mass one-half, connected to
  the genuine minimum event in the full two-member set. It cannot be given
  the singleton's inverse-cardinality mass one.
- For constant tied priorities on a two-member set, each member is a
  non-strict minimum on every sample, with mass one. Dropping injectivity
  would therefore make the one-half formula false.

Independent exact enumeration checked every permutation and fixed subset
for universe sizes zero through six, including these overlap and empty
boundaries. That arithmetic is preparation evidence only. None of these
source-written examples is called checked until the required Lean gates pass.

## Source use and remaining chapter work

The source edition is *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, July 27, 2026, available from
[the authors](https://fdsa-book.net/functional_data_structures_algorithms.pdf).
Its SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The relevant later obligations are average/randomized quicksort in Chapter 2
and shared random-priority treaps in Chapter 10's notes. The recovered
treap source is Blelloch, Ferizovic and Sun,
[*Joinable Parallel Balanced Binary Trees*](https://doi.org/10.1145/3512769),
with the [author copy](https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf)
pinned at SHA-256
`c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`.
The shared-ranking construction is on pp.7:4–5; its root-priority estimate
and expected bulk-work argument require further results beyond this unit.

The exact fixed-subset minimum law is useful shared groundwork, not a claim
that the source algorithms have been implemented:

- Quicksort still requires its input-list/permutation orientation bridge,
  conditional subproblem laws or an explicitly proved equivalent joint
  construction, both recursive branches and its actual source tariff.
  Random occurrence pivots and duplicate inputs retain their own obligations.
- Treaps still require their canonical construction and deterministic
  root/ancestor characterizations under one shared priority assignment.
  Expected join/set-operation work additionally needs conditional depth,
  Jensen/charging arguments and an actual observed-work correspondence.
- The expected count of labels preceding all members of S has its own
  count/indicator bridge and finite-linearity proof. Interpreting count plus
  one as a first position additionally requires a nonempty subset and an
  ordinal/rank bridge. For empty S that quantity is only a sentinel.
- Full relative-order restrictions and conditional histories are stronger
  distribution claims. `Equiv.Perm.subtypePerm` restricts a self-map preserving
  a subtype; it does not automatically produce the induced order of an
  arbitrary subset under a global ranking.

The frozen requirements preserve these later obligations. Acceptance requires
immutable-candidate compilation, whole-candidate guarded verification,
exhaustive axiom audit, both independent review axes and immediate final
candidate verification.
