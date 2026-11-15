# Shared uniform-permutation minimum requirements

Recorded 2026-11-02 before implementation. This is FDSA-XU01, a bounded
cross-cutting unit under the user's explicit exception for shared concerns.
The governing request is `../REQUEST.md`. Chapter 1 remains the active chapter;
no chapter is accepted, and this unit does not activate a later chapter.

## Origin, baseline and scope

Chapters 2 and 10 need fixed-subset minimum laws under one global random
ranking. The source obligations and remaining algorithm-specific work are
recorded in `../research/finite-ranking-source-preflight.md`, SHA-256
`a67ce7f338587b1cf719c47e200fde4fff948647f67d04571e5b209a68a738f9`.
The coordinated pinned-API preflight is
`../research/finite-ranking-api-preflight.md`, SHA-256
`97da582310e190ab7036817ee42e746ee3f14a4a6ed44b690b449d86748ef6dc`.
Independent exact finite calculations are retained in
`../research/finite-ranking-calculations.json`, SHA-256
`36f853f68d0f0713581aea33e7c91187a003f99bb7386ff5ba509e52964c1949`.
The calculation file also explores a separately scoped future count mean;
that exploration does not include the mean in this unit's acceptance scope.

Start from the committed Chapter 1 repair
`a14977b9e316cc484ffad8a470d26b15615956c0` in an isolated development worktree
`conaled-permutation-minimum`, branch `work/fdsa-permutation-minimum`.
This base is an unvalidated draft, not an accepted dependency. Record the
clean starting state before source edits. Keep separate project output paths;
only the unchanged pinned dependency package path may be shared. Do not
change the active old-candidate validation checkout or run another compiler
while its gate is active. Save this unit as an explicitly uncompiled draft
until the sequential validation resources become available.

Use ordinary permutations, finsets, sets and Mathlib's `uniformOn` measure.
No new probability carrier, random executor, ranking record, minimum selector
or action framework is justified. The source's global ranking sends key
indices to distinct priority positions; its inverse sends positions to keys.
The assignment is one common random environment for all observed subsets.

Suggested core is `Applications/Probability/PermutationMinimum.lean`, with
connected clients in `Examples/PermutationMinimum.lean`. Naming and helper
placement are routine implementation choices. Keep expectation and full
relative-order imports out of this minimum-law unit unless an actual proof
dependency requires them.

## Required mathematics and assumptions

For an index type I, a priority type P with an order relation, an ordinary
function `priority : I → P`, a finset S and an index a, define the event

`{π : Equiv.Perm I | a ∈ S ∧ ∀ b ∈ S, priority (π a) ≤ priority (π b)}`.

The membership conjunct is part of its meaning: it is the event that a is
a minimum member of S, rather than a comparison event for an outsider.
Its definition needs only `LE P`; finiteness, injectivity and linear order
are laws' hypotheses. Retain useful elementary empty/outsider and singleton
specializations without imposing the probability theorem's hypotheses on
the event itself.

Under `[Finite I]`, `[LinearOrder P]`, injectivity of priority, and existing
measurable-space/measurable-singleton instances on `Equiv.Perm I`, prove:

For every fixed S, a and proof `ha : a ∈ S`,

`uniformOn Set.univ (minimumEvent priority S a) = (S.card : ℝ≥0∞)⁻¹`.

The reciprocal is in the extended nonnegative reals, not natural division.
Membership already supplies nonemptiness; do not add a redundant hypothesis.
Do not impose an order or measurable space on I, a finite or measurable
priority target P, a public Fintype enumeration, or an inhabited/nonempty
index type. A classical equality decision and local Fintype are proof tools.
Explicit measurable-singleton structure on the finite permutation sample
space justifies the event masses. Do not install a new global measurable
space instance on permutations.

Prove the probability under the supplied global uniform law. Replacing that
experiment by an independently uniform draw from S is not a proof of this
claim. The intended argument uses a bijection exchanging two key labels,
existence and uniqueness of a finite minimum, and the disjoint event
partition of the sample space. Either this argument or another sound
source-faithful proof is acceptable; proof syntax is not an acceptance
requirement. No factorial formula or full-order restriction theorem is
required. Right composition exchanges key labels; left composition generally
changes the ordered priority labels and needs a different justification.

## Connected cases and independently expected results

Develop these alongside the public result and retain their connections to
it. Exact finite enumeration is independent arithmetic, not Lean validation.

1. On one uniform permutation of Fin 3 with identity priorities, let
   S={0,1} and T={1,2}. Derive through the generic theorem that index 1 is
   first in each subset with probability 1/2. Prove that the intersection
   of those events is its minimum event in S∪T, and obtain mass 1/3 through
   the same theorem. Prove this differs from the product 1/4. Both events
   must use the same sampled permutation.
2. Use an injective priority assignment into Int with a negative value and
   nonuniform gaps. Derive a two-member subset's mass 1/2 through the public
   theorem. This exercises an infinite priority target whose numeric values
   are not ordinal positions. Do not infer a mean raw priority from ranks.
3. Exercise singleton and full-universe subsets. The singleton member has
   mass one; members of a nonempty full finite universe have reciprocal
   universe-cardinality mass. These may reuse the Fin 3 cases where they
   already demonstrate the public theorem's connections.
4. Empty S has no first member. Show its event is empty; do not apply the
   reciprocal formula to card zero. Include an empty index type to verify
   that the probability space of its permutations is still normalized,
   without adding a global nonempty-I assumption.
5. For Fin 2, S={1}, candidate 0, the membership-aware event has mass zero.
   The raw comparison event has mass 1/2, not inverse subset cardinality one;
   establish its connection to a genuine full-set minimum event. This is
   the consequential boundary for dropping membership.
6. With constant tied priorities on a two-member set, each member satisfies
   the non-strict minimum event on every sample, hence has mass one, not
   one-half. Retain this checked counterexample to dropping injectivity.

Other small examples are justified only by a concrete remaining semantic
risk or reuse argument. There is no example quota for private proof helpers.
An additional cyclic-ranking counterexample may show that uniform individual
priority marginals do not specify the full uniform law, but it is not needed
to close this bounded unit.

## Explicit remaining work

The expected number of labels preceding S, its actual count/indicator bridge,
and the one-based first-position corollary are separate follow-up scope.
For empty S the preceding count is the universe size, while count plus one
is a sentinel, not a first member's position. No such mean is claimed here.

Full induced relative-order uniformity, adaptive-subset and conditional
history laws, input-permutation/list orientation bridges, occurrence pivots,
quicksort's two recursive branches, treap construction/root/ancestor laws,
conditional depth and weighted charging, and actual source cost models
remain in their existing chapter or shared obligations. Uniform overlapping
minimum marginals do not imply independent restrictions. This unit closes
no algorithm complexity or chapter-coverage claim by itself.

## Statement review and acceptance

Inspect the actual public types and definitions, including membership,
fixed-subset quantifiers, the common law, sample/permutation orientation,
finite normalization, distinctness and all empty/tie boundaries. Keep
operations and laws separate with the minimal assumptions above. Reuse the
existing probability/resource interfaces without changing their semantics.

Use only the project's allowed axioms and pinned toolchain. No admission,
new axiom, unsafe/partial definition or proof-checking bypass is permitted.
Integrate examples through the normal public root and document the exact
source use and remaining work. Capture an immutable candidate and source
statement review, then perform focused compilation, the full applicable
guarded candidate build and exhaustive proof audit, both independent review
axes and immediate final candidate verification. Preserve every unresolved
finding. A source preflight, uncompiled draft or durability checkpoint is
not acceptance. Integrate only after repaired Chapter 1 and this unit have
both passed their gates.
