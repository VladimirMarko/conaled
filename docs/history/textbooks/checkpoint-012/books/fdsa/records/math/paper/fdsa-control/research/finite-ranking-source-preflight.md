# Finite-ranking minimum law: bounded source preflight

Prepared 2026-11-02. **Mathematical/source preparation, not implementation,
final review or acceptance.** This note coordinates with
**finite-ranking-api-preflight.md**. Existing chapter obligations and
requirements are unchanged; no new unit scope is frozen.

## 1. Minimum useful common statement

Let I be any finite type, P a linearly ordered type, and \(r:I\to P\)
a fixed injective assignment of priority labels. Sample \(\pi\) uniformly
from \(\operatorname{Perm}(I)\); key a receives priority \(r(\pi(a))\).
Smaller priorities come first. Fix a finite subset \(S\subseteq I\)
**before sampling**. For any \(a\in S\),

\[
\boxed{\Pr[\forall b\in S,\ r(\pi(a))\le r(\pi(b))]=1/|S|.}
\]

This is a minimum-member marginal under **one global ranking**.
The membership premise already implies nonemptiness. A definition with
\(a\in S\) as an event conjunct also gives outsiders mass zero; without
that conjunct an outsider's comparison event has a different meaning.

No order or measurable structure on I is needed. P needs its linear
order but no finiteness or measurable structure. The existing finite
uniform law uses the measurable permutation sample space. A public
finite-type hypothesis suffices; classical equality decisions and a
Fintype instance can be local to the proof. No ranking record, new
probability carrier, selector or executor is required.

The source-position specialization is \(I=\mathrm{Fin}(U)\),
\(r=\mathrm{id}\): \(\pi\) maps **key index to priority position**.
A position-to-key input-list permutation uses the inverse orientation.
The finite indexing need not follow the keys' BST/comparison order.

| Boundary | Required treatment |
|---|---|
| Empty I | Its permutation space is a singleton, but no member premise can hold. No global nonempty-I hypothesis is needed. |
| Empty S | There is no first member; the minimum-probability theorem has no instance. |
| Singleton S | Its member is first with probability 1, even with other keys present. |
| S is all of I | Each member is globally first with probability \(1/\lvert I\rvert\). |
| Outsider | In Fin2 with identity priorities, S={1} and a=0 give the raw comparison event probability 1/2, not 1. Membership must not be dropped. |
| Ties | Injectivity gives uniqueness. Arbitrary random scores with ties and deterministic tie-breaking are a different model. |
| Adaptive S | Choosing S after seeing the ranking does not inherit the fixed-subset law; its conditional distribution needs a separate proof. |

## 2. Source-faithful proof route

For each permutation, the nonempty finite image \((r\circ\pi)(S)\)
has one least priority, and injectivity identifies exactly one member
of S attaining it. Thus the minimum events indexed by S are disjoint
and cover the sample space.

For \(a,b\in S\), let \(\tau\) exchange a and b and fix all other
indices. It preserves S. The involution

\[
F(\pi)=\pi\circ\tau
\]

maps the a-minimum event bijectively onto the b-minimum event:
\(r(F(\pi)(b))=r(\pi(a))\), and \(\tau\) permutes the quantifier over
S. This includes a=b. Uniform finite measure assigns equal masses to
these fibers. Their disjoint union has mass 1, so \(|S|p=1\) and
\(p=1/|S|\), with positive finite normalization checked explicitly.

Equivalently, prove the cardinality identity
\(|\operatorname{Perm}(I)|=|S|\,|E_a|\) and use the existing uniform
cardinality ratio. Neither route needs a factorial formula, a general
group-action hierarchy, or full relative-order uniformity. The API
preflight records the pinned finite-minimum, swap, counting and
normalization lemmas. Replacing the supplied experiment by an
independent uniform draw from S would omit its joint-law connection.

## 3. Correlated-overlap example

Use one uniform permutation of Fin3 with identity priorities. Let
\(S=\{0,1\}\) and \(T=\{1,2\}\). The generic theorem gives

\[
\Pr[1\text{ first in }S]=1/2,\qquad
\Pr[1\text{ first in }T]=1/2.
\]

The intersection is exactly the event that 1 is first in
\(S\cup T=\{0,1,2\}\), hence has mass **1/3**, not 1/4.
An independent enumeration confirms that each marginal contains three
of the six rankings and the intersection contains two. A connected
example can invoke the public theorem for S, T and their union, then
prove the event identity; it need not rely solely on enumeration.

After a separate deterministic root/minimum bridge, these are uniform
but correlated treap roots. Both events must observe the same sampled
permutation; two independent subset rankings change the experiment.

## 4. Separate possible next layers

**Relative orders and histories.** Uniformity of the entire induced
ordering on a fixed subset is stronger than a first-member marginal.
Conditional remaining-order laws must state exactly what history was
revealed and normalize a positive-mass conditioning event. Neither is
proved by the unconditional minimum law. Disjoint-restriction
independence is another joint-law statement; expectation arguments may
need only conditional marginals. None is automatically first-unit scope.

**Expected number of preceding labels.** A small possible corollary,
still separately scoped, counts the labels strictly before every member:

\[
C(\pi)=|\{x\in I:\ \forall s\in S,\ r(\pi(x))<r(\pi(s))\}|.
\]

Members of S never contribute. For each \(x\notin S\), its indicator
is exactly the event that x is first in \(S\cup\{x\}\). The minimum
law and finite indicator linearity therefore give

\[
\mathbb E C=\frac{|I|-|S|}{|S|+1}.
\]

This uses no independence. It remains valid when S is empty: all labels
satisfy the vacuous predicate, so C is constantly \(|I|\). Cardinality
subtraction is safe because S is a subset of I.

For nonempty S, C+1 has the **one-based ordinal first-position** meaning
among all assigned priorities. In the Fin U identity-priority model,
a pointwise rank bridge gives
\(\mathbb E(C+1)=(U+1)/(|S|+1)\). It is not the expected raw priority
in an arbitrary ordered P. For empty S, C+1 is a sentinel U+1 and is
not a first member's position. This consequence needs no binomial-tail
counting or full restriction law, but its feasibility does not freeze
it into the initial unit.

## 5. Mapping to existing obligations

| Existing source obligation | Support from the proposed minimum law | Required later bridge |
|---|---|---|
| C02-024: average first-pivot quicksort on distinct keys | Uniform first key; fixed interval/subset minimum events for a possible comparison-indicator argument. | Input-permutation orientation, filtered-subproblem conditional laws, both recursive branches and exact source tariff. |
| C02-024: randomized occurrence pivots | A fixed subset minimum has the uniform-member marginal. | Coupling to fresh conditional occurrence choices requires history laws. Duplicates remain occurrences, not distinct values; the existing two-way sorter's quadratic duplicate counterexample remains. |
| C10-112 and C10-115: shared-priority treaps | Fixed operand minimum is uniform under the one global permutation; the overlap example retains correlation. | Finite-key construction and canonical treap/root semantics for both operands. |
| C10-117: expected join/set-operation work | Fixed-subset minimum events; optional preceding-count/position consequence supports the root-priority estimate. | Conditional depth, Jensen, cluster/weighted charging, actual work, constants and empty-input cases. |

Treap sets A and B are fixed before sampling on \(A\cup B\); shared keys
have shared priorities. Uniform individual numeric-priority marginals,
deterministic hashes or heap/BST invariants alone do not establish this
joint model. The lemma by itself discharges no algorithm complexity or
chapter-coverage claim. The prior probability preflight and chapter
inventories retain all remaining obligations.

### Saved primary evidence

Only already recovered sources were used; no new source campaign:

- FDSA July 27, 2026, p.16 and Chapter Notes p.125,
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
  SHA-256: `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
- AFP Quick_Sort_Cost dated archive,
  <https://isa-afp.org/release/afp-Quick_Sort_Cost-2026-10-26.tar.gz>.
  SHA-256: `cda7ed0a00991dcf8a5adff2d9909d6e761b2d8fb9501425ed8b93dbf462f457`.
  Exact correspondence boundaries are already in quicksort-average-proof-plan.md.
- Blelloch–Ferizovic–Sun, *Joinable Parallel Balanced Binary Trees*,
  DOI <https://doi.org/10.1145/3512769>, author copy
  <https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf>.
  SHA-256: `c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`.
  Shared priorities: pp.7:4–5; root-priority estimate: p.7:25;
  expected bulk-work target: Theorem 9, p.7:24.

Only this requested research note was written. No compiler, project
hash helper, Git, cache, gate, repository source, ticket, requirement or
acceptance state was changed.
