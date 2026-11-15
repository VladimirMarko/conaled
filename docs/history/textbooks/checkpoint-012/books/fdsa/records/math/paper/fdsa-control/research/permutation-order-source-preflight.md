# Full fixed-subset order: bounded mathematical/source preflight

Prepared 2026-11-02. **Preparation only: no implementation, frozen new scope,
chapter activation, validation or acceptance.** The parent reports the prior
minimum-law draft at `ff3dd88082c6283df40bcd86a4363841a0360b12`, saved in
checkpoint 0016. This assessment does not validate that draft.

## 1. Smallest useful complete-order statement

Fix an ordinary list `positions : List I` that is **Nodup and complete**:
every index occurs in it. It enumerates priority-label indices in the chosen
order. Fix a finset S before drawing a uniform `π : Equiv.Perm I`, where π
maps a key to its assigned label index. Use the ordinary list expressions

```text
globalOrder π = positions.map π.symm
restrictedOrder S π = (globalOrder π).filter membership_S
baseOrder S = positions.filter membership_S
outcomes S = (baseOrder S).permutations.toFinset
```

Here `membership_S` is the usual Boolean membership decision. The target is
the actual pushforward equality

```text
(uniformOn Set.univ).map (restrictedOrder S)
  = uniformOn (outcomes S : Set (List I)).
```

No order on I is needed. The complete list supplies finiteness locally; an
additional public `Finite I` or nonempty-I premise is mathematically redundant.
Ordinary equality decisions suffice for filtering and finite support. Explicit
measurable structures with measurable singletons on the permutation and List I
sample spaces support the probability argument. Finite input makes the map
measurable; finite target support permits equality from singleton masses.
No new global instance, ranking carrier, selector or executor is justified.

Defining a fresh uniform draw from `outcomes S` would assert the answer without
connecting it to the supplied global experiment.

## 2. Deterministic semantics and orientation

For each π, `globalOrder π` is complete and Nodup: the key assigned label
`positions[j]` is `π.symm (positions[j])`. Equivalently, a key's position in
the global list is the position of its label `π a` in positions. Filtering
preserves relative order, contains each member of S exactly once and no
outsider, and has length `S.card`. Thus `restrictedOrder S π` is a `List.Perm`
of `baseOrder S` and belongs to the target support. These pointwise facts
accompany the distribution statement.

The inverse is consequential. With positions `[0,1,2]` and key-to-label
permutation `(1,2,0)`, the ordered keys are `[2,0,1]`. Restriction to `{0,1}`
gives `[0,1]`; mapping by π directly gives `[1,0]`. Both direct and inverse
maps have uniform marginals under uniform π, so a distribution-only check
cannot detect this source-orientation error.

An arbitrary enumeration orders **labels**, not arbitrary numeric priorities.
For the earlier assignment `priority = [-7,100,4]`, increasing numeric priority
requires positions `[0,2,1]`. At identity π, positions `[0,1,2]` gives a
different pointwise order. Any fixed complete enumeration yields the uniform
list law, but matching a concrete priority order needs this sorted-enumeration
bridge. No mean numeric priority or algorithm cost follows.

## 3. Equal-fiber proof of the actual pushforward

Two target lists xs and ys are Nodup, have equal length and have the same
support S. Match their entries position by position. This finite injective
correspondence extends to a global permutation σ with `xs.map σ = ys`.
Their common support forces σ to map S onto S; fixing its complement
pointwise is unnecessary. The API contributor found the existing
`Equiv.Perm.exists_extending_pair` for the extension, avoiding a new framework.

Use the sample bijection

\[
F(\pi)=\pi\circ\sigma^{-1}.
\]

Its inverse ranking is \(\sigma\circ\pi^{-1}\). Preservation of S gives

\[
\operatorname{restrictedOrder}(S,F(\pi))
=\operatorname{map}(\sigma,\operatorname{restrictedOrder}(S,\pi)).
\]

Thus F bijects the fiber of xs with the fiber of ys, and uniform finite
measure gives them equal mass. The fibers indexed by the finite target are
disjoint and cover every global sample. The target contains `baseOrder S`,
so is nonempty. Normalize their equal masses to the reciprocal of its
cardinality. Off-support fibers are empty. Finite summation over intersections
with the target proves the stated `Measure.map` equality.

No factorial or interleaving formula is required. Nor does this infer whole
orders from the old minimum marginals. The saved arithmetic gives a useful
separation: uniform sampling of the twelve even permutations on four labels
has every fixed-subset member minimum marginal, while full orders have mass
1/12 or zero instead of 1/24. That different law is not a counterexample to
the proposed theorem under the full uniform-permutation assumption.

## 4. Boundaries and distribution examples

| Case | Exact interpretation |
|---|---|
| Empty S | The output is always `[]`; the target is the singleton `{[]}`, not empty. Its law has mass one. |
| Empty I | Positions is `[]`; the identity permutation still exists and both laws normalize. |
| Singleton S | Its one-member list is the only output. |
| Full S | Every permutation of positions is the complete ordered key list for exactly one global sample. |
| Arbitrary complete enumeration | It changes pointwise label order while preserving the uniform list law; numeric-priority agreement needs the bridge above. |

The retained independent calculations are in
[permutation-order-calculations.json](permutation-order-calculations.json),
SHA-256 `54163e6729373a9c78cd82432d48ae827498321c64e53e3c5160cebb54ca2f80`.
Their identity was checked by ordinary read-only SHA-256. The report records
all 50,363 permutation/subset pairs through universe size six; the arithmetic
was read, not rerun or treated as formal validation.

A whole-list example uses four labels and S=`{0,2,3}`. Each of its six orders
has four of the 24 global samples and mass 1/6. In particular, `[0,2,3]`
and `[0,3,2]` share their first member but are distinct outcomes with separate
one-sixth masses. A later connected example can derive those masses through
the pushforward theorem and its actual list projection, rather than only
the earlier minimum result.

Overlapping observations must retain one common π. For three labels, their
joint orders on S=`{0,1}` and T=`{1,2}` are:

| S order | T order | Joint mass |
|---|---|---|
| `[0,1]` | `[1,2]` | 1/6 |
| `[0,1]` | `[2,1]` | 1/3 |
| `[1,0]` | `[1,2]` | 1/3 |
| `[1,0]` | `[2,1]` | 1/6 |

Each marginal order has mass 1/2, but the joint is not the independent product
1/4. Conditioning on “1 precedes 2”, an event of mass 1/2, gives S-order
probabilities 1/3 and 2/3. Even a fixed subset's unconditional law therefore
does not give its law after arbitrary observations.

Adaptivity also matters. Choose S to contain 0 and whichever of 1 or 2 is
earlier in the sampled order. S always has two members and contains 0, but
0 is first in S exactly when it is globally first: probability 1/3, not the
fixed-subset 1/2. These are preparation cases and scope boundaries, not newly
frozen implementation requirements.

## 5. Source use and limited handoff

The prior [probability preflight](probability-source-preflight.md),
[minimum-law source note](finite-ranking-source-preflight.md), and
[quicksort proof plan](quicksort-average-proof-plan.md) retain exact C02/C10
scope, primary-source pins and cost distinctions. This note does not reaudit
or alter them. The parallel API assessment is
[permutation-order-api-preflight.md](permutation-order-api-preflight.md).

For C02-024, the actual filtered-list observation is shared groundwork. It
does not justify conditional subproblem laws after a revealed pivot, equivalence
to fresh occurrence choices, or the two recursive costs. The saved AFP
`Quick_Sort_Average_Case.thy` uses `random_permutation_of_set` and
`partition_random_permutations` for further decomposition and pair-law steps;
this fixed-subset theorem does not silently supply all of them.

For C10-115 and C10-117, fixed operands can observe uniform relative orders
under one common priority assignment while preserving overlap correlation.
Canonical treap/root/ancestor bridges, histories, weighted charging and observed
work remain separate. Full disjoint-restriction independence and specialized
conditional laws may be useful later, but are not required to prove this
single fixed-subset pushforward. Source models and chapter obligations remain
unchanged.

Only this requested research note was written. No compiler, Git command,
project hash helper, cache, gate, repository source, tracker, frozen requirement
or acceptance state was changed.
