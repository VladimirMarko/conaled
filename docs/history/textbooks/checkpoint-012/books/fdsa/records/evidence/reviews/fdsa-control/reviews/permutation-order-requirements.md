# Shared fixed-subset ordering requirements

Recorded 2026-11-02 before implementation. This is FDSA-XU02, a bounded
cross-cutting unit under the user's explicit exception for shared concerns.
The governing request is `../REQUEST.md`. Chapter 1 is still active; no
chapter is accepted or activated by this unit.

## Origin, baseline and scope

The actual relative ordering induced on a fixed subset supports existing
Chapter 2 and Chapter 10 obligations. The preceding minimum law describes
only a member's first-position event; it does not specify a whole output
list or its joint meaning. The preparation for this next unit is:

- `../research/permutation-order-api-preflight.md`, SHA-256
  `3e18c4f3eb1d47b8335c270aee311eecc3817e4af0edac69232678efd85c4294`.
- `../research/permutation-order-source-preflight.md`, SHA-256
  `53cd24c2bf07945facb04f0249baf0fc52a64bf498466185d7d528488f7214bd`.
- `../research/permutation-order-calculations.json`, SHA-256
  `54163e6729373a9c78cd82432d48ae827498321c64e53e3c5160cebb54ca2f80`.

The calculation file includes exploratory conditional/adaptive and even-law
boundaries. They are not automatically formal requirements of this bounded
unit. Existing chapter requirements and source inventories remain unchanged.

Use an isolated development worktree `conaled-permutation-order`, branch
`work/fdsa-permutation-order`, starting at the committed minimum-law draft
`ff3dd88082c6283df40bcd86a4363841a0360b12`. Record its clean starting state
before source edits. Its parent chain includes the unvalidated Chapter 1
repair; no base in this chain is an accepted dependency. Keep separate
project output directories, sharing only the unchanged pinned dependency
packages. Do not alter the active old Chapter 1 validation checkout, run
another compiler while that gate is active, or change toolchain/checker
configuration. Preserve an explicitly uncompiled source draft until matching
validation can run.

Reuse ordinary lists, finsets, permutations, Mathlib measures and their
standard maps. No new ranking datatype, probability carrier, random
executor, selector, group-action instance or general probability framework
is justified. The existing Table/kernel/resource semantics remain unchanged.
Suggested modules are `Applications/Probability/PermutationOrder.lean`,
`Examples/PermutationOrder.lean` and a separate boundary example if useful.
Names and private helper placement are routine implementation choices.

## Observation and deterministic contracts

Let I be any index type with decidable equality. Fix an ordinary list
`positions : List I` giving a chosen order of the priority-label indices.
The sampled permutation π maps a key index to its assigned label. Define

`restrictedOrder positions S π :=
  (positions.map π.symm).filter (fun a => decide (a ∈ S))`

for a finset S. The inverse is part of the intended semantics: label
`positions[j]` belongs to key `π.symm (positions[j])`. The definition needs
no completeness, Nodup, finiteness, inhabitance, order or measurable
structure. Its equality decision serves the actual computational filtering.

Establish the following value laws with only their needed hypotheses:

1. General membership:
   `a ∈ restrictedOrder positions S π ↔ π a ∈ positions ∧ a ∈ S`.
   Under `hcomplete : ∀ a, a ∈ positions`, specialize to membership in S
   and derive that the output's `toFinset` equals S.
2. If `positions.Nodup`, the output is Nodup. With completeness as well,
   its length is S.card and it is a `List.Perm` of
   `positions.filter (fun a => decide (a ∈ S))`.
3. The pointwise order bridge
   `(restrictedOrder positions S π).map π <+ positions`, with no
   completeness, Nodup or probability hypothesis. This establishes the
   ordering relative to the supplied label enumeration.
4. Filtering the output again to T equals restriction to `S ∩ T`.
   If `T ⊆ S`, it equals `restrictedOrder positions T π`. These are
   deterministic composition laws, not conditional probability claims.

Use the existing finite target

`orders := (positions.filter (fun a => decide (a ∈ S))).permutations.toFinset`.

This may be a named ordinary finset or an expression; no support record is
needed. Under completeness and Nodup, identify membership in orders with
the corresponding `List.Perm` proposition, prove that every projection lands
there, and derive `orders.card = S.card!` using existing list-permutation
cardinality results. Its support is nonempty even when S is empty.

An arbitrary complete enumeration orders labels. It does not automatically
sort an independently supplied numeric priority function. Source callers
must provide a matching enumeration or establish their own order bridge.
Do not add an unnecessary LinearOrder I or priority datatype to this unit.

## Whole-output probability and pushforward

Under `positions.Nodup`, `∀ a, a ∈ positions`, and existing measurable-space
and measurable-singleton instances on `Equiv.Perm I`, prove the universal
output-fiber formula for every fixed S and output list xs:

`uniformOn Set.univ {π | restrictedOrder positions S π = xs}
  = if xs ∈ orders then (S.card! : ℝ≥0∞)⁻¹ else 0`.

The reciprocal is in ENNReal, not natural division. An equivalent supported
case plus off-support zero theorem is acceptable if the complete formula is
also exposed or immediately derived. This is a probability under the actual
global uniform permutation law; defining an independent uniform subset
sample does not establish it.

Completeness supplies a local `Fintype.ofList`. Do not require an additional
public Finite/Fintype I or nonempty I hypothesis. No measurable space on I
or List I belongs on this source-event theorem. Each finite source fiber is
measurable from the explicit permutation sample-space assumptions.

Then add the semantic corollary, with an existing measurable space and
measurable singletons on `List I`:

`(uniformOn Set.univ).map (restrictedOrder positions S)
  = uniformOn (orders : Set (List I))`.

This is equality of the supplied measures. Use ordinary `Measure.map`, its
measurability conditions and the existing finite/countable extensionality
APIs. A finite I makes List I countable, not finite in general. Do not add
new global measurable-space instances on lists or permutations. Concrete
examples may choose local discrete measurable spaces.

The expected proof extends the positionwise correspondence between two
supported Nodup lists to a permutation σ using existing finite-extension
machinery. Their common support implies that σ preserves S. The bijection
`π ↦ π * σ.symm` transports one whole-output fiber to the other. Equal
fiber masses normalize over the finite complete output support. Fixing
the complement pointwise, a factorial quotient for individual fiber sizes,
and a public action/equal-fiber framework are unnecessary. These proof
choices explain feasibility; a different sound proof of the same actual
law is acceptable.

## Connected cases and independent expectations

Grow these cases alongside the public results. The saved exact calculations
are preparation only and must not be reported as kernel validation.

### Whole lists and composition

Use Fin 4, positions `[0,1,2,3]`, and S=`{0,2,3}`. Its six whole output
orders have mass 1/6 each. Retain at least two distinct three-element orders
with the same first key, such as `[0,2,3]` and `[0,3,2]`, and derive their
masses through the new whole-order result. This makes the extra content
beyond a minimum event explicit. Exercise the Measure.map equality through
a concrete semantic specialization and at least one resulting observation.

Retain an invalid repeated or wrong-support output with mass zero, through
the generic off-support result. Prove an actual nested-filter composition:
filter the S output again to T=`{0,3}`, connect it pointwise to the T
projection, and derive an ordered-pair probability of 1/2 through the
generic law. The two restrictions must observe the same π. Do not infer
conditioning or independence from the composition law.

Include singleton and full-universe specializations. They may reuse these
examples: a singleton has its sole one-member list with mass one; a full
Fin 4 order has mass 1/24.

### Consequential boundaries

- Empty S gives the sole output `[]` with mass one, not an empty target
  measure. Include an empty index type with positions `[]` and use the
  new generic law; no `Nonempty I` premise may be introduced.
- On Fin 3, positions `[0,1,2]`, choose the key-to-label cycle `(1,2,0)`
  and S=`{0,1}`. The inverse global key list is `[2,0,1]`; the correct
  restricted order is `[0,1]`. Directly mapping π and filtering instead
  gives `[1,0]`. Retain this checked pointwise distinction. Uniform
  marginal distributions alone cannot detect this orientation error.
- To distinguish label order from arbitrary numeric priority values,
  use the earlier values `-7,100,4` with positions `[0,2,1]`. At identity
  π the full output follows increasing numeric priority, while positions
  `[0,1,2]` have a different pointwise order. A small concrete value/order
  check is sufficient; no numeric expectation theorem is in scope.
- Incomplete positions `[0]` on Fin 2, S=`{0}`, under the swap produce
  `[]`, outside the permutations of base `[0]`. This disproves the
  unconditional support claim if completeness were removed.
- Complete repeated positions `[0,0,1]` on Fin 2, S full, under the swap
  produce `[1,1,0]`, outside the permutations of base `[0,0,1]`.
  Retain this counterexample to removing Nodup from the support claim.

The existing minimum-law overlap example already establishes a consequential
shared-law correlation. Do not expand this unit merely to formalize every
exploratory conditional, adaptive or even-permutation counterexample.

## Remaining scope and acceptance

Fixed-subset uniformity is not an arbitrary conditional-history theorem.
Recursive pivot/subproblem laws, equivalence to fresh occurrence choices,
joint disjoint-restriction laws, adaptive subsets, source list/algorithm
correspondences, treap root/ancestor/charging arguments and actual work
remain in their existing chapter/shared obligations. Expected preceding
counts and first-position means are separate scope. No independence,
runtime or algorithm-complexity conclusion is claimed here.

Perform statement review of the pointwise inverse orientation, exact list
equality versus permutation, completeness/Nodup assumptions, common law,
fixed-subset quantifiers, empty support, factorial normalization, finite
versus countable spaces, map measurability and actual theorem connections.
Keep operations, semantic observations and probability laws separate.

Use only allowed project axioms and the pinned environment. No admission,
new axiom, unsafe/partial definition or proof-checking bypass is permitted.
Integrate the examples through the public root and provide concise source-use
documentation. Capture an immutable candidate with these requirements kept
outside its diff. Focused compilation, the applicable full guarded candidate
build and exhaustive audit, both independent final axes and immediate
candidate verification remain mandatory. Preserve unresolved findings.
No preflight, source draft or recovery checkpoint supplies acceptance credit.
Integration depends on acceptance of the repaired Chapter 1 and prior
minimum-law base as well as this unit's own gates.
