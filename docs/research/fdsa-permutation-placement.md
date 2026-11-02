# Fixed-subset placement and internal order

Status: **source draft, not compiled or accepted**. Local FDSA-XU06 retains the
exact frozen requirements, preparation, source identities and later validation.
This unit uses the existing [order](fdsa-permutation-order.md) and
[count/expectation](fdsa-permutation-expectation.md) observations. It accepts no
chapter or algorithm obligation.

## The two actual observations

Fix a complete Nodup list of labels, a subset A and a priority function.
A permutation π sends each key to its assigned label. The existing observation

    O π = restrictedOrder positions A π

reads the inverse permutation in the supplied label order and retains A.
The existing aggregate

    B π = beforeCount priority A π

counts all keys whose assigned priority precedes every selected key's priority.
Its Set.ncard definition gives zero for an infinite counted set. Complete
positions supplies finiteness locally for the probability statements.

The new result concerns the joint relationship of these same two observations.
Their separate marginal statements do not determine their joint law.
The unit introduces no count over a second selected set and no new sampler.

## An invariant event is split equally among supported orders

Let μ0 be the existing uniform measure on all permutations of I. Suppose E is
unchanged by every right relabeling π ↦ π * σ.symm for which σ preserves A
setwise. The new PermutationOrder.uniformOn_inter_restrictedOrder_eq states

    μ0 (E ∩ {π | O π = xs}) =
      if xs ∈ orders positions A then μ0 E / A.card! else 0.

This is an unnormalized event identity. Its only denominator is the positive
finite factorial, including 0!=1. E may have mass zero and A may be empty.
The scalar statement requires measurable structure and measurable singletons
only on the permutation sample; all of its subsets are measurable because it
is finite. It adds no public finite enumeration, inhabited identifier,
identifier order, measurable priority space or list measurable space.

The proof stays in the existing order module and reuses its private
list-extension and relabeling witnesses. The sample translation gives a
bijection between the E-sliced fibers of any two supported lists. Their
finite partition is calculated with μ0.restrict E, whose total is μ0 E.
The existing support cardinality identifies the number of equal slices.
No event-mass cancellation or new probability carrier is involved.

PermutationExpectation.beforeCount_relabel establishes the concrete
observation invariance. Its defining counted set after relabeling is the
inverse image of the old set under σ.symm, which preserves Set.ncard.
The theorem needs only LT P and setwise preservation of A. It retains the
infinite-set convention and requires no probability law.

The chosen σ can move keys outside A. It can therefore change which named
outside key precedes A while preserving how many do. No individual outside-key
invariance is asserted.

## Independence under a current full global law

PermutationPlacement.indepFun_beforeCount_restrictedOrder has the premise

    hΠ : HasLaw Π (uniformOn (Set.univ : Set (Equiv.Perm I))) μ

for an actual observation Π on an arbitrary measurable environment Ω. It
concludes the existing Mathlib IndepFun predicate for

    (fun ω => B (Π ω))    and    (fun ω => O (Π ω))

under that same μ. Taking Π=id and HasLaw.id recovers the canonical sample.

Every event determined by B is invariant under the established relabeling.
Summing the new sliced probabilities over supported orders in an arbitrary
list event proves the canonical independence criterion. HasLaw.measure_eq
then transports the intersection and both marginals to the actual environment.
The proof never assumes independence from the two marginals alone.

Ω need not be finite or countable, and Π need only have the a.e. measurability
already supplied by HasLaw. A source probability instance is unnecessary in
the public assumptions. The independence statement names a caller's measurable
space on List I but does not require its measurable-singleton class.

The priority comparison still needs only LT P. Under such a raw relation,
a key can precede itself, so B can include members of A. The lawful
outside-key interpretation and existing complement bound use irreflexivity.
The explicit expectation additionally requires injective linear priorities.

## Weighted means and genuine integrability

For an injective priority function into a linear order, put

    c = ((Nat.card I - A.card : Nat) : Real) / ((A.card + 1 : Nat) : Real).

The subtraction is natural subtraction before casting, as in XU04.
For every fixed g : List I → Real, integral_beforeCount_mul_order states

    ∫ ω, (B (Π ω) : Real) * g (O (Π ω)) ∂μ
      = c * ∫ ω, g (O (Π ω)) ∂μ.

The proof combines the new independence with the old actual count mean.
It permits signed g and does not impose a global bound on unsupported lists.
The actual count, order weight and their product are genuinely integrable
on the finite canonical permutation sample. A private proof bundles the
three integrability facts transported through hΠ with the resulting identity.
The scalar public statement requires no measurable structure on lists:
a local discrete instance suffices for the composition proof.

lintegral_beforeCount_mul_order gives the corresponding ENNReal statement.
Its weights may be infinite, with the existing convention 0 * ∞ = 0.
The real theorem has its own integrability proof; it is not obtained by
discarding infinite values in a conversion.

The exact factorization supports coefficient bounds when the expected weight
is nonnegative. Nonnegativity on the actual finite order support suffices.
Count-plus-one follows through ordinary integration. Identifying that quantity
with an actual first ordinal position additionally uses a rank equivalence,
nonempty A, and the existing finite-image minimum bridge. Neither a general
numeric-priority minimum nor an arbitrary random work weight is identified
with these observations without its own value theorem.

## Conditional consequences preserve different information

The examples use existing conditional probability APIs:

| Positive conditioning event | Preserved observation | Observation that may change |
| --- | --- | --- |
| A predicate of this same fixed internal order O | The full distribution of B | The order O and the whole global permutation law |
| An event invariant under A-preserving relabelings, including a predicate of B | The uniform internal-order distribution | The count distribution and its mean |

The positivity requirement belongs to normalized conditional consequences.
The unnormalized fiber law also covers null E. Conditioning on a null event
gives the existing zero measure, with no normalized law claim.

Neither direction resets the whole environment to its original global law.
A uniform selected-order marginal under a changed measure is insufficient
for the global HasLaw premise above.

## Connected source examples

The main Fin3 fixture reuses the actual selected set {0,1}, identity ranks and
global law from Examples.PermutationExpectation. With positions [0,1,2], its
count is 0 with probability 2/3 and 1 with probability 1/3. Its two supported
orders each have probability 1/2. The new event theorem supplies the actual
joint table:

| Order | Count 0 | Count 1 |
| --- | ---: | ---: |
| [0,1] | 1/3 | 1/6 |
| [1,0] | 1/3 | 1/6 |

Giving those two orders weights 2 and 5 yields mean weight 7/2 and weighted
count mean 7/6 through the new public result. The existing first-position
value bridge then gives weighted ordinal mean 14/3. Signed-weight and
nonnegative coefficient-bound uses keep their distinct premises explicit.

Conditioning on order [0,1] retains the two count probabilities. Conditioning
on count 1 retains the two order probabilities while changing the count mean
to 1. Unsupported [0,0], impossible count 2 and empty-event cases retain zero
mass without positive-event normalization.

The boundary module connects the new laws to empty/full/singleton/tied
subsets, the Empty identifier type, a bare always-true comparison relation,
an infinite ENNReal weight and arbitrary-environment law transport with actual
product integrability. A two-atom law on the actual identity and swap-0-2
permutations has a uniform nonconstant internal-order marginal, but a joint
cell of mass 1/2 versus marginal product 1/4.

Two earlier boundaries remain: an unrelated global-head conditioning changes
a singleton's count mean while its constant order law stays the same, and an
adaptive minimum-selected singleton has zero count. The former refutes mean
transfer, not independence from a constant order. Finally, taking the original
Fin3 count itself as a random weight yields E[B²]=1/3 versus E[B]²=1/9; a
placement-dependent work quantity cannot be treated as an order-only g.

These are source-written statements and connections pending compilation.
Independent arithmetic and source readings do not provide kernel validation.

## Source use and remaining obligations

The book source remains the July 27, 2026 edition of
[*Functional Data Structures and Algorithms: A Proof Assistant Approach*](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645.
The retained source assessment relates the fixed-set weighted method to the
treap discussion and the corresponding analysis in
[*Joinable Parallel Balanced Binary Trees*](https://doi.org/10.1145/3512769),
whose pinned local PDF hash is
c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057.

An actual treap client still has to identify its priority order, shape/work
weight and placement variable, and justify the law under its current history.
The retained ancestor-conditioning counterfamily prevents assuming a uniform
global environment at every recursive call. The separate conditional
frontier, path-charge and weighted layer arguments, actual join2 recurrences
and C10-117 remain open. The optional stronger complement-fixing symmetry and
another Fin5 conditional-filter example are not prerequisites for this unit.

The saved Chapter 2 mean route uses conditional child marginals and genuine
integrability; XU06 does not become its prerequisite. Algorithm/pivot/partition,
occurrence, duplicate-bearing and source-cost obligations stay with that
chapter. All existing chapter and appendix scopes remain unchanged.

The immutable candidate must still pass focused compilation, the full guarded
build and exhaustive audit, both independent final review axes, and immediate
candidate verification. Accepted repaired Chapter 1 and the inherited shared
bases remain prerequisites. A source checkpoint does not grant acceptance.
