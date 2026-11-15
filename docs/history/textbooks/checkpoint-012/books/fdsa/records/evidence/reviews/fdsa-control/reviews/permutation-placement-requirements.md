# Shared fixed-placement and internal-order requirements

Recorded 2026-11-02 before implementation. This is FDSA-XU06, a bounded
shared probability unit under the user's cross-cutting exception. The
governing request remains ../REQUEST.md. Chapter 1 remains active; no chapter,
appendix or shared unit is accepted. Earlier requirements, source inventories,
findings and the Chapter 2-first integration plan remain unchanged.

## Preparation, placement and clean baseline

Root read the complete retained placement plan, its separate source assessment,
the current order/count modules, and all three new bounded reports before this
freeze. Retained inputs:

- ../research/permutation-placement-order-preflight.md, SHA-256
  3fe9a8d80a6a57faa4265ecb85267216039dae9f39164cf928560c1bae9cba81.
- ../reviews/permutation-placement-order-source-preflight.md, the retained
  independent assessment of that proposal.
- ../research/permutation-placement-unit-source-preflight.md, 22,902 bytes,
  SHA-256 5af7d39d56cf0e9766074ab720b79781b2f118480bff3696c7b9692e5efc662d.
- ../research/permutation-placement-unit-api-preflight.md, 29,445 bytes,
  SHA-256 fc7cf3773a3ddec7cda27f29662541fd41003b89a6ca7176497834c386642fe5.
- ../research/permutation-placement-unit-case-preflight.md, 25,425 bytes,
  SHA-256 93d3a60b2b92c62f1bef86d047efe9f767d2e4dea41eb611266620a800aa1877.

Use isolated checkout conaled-permutation-placement, branch
work/fdsa-permutation-placement, starting at saved joint-order draft
a5341221bd3e28d76e3b8ad2bc1683a74621ad5e. Its clean starting state is recorded
in permutation-placement-start.json. Only unchanged pinned dependency packages
are linked; project outputs are separate. All inherited drafts are unaccepted.
No second compiler, project checker or project hash helper may run while old
Chapter 1 gate 80227 is active. Do not alter that gate, source or configuration.
The initial deliverable is an explicitly uncompiled source draft.

Use the existing aggregate beforeCount, ordinary permutations, sets/finsets,
lists, HasLaw, IndepFun and integral APIs. There is no new selected-outsider-set
count, sampler, executor, law wrapper, independence predicate, group-action
framework or shuffle representation. The current symmetry may move named
outside keys; it preserves their aggregate count, not individual observations.

Extend PermutationOrder with one semantic event-fiber law beside its existing
private relabeling machinery; retain the old public statements and proof
bodies. Add one deterministic observation law to PermutationExpectation.
Create Applications/Probability/PermutationPlacement.lean for the concrete
joint/integration client. Its direct imports are the existing order/count
modules and relevant Mathlib independence/integration APIs. Do not import
PermutationTail into the order or placement core, expose private extension
witnesses, or duplicate the list-extension argument in another module.

## Actual invariant-event fiber law

For I : Type u, retain DecidableEq I, complete Nodup positions : List I,
and one fixed A : Finset I. Write O for the existing restrictedOrder positions A
and μ0 for uniformOn (Set.univ : Set (Equiv.Perm I)). For E a set of samples,
assume precisely:

    hInvariant : ∀ (σ : Equiv.Perm I),
      (∀ a, σ a ∈ A ↔ a ∈ A) →
      ∀ π, (π * σ.symm ∈ E ↔ π ∈ E)

Prove, for every xs:

    μ0 (E ∩ {π | restrictedOrder positions A π = xs}) =
      if xs ∈ orders positions A
      then μ0 E / (Nat.factorial A.card : ℝ≥0∞)
      else 0

Public call:

    uniformOn_inter_restrictedOrder_eq
      positions hnd hcomplete A E hInvariant xs

The scalar statement needs measurable-space/singleton instances only on the
permutation space. It needs no measurable structure on lists, identifiers or
priorities, no separate MeasurableSet E, no public Fintype/Finite I, key order,
inhabited index, positive event mass or nonempty A. Completeness supplies the
local finite enumeration. Even Empty has its identity permutation.

Use the existing private A-preserving witness and actual right multiplication
π ↦ π * σ.symm to biject E-sliced fibers. Normalize their actual finite
partition by orders_card = A.card!. The factorial is positive and finite
including at A empty. Never cancel μ0 E: zero events are required. Unsupported
lists have empty fibers. A small new private equal-slice lemma is allowed;
old proof bodies need not change.

## Deterministic count transport and current-law independence

For independent priority universe P : Type v, only LT P, fixed priority : I → P,
A, π and σ, prove:

    beforeCount priority A (π * σ.symm) = beforeCount priority A π

under hA : ∀ a, σ a ∈ A ↔ a ∈ A. Public call:

    beforeCount_relabel priority A π σ hA

This theorem in the existing expectation namespace needs no finite type,
DecidableEq I, injectivity, order laws or measurable structure. Reindex the
universal comparisons to show that the defining set is the inverse image under
σ.symm, then reuse the existing Set.ncard bijection law. Preserve the infinite
set convention. Under bare LT the count may include members of A; exclusion
uses irreflexivity, as in the existing preorder bound.

In the new PermutationPlacement namespace, expose one generic independence
theorem, without a redundant public canonical wrapper:

    indepFun_beforeCount_restrictedOrder
      positions hnd hcomplete priority A hΠ

For independent Ω : Type w with a measurable space, current μ : Measure Ω and
Π : Ω → Equiv.Perm I, hΠ is exactly:

    HasLaw Π (uniformOn (Set.univ : Set (Equiv.Perm I))) μ

The conclusion is the existing predicate:

    IndepFun
      (fun ω => beforeCount priority A (Π ω))
      (fun ω => restrictedOrder positions A (Π ω)) μ

Keep only LT P, the ordinary complete positions/DecidableEq I interface,
the permutation measurable-space/singleton pair, and a caller-supplied
measurable space on List I. Do not require list measurable singletons,
finite/countable/discrete Ω, a source probability instance, Measurable Π,
priority measurability, injective priorities or nonempty A.

First derive canonical independence from invariant count events and the finite
sum over supported orders. A private canonical lemma is appropriate. Transfer
the actual intersection and both marginals through HasLaw.measure_eq; do not
replace Π by a separately drawn permutation. HasLaw supplies only the required
a.e. measurability. The public specialization Π=id, hΠ=HasLaw.id recovers μ0.

## Exact weighted source application

Expose exactly these two further public calls in PermutationPlacement:

    lintegral_beforeCount_mul_order
      positions hnd hcomplete priority hinj A g hΠ
    integral_beforeCount_mul_order
      positions hnd hcomplete priority hinj A g hΠ

The first has g : List I → ℝ≥0∞ and the second g : List I → ℝ. Both add
LinearOrder P and hinj : Function.Injective priority, retain the same complete
positions and full-global HasLaw premise, and conclude:

    ∫ ω, (beforeCount priority A (Π ω)) * g (restrictedOrder positions A (Π ω)) ∂μ
      = ((Nat.card I - A.card) / (A.card + 1))
          * ∫ ω, g (restrictedOrder positions A (Π ω)) ∂μ

Use the correctly typed lower integral and ENNReal casts in the first and real
integral/casts in the second. Nat subtraction occurs before casting, as in XU04.
These scalar statements need no public measurable structure on List I and no
measurability or bound premise on g. A local discrete list space, local finite I,
and ordinary measurable composition suffice. No priority/index space is needed.

Combine the new independence with the existing actual count mean, not a new
assumed joint law. Prove genuine real integrability of the canonical count,
actual order weight and product, and transport it through hΠ to arbitrary Ω.
A private proof bundling those integrability facts with the identity is allowed;
do not rely on a nonintegrable integral's default zero value. The real equality
permits signed weights. ENNReal permits infinite weights, including 0 * ∞ = 0;
do not obtain the real result by a toReal step that ignores infinity.

The un-substituted product identity, coefficient upper-bound inequality,
count-plus-one and conditional consequences use existing APIs in Examples.
No additional public aliases, product-measure wrapper, generic expectation
framework or public conditional theorem is part of this first unit.

## Connected cases and independent expectations

Develop the theory and its actual clients together. The mathematical gap is the
missing joint/count-order connection: the old mean and marginal order law do not
supply independence. No artificial compiler failure is required or claimed.
Use public laws in the derivations; arithmetic about unrelated samples or
surrogate definitions is insufficient. Reuse the saved finite calculations and
existing expectation/joint/boundary fixtures; do not rerun an exhaustive campaign.

### Fin3 actual joint, weights and ordinal bridge

Use the existing Examples.PermutationExpectation.selected = {0,1}, rank3 and
law3, with complete positions [0,1,2] and the actual restrictedOrder. Retain
and connect the actual count distribution: 0 has mass 2/3, 1 has mass 1/3.
The count is at most 1; its existing mean can identify its indicator mass.
Each supported order [0,1] and [1,0] has mass 1/2 through XU02.

Through the new invariant-event law derive all four joint cells: count 0 with
either order has mass 1/3; count 1 with either has mass 1/6. Include the new
IndepFun specialization for these same observations.

Define the fixed real order weight to be 2 at [0,1] and 5 otherwise. Its actual
mean is 7/2. Use the new real weighted theorem to derive mean product 7/6.
Use the existing first_position_bridge, ordinary integration and that product
result to derive mean firstPosition3 * weight = 14/3. The ordinal is the actual
finite-image minimum, not a new count-defined surrogate. Exercise the ENNReal
weighted theorem with the same positive values or a useful infinite boundary.

Retain signed-real equality with a simple negative order weight and a concrete
coefficient-bound application with justified nonnegativity on supported orders.
The bound is an existing multiplication/integration consequence, not a new
public core wrapper. For the placement-dependent weight W=count, prove that
E[count * W] = 1/3 whereas E[count] E[W] = 1/9. This refutes removing the
order-only-weight premise.

### Both conditional directions and null boundaries

For H={actual order=[0,1]}, mass 1/2, use the new independence and existing cond
APIs to show that conditioned count probabilities are still 2/3 and 1/3.
For E={actual count=1}, mass 1/3, use the new event-fiber result and cond to show
that both supported orders retain mass 1/2 while count is 1 a.e. and its mean
is 1. Neither result preserves the whole global permutation law.

The unnormalized fiber law covers E=∅, the impossible count event count=2,
and the unsupported list [0,0]. Prove the pertinent zero masses through the
new formula/support or actual count bound. Null conditioning is the existing
zero measure, not a normalized probability law.

### Minimal assumptions, actual-law transfer and counterexamples

- Connect new independence to existing empty/full/singleton/tied cases.
  Empty A gives count N and order []; full A gives count zero under lawful
  strict order; Empty I gives normalized identity sample, empty order and
  zero count without manufacturing an identifier.
- Use a local always-true LT relation on Unit and a full Fin2 subset to show
  that the weak-LT independence theorem is applicable even though count is 2.
  Do not attach the lawful outside-count interpretation to this case.
- With a full lawful subset and an ENNReal weight constantly ∞, connect the
  new lower-integral theorem to the actual zero product. The zero coefficient
  is compatible with the infinite weight under ENNReal conventions.
- Show current-law transfer and genuine real product integrability in a
  specialization with arbitrary Ω, μ and Π satisfying the actual global HasLaw.
  No finite-Ω premise may appear. Existing HasLaw.integrable_comp plus finite
  target integrability suffices for the example.
- Reuse the old actual singleton/global-head boundary: the selected order has
  the same HasLaw, while the count mean changes from 1 to 3/2. Correctly state
  that this refutes mean transfer, not independence from a constant order.
- Give the compact actual two-atom Fin3 law with mass 1/2 at identity and 1/2
  at swap 0 2. The actual (count, order) values are (0,[0,1]) and (1,[1,0]).
  Its order has the old uniform two-order law, but joint probability 1/2
  differs from the product 1/4. This directly refutes inferring the new
  independence from a uniform internal-order marginal.
- Retain the existing adaptive-minimum count counterexample and its fixed-set
  limitation by reference/composition; another adaptive experiment is not
  required. A-preserving relabelings may move a named outsider: a small swap
  case or explicit statement assessment must retain that distinction.

The more elaborate optional Fin5 conditional pair-filter consumer in the
preflight is deferred: existing XU05 already checks actual conditional pair
composition. No source obligation is dropped by avoiding another duplicate
client here. A stronger complement-fixing event helper, full count distribution
formula, other overlapping-order counterfamily and public conditional wrappers
remain optional later work, not additional gates for this bounded unit.

## Source limits, statement review and acceptance

This fixed-set method supports a justified weighted treap argument only after
the actual work weight is proved to depend on this same fixed internal order.
It does not supply that algorithm/value bridge, conditional ancestor law,
recursive-history theorem, frontier/layer sum or C10-117. The retained treap
counterfamily, actual join2 qualifications and separate conditional charging
plan remain open. A uniform relative-order marginal under a changed measure
must never be upgraded to the full global law required here.

Chapter 2's mean proof already has a smaller route through XU03 conditional
marginals and genuine integrability. XU06 must not become an artificial
prerequisite. All source pivot/partition/cost/duplicate and randomized-execution
obligations remain where previously tracked. No book coverage is accepted here.

Statement review covers the actual shared sample, fixed quantifier order,
inverse orientation, arbitrary LT versus lawful order, complete finite support,
factorial and null-event normalization, target versus source measurability,
genuine integrability under arbitrary Ω, natural subtraction before casts,
signed/infinite weights, same-set conditional direction, and every expected
case's use of the public results. Update public-root imports, the concise
source-use document and reconstruction map. No new axiom, admission, unsafe or
partial definition, native_decide or skipped kernel check is permitted.

Capture a clean immutable draft with the requirements outside its diff.
Matching focused compilation, full guarded candidate build and exhaustive
audit, independent final Standards and Spec reviews, and immediate candidate
verification remain mandatory. Integrate only after repaired Chapter 1 and
the inherited shared bases are accepted, preserving history and all corrections.
Bounded source readings and durability checkpoints do not close formal gates.
