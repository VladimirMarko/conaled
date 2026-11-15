# Fixed placement and internal order: independent unit/case preflight

## Status, scope and conclusion

This is independent mathematical and source preparation for a possible XU06 unit. It is not a scope freeze, an implementation, compilation evidence, either final-review axis, or acceptance. The XU01–XU05 source drafts remain uncompiled and unaccepted. Chapter status and the old gate 80227 are unchanged.

The retained fixed-set proposal is mathematically sound. Its strongest useful small statement is the invariant-event fiber formula for the existing `restrictedOrder`, with the existing aggregate `beforeCount` as an immediate client. Count/order independence needs only `LT P`; the explicit mean needs injective priorities in a linear order. A supported complete internal-order conditioning of the **same fixed set** preserves the count distribution. It must not be classified with arbitrary global-head or adaptive-set conditioning.

The coordinator clarified that the earlier mention of a fixed disjoint second set was context, not a request for a new count restricted to that set. This note proposes no such observation. All occurrences of the count below mean the existing count over **all** keys. The existing XU05 pair-filter contract supplies a useful downstream connection once an actual whole-order law is established under the current measure.

Only this new report was written. No compiler, checker, project hash helper, Git/ref operation, enumeration, cache/configuration change, remote operation, or source/status edit was performed. Named finite cases below use retained source fixtures and hand calculations; the prior enumeration was not repeated.

## Inspected sources and evidence boundary

The implementation reference is `conaled-permutation-joint`, previously identified by the coordinator as local candidate `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e`. This is coordinator-provided identity, not a new Git/hash check. The relevant existing dependency pin is Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The bounded reading covered:

- `fdsa-control/research/permutation-placement-order-preflight.md`, including its actual right-relabeling direction, private-helper reuse, weighted formulas and limitations.
- `Applications/Probability/PermutationExpectation.lean`: the aggregate definition, complement bound, minimum-event bridge, real/ENNReal means and ordinal bridge.
- `Applications/Probability/PermutationOrder.lean`: actual observation/support operations, one-set and simultaneous two-set transports, the existing joint law, and the exact current `hasLaw_filter_pair` contract.
- `Examples/PermutationExpectation.lean` and `Examples/PermutationExpectationBoundary.lean`: the actual Fin3 variables, rank/minimum correspondence, empty/full/tied/adaptive cases, and the global-head-conditioned singleton mean.
- `Examples/PermutationJointBoundary.lean`, and the relevant actual-law/conditional projection portion of `Examples/PermutationJoint.lean`: unused labels, empty subsets/universe, the overlapping-set counterexample, and the Fin5 conditional-tail/projection connection.
- `Applications/Probability/PermutationTail.lean`'s current private `hasLaw_cond` proof and public conditional-order contracts, to resolve the almost-everywhere-measurable sample-space transfer issue.
- Pinned `Mathlib/Probability/HasLaw.lean` and the relevant conditional-probability signatures. The retained `permutation-expectation-calculations.json` supplies the already recorded count distribution and conditional samples.

Names and proof routes below describe source contracts and mathematical expectations. They are not claims that new Lean statements have elaborated.

## 1. Actual observations and minimal assumptions

Let `positions : List I` be a complete duplicate-free enumeration, let `A : Finset I` be fixed before sampling, and let `priority : I → P` be fixed. Write

```text
μ       = uniformOn (Set.univ : Set (Equiv.Perm I))
O_A π   = restrictedOrder positions A π
C_A π   = beforeCount priority A π
N       = Nat.card I
k       = A.card
Q_A     = orders positions A
```

These are abbreviations in this report, not new proposed carriers or operations. The source definitions are

```text
O_A π = (positions.map π.symm).filter (membership in A)
C_A π = Set.ncard {b | ∀ a ∈ A, priority (π b) < priority (π a)}.
```

Thus `π` maps keys to assigned labels, and the observed order uses its inverse. `C_A` is not the count before a named outside key, nor a separately selected-subset count.

`positions.Nodup` and `∀ a, a ∈ positions` supply the finite enumeration locally. As in XU02/XU05, no public `Fintype I`, inhabited key, index order, or measurable structure on `I` is necessary. `restrictedOrder` uses the existing `[DecidableEq I]` parameter. Probability statements need a measurable permutation space with measurable singletons. It is a finite nonempty sample space even when `I` is empty.

| Conclusion | Additional semantic assumptions |
| --- | --- |
| Right-relabeling invariance of `C_A` | Only `[LT P]` and setwise preservation of `A`; even finiteness is unnecessary for this `Set.ncard` equality. |
| Invariant-event fiber law and `IndepFun C_A O_A μ` | Complete duplicate-free `positions` and the original uniform global permutation measure. No `A.Nonempty`, priority injectivity, or lawful order is required. |
| `C_A ≤ N - k`; “count of outside keys” | The existing public theorem uses `[Finite I] [Preorder P]`; its self-exclusion argument uses irreflexivity. Bare `LT` does not provide that meaning. |
| Explicit real/ENNReal count mean `(N-k)/(k+1)` | `[LinearOrder P]` and `Function.Injective priority`, exactly as XU04. No nonempty-set assumption. |
| Count plus one is the actual one-based first ordinal | A rank equivalence `rank : I ≃ Fin U` and `A.Nonempty`, using the existing actual image-minimum bridge. |

The independence claim is valid for any fixed complete `positions`, even when it is not sorted by numeric `priority`. Calling `O_A` an algorithm's increasing-priority order requires a separate pointwise source correspondence. Uniform distribution cannot substitute for that correspondence.

## 2. Relabeling invariance is an observation fact, not assumed independence

Take `σ : Equiv.Perm I` with

```text
∀ a, σ a ∈ A ↔ a ∈ A,
```

and transform the sample by `Tσ π = π * σ.symm`. The existing private order transport states exactly

```text
O_A (Tσ π) = (O_A π).map σ.
```

For the actually counted set `Dπ`, substituting `σ.symm a` for the quantified members of `A` gives

```text
D(Tσ π) = σ.symm ⁻¹' Dπ.
```

The equivalence preserves cardinality, hence `C_A (Tσ π) = C_A π`. This is valid for an arbitrary `LT` relation and preserves the `Set.ncard` infinite-set convention. No minimum, injectivity of `priority`, or probabilistic independence is used in this deterministic proof.

The permutation `σ` need not fix keys outside `A`. For example, use `Fin 3`, identity rank, `A = {1}`, `π = id`, and `σ = swap 0 2`. The named event “key 0 precedes every key in A” changes from true to false, while the aggregate count stays 1: the preceding key changes from 0 to 2. Thus an aggregate cardinality argument must not silently become individual outside-key invariance.

There are two different symmetries here. The uniform permutation measure is invariant under arbitrary permutation translations, but arbitrary observations need not be unchanged. The relevant right action on the key domain additionally preserves `C_A` and transports `O_A` transitively. A left action on assigned labels can change the count: with identity rank, `A={0,1}`, and `π=id`, the count is 0, whereas composing on the label side with `swap 0 2` gives count 1. Invariance of the global sampling measure alone is not a proof of independence.

## 3. Strong invariant-event statement and the count consequence

For an actual event `E : Set (Equiv.Perm I)`, suppose

```text
∀ σ, (∀ a, σ a ∈ A ↔ a ∈ A) →
  ∀ π, (π * σ.symm ∈ E ↔ π ∈ E).
```

Then for every list `xs`, the sound fiber identity is

```text
μ (E ∩ {π | O_A π = xs})
  = if xs ∈ Q_A then μ E / (k! : ENNReal) else 0.
```

The proof uses the existing private one-set transport to biject the sliced fibers, partitions `E` by the actual supported orders, and uses `Q_A.card = k!`. Every source event is measurable because the permutation sample is finite and has measurable singletons. No measurable space on lists is needed for this scalar source-event equality. No positive-mass assumption on `E` is needed either: the only denominator is `k!`, which is positive and finite, including `0! = 1`.

Every count event `E = {π | C_A π ∈ D}`, for any `D : Set ℕ`, satisfies the premise. Summing the scalar formula over the supported lists in a target order event proves

```text
IndepFun C_A O_A μ.
```

For that standard predicate, supply the target measurable spaces. A direct finite-source event proof works with any list measurable space; using the existing uniform-on-orders `HasLaw` additionally uses its list-singleton hypothesis. The result controls the **whole count distribution**, not merely the mean. Measurable transforms of the count and of the order inherit independence through existing Mathlib composition results.

This is the strongest useful small event statement supported by the retained symmetry argument. It does not assert that every independent event must satisfy the displayed invariance premise, nor propose a new group-action abstraction. The current relabeling helpers are private; a future separate module cannot simply invoke them by name. An ordinary event-fiber theorem in their existing module is a sound reuse boundary.

## 4. Two valid conditional directions, with different preserved objects

### Placement conditioning preserves the internal-order law

If `E` satisfies the invariant-event premise and `μ E ≠ 0`, then

```text
HasLaw O_A (uniformOn Q_A) (μ[|E]).
```

Here positivity is required for a normalized conditional law. It is not required for the unnormalized fiber equality. Since `μ` is finite, no extra `μ E ≠ ∞` hypothesis is needed. An event such as `C_A = c` preserves the uniform internal-order law when it has positive mass; it normally changes the count distribution itself.

This produces a concrete XU05 consumer. Given fixed `B,D ⊆ A` with `Disjoint B D`, apply the current `hasLaw_filter_pair` to `Y = O_A` and the current measure `μ[|E]`. Its actual filtered pair has the product of the two uniform order laws. The existing pointwise `filter_restrictedOrder_of_subset` identifies that pair with `(O_B, O_D)` on the same sample. No union-cover assumption is needed. This adds no separately selected-set count.

The saved Fin5 fixture is already suitable. Take `A = Examples.PermutationJoint.remaining5 = univ.erase 2`, identity ranks, and `E = {C_A = 1}`. With exactly one outside key, `E` is exactly the saved `firstTwo` global-head event, of mass `1/5`. Under `afterTwo`, `O_A` is uniform. Filtering it by the saved disjoint `left5={0,1}` and `right5={3,4}` gives the same product law, with each supported pair mass `1/4`, as the existing actual-tail/projection development. The original count mean is `1/5`; after conditioning it is 1. That difference is fully compatible with the preserved order law.

### Internal-order conditioning preserves the placement/count law

If `xs ∈ Q_A`, the event `Hxs = {π | O_A π = xs}` has mass `1/k! > 0`. Independence gives, for every count event `D`,

```text
(μ[|Hxs]) {π | C_A π ∈ D} = μ {π | C_A π ∈ D}.
```

Consequently the conditional count mean is the same XU04 coefficient `(N-k)/(k+1)` under its linear-order/injectivity assumptions. More generally, conditioning on any positive-probability event determined only by `O_A` preserves the count law. A selected first key of this same fixed set is one such event; its positive mass follows from membership in `A`.

This direction does **not** say that `O_A` remains uniform after conditioning on its complete value: it then equals `xs`. It says that the count retains its original distribution. Neither direction says that the entire global permutation remains uniformly distributed. These distinctions are essential when transferring a later conditional mean.

The complete own-order and own-head consequences can be checked clients of the event/independence theorem. They do not require a separate public conditional-expectation wrapper in a first unit. Global-head conditioning is not automatically invalid either: it is valid when its actual event satisfies the relevant premise, as the Fin5 example does for the remaining set. The warning concerns transferring a count mean without proving the appropriate premise.

## 5. Real/ENNReal weights and actual sample-space transfer

Under the XU04 mean hypotheses, put

```text
q = ((N-k : Nat) : Real) / ((k+1 : Nat) : Real).
```

For every fixed `g : List I → ℝ`, the desired equality is

```text
∫ π, (C_A π : Real) * g (O_A π) ∂μ
  = q * ∫ π, g (O_A π) ∂μ.
```

The ENNReal analogue uses the corresponding casts and lower integrals. For the finite global sample, arbitrary real-valued `g` gives genuinely integrable composites and products; no global bound on `g` over unsupported lists is needed. Signed weights are permitted in the equality. A coefficient upper-bound inequality needs nonnegative expected weight; nonnegativity on the actual finite support is a convenient sufficient premise.

ENNReal weights may take `∞`, with the usual multiplication convention including `0 * ∞ = 0`. A real theorem cannot be obtained by casually applying `toReal` to such an infinite-valued calculation. Establish the real finite integrability separately, as the retained plan does.

Factorization for `C_A+1` follows by composition/addition. Its coefficient is `(N+1)/(k+1)`, including `A=∅` as an arithmetic sentinel. To identify the factor with an actual one-based ordinal, use a rank equivalence and the nonempty-set image-minimum bridge. The saved raw numeric minimum `100 + 10*rank` has mean `310/3` in the Fin3 case, not the ordinal mean `4/3`; the new weighted result does not erase that distinction.

For arbitrary actual sample space `Ω` with current measure `ν`, a sufficient transport premise is

```text
hΠ : HasLaw Π μ ν,   where Π : Ω → Equiv.Perm I.
```

Compose the actual observations with that **same** `Π`. The event formulas, joint law/independence, and weighted integrals transfer. No finiteness, countability, or measurable-singleton assumption on `Ω` is required. The pinned `HasLaw.isProbabilityMeasure` supplies probability normalization of `ν` from that of `μ`. The pinned `HasLaw.fun_comp`, `HasLaw.measure_eq`, `HasLaw.integrable_comp` and `HasLaw.integral_comp` provide the needed mechanisms. Integrability is proved on the finite permutation target and transported; applying `Integrable.of_finite` directly to arbitrary `Ω` would be unjustified.

Only almost-everywhere measurability of `Π` is required by this `HasLaw` premise. The current XU03 private `hasLaw_cond` proof also shows the exact transport pattern for a measurable target event `E`:

```text
HasLaw Π (μ[|E]) (ν[|Π ⁻¹' E]).
```

It uses `cond_absolutelyContinuous`, `Measure.map_smul`, `Measure.restrict_map_of_aemeasurable`, and `Measure.map_apply_of_aemeasurable`; it does not strengthen `HasLaw` to a globally measurable observation. This proof pattern is available to inspect, but the private theorem is not an exported API. A new client must not use `ae_cond_of_forall_mem` with an unproved measurable source event merely because `Π` is a.e. measurable. Composition through the actual conditional law avoids that mistake.

A current `HasLaw` only for `O_A`, or for a pair of its filters, is insufficient to infer the global-uniform law of `Π` or the placement/count law. Likewise, an almost-everywhere identity `W = g ∘ O_A` must hold under the measure used in the integral; a fresh environment needs its own justified observation/law bridge. No independent replacement sample is introduced by these transports.

## 6. Connected positive fixture and exact arithmetic

Use the existing `Examples.PermutationExpectation.selected = {0,1}`, its identity `rank3`, and `law3`. For this case use the complete label list `[0,1,2]`; the current boundary module already supplies that list, while the main expectation fixture does not define an internal-order observation or the new weight. Those remain actual client definitions to add if a unit is frozen.

The retained count distribution is `P(C_A=0)=2/3`, `P(C_A=1)=1/3`, and `count_mean_real`/`count_mean_ennreal` connect its mean to the actual source count. The two supported orders each have mass `1/2`. The new sliced-event result should give:

| Actual internal order | Joint mass with `C_A=0` | Joint mass with `C_A=1` |
| --- | ---: | ---: |
| `[0,1]` | `1/3` | `1/6` |
| `[1,0]` | `1/3` | `1/6` |

Define an actual fixed order function with values `g([0,1])=2` and `g([1,0])=5`, for example by testing equality with `[0,1]` and using 5 otherwise. Its values outside `Q_A` are irrelevant. Direct arithmetic gives

```text
E[g(O_A)]        = 2/2 + 5/2                 = 7/2
E[C_A*g(O_A)]    = 2/6 + 5/6                 = 7/6
E[(C_A+1)g(O_A)] = (1 + 1/3) * (7/2)        = 14/3.
```

The last expression is also the expectation of `firstPosition3 * g(O_A)` by the existing pointwise `first_position_bridge`. A connected Lean case should use that bridge and the new public factorization, not define a surrogate ordinal or use a separate sampled permutation.

Conditioning on either supported complete internal order leaves the count mean `1/3` and its two probabilities unchanged. Conversely, conditioning on `C_A=1` leaves both internal orders at mass `1/2` and sets the count to 1. An unsupported order such as `[0,0]` has zero mass, as does the event `C_A=2`; their unnormalized fiber identities remain valid, while neither should be advertised as a normalized conditional probability law.

## 7. Boundaries and concrete failed extensions

### Empty/full/singleton/tied boundaries

| Case | Required exact expectation |
| --- | --- |
| `A=∅` | `C_A=N`, `O_A=[]`, supported order mass 1, coefficient `N`; no actual first element. A scalar invariant-event formula includes the empty event as well. |
| Full `A` with a lawful strict order | `C_A=0`; the existing preorder bound proves this. Internal order may vary. A real or ENNReal count-weight integral is zero. |
| Full `A` with only bare `LT` | Invariance/independence still holds. Zero count is not implied: an always-true relation makes the full-set count `N`. |
| Singleton `A={a}` | `O_A=[a]`; count need not be constant. Under injective linear priorities its original mean is `(N-1)/2`. Conditioning on this complete singleton order changes nothing. |
| Empty key type | Exactly one permutation, empty order and zero count. Normalization is 1; no key is manufactured. |
| One key | Empty subset gives count 1; the full singleton gives count 0 under a lawful order. Both order laws are degenerate and both factorials are 1. |
| Tied priorities | Count/order independence still holds. The retained Fin2 constant-priority nonempty singleton has count 0, whereas substituting the injective-priority coefficient would incorrectly give `1/2`. |

### Global-head conditioning changes an unrelated placement mean

The saved `PermutationExpectationBoundary` case uses `A={1}` and conditions the actual global order on key 0 first. The two possible orders `[0,1,2]` and `[0,2,1]` have conditional mass `1/2`; their actual counts are 1 and 2. Thus the mean changes from 1 to `3/2`. The singleton order remains `[1]` under both measures, with the actual old and conditional `HasLaw` proofs already present in the draft.

This refutes an inference from unchanged marginal order law to unchanged placement mean. It does **not** refute independence from that constant singleton order, which holds trivially under either measure.

### A uniform nonconstant order marginal does not establish independence

Use the same actual Fin3 `A={0,1}`, identity ranks and label order. Give mass `1/2` each to the identity permutation and `swap 0 2`, and zero mass elsewhere. These two samples have global orders `[0,1,2]` and `[2,1,0]`. Their actual `(C_A,O_A)` values are respectively `(0,[0,1])` and `(1,[1,0])`.

Consequently `O_A` has exactly the same uniform two-order law as under the original experiment, but

```text
P(C_A=1 and O_A=[1,0]) = 1/2,
P(C_A=1) * P(O_A=[1,0]) = 1/4.
```

This is a two-point hand calculation on actual existing-style permutations, not a new enumeration. It directly refutes the proposed implication from an internal-order marginal `HasLaw` to count/order independence. Its count mean is `1/2`, also different from the original `1/3`.

### Adaptive sets can fail both the mean and the independence extension

The saved `adaptiveSubset π = {π.symm 0}` always selects the global first key, so its count is 0 rather than the fixed-singleton mean 1. That saved example refutes the adaptive mean extension, but its constant count is not a counterexample to independence.

A separate compact hand consequence gives a genuine independence failure without enumerating permutations. In Fin3 choose the singleton `{0}` when key 0 is globally first, and `{1}` otherwise. The adaptive order is `[0]` with probability `1/3`. The adaptive count is zero exactly when global first is 0 or 1, hence with probability `2/3`. On adaptive order `[0]` the count is always zero, so the joint mass is `1/3`, whereas the product is `2/9`. This uses the retained global-head masses and actual singleton rank interpretation. Constant adaptive cardinality 1 is therefore insufficient for either general extension.

### Other overlapping order observations need their own argument

The existing XU05 boundary has `A={0,1}`, `B={1,2}`. Its paired-order event `O_A=[1,0]` and `O_B=[1,2]` has mass `1/3`, while the product of the marginal masses is `1/4`. Therefore the disjoint-filter product law must not be reused without its disjointness premise.

The same fixed sets also give a count/order warning. With standard ranks, `C_A=1` exactly when key 2 is globally first, of probability `1/3`. The event `O_B=[1,2]` has probability `1/2` and forces key 1 to precede key 2, so it is disjoint from `C_A=1`. Their joint mass is 0, not `1/6`. Conditioning on that other order changes the count mean to 0. This does not contradict the valid independence of `C_A` from `O_A` itself: the full same-set order remains a valid conditioning observation even though it shares all of A's keys.

### An arbitrary random weight is not an internal-order function

For the original Fin3 `A={0,1}`, let `W=C_A`. Since the count is 0 or 1,

```text
E[C_A*W] = E[C_A²] = 1/3,
E[C_A] E[W] = 1/9.
```

Thus the arbitrary-weight factorization is false. In a source application, the equation `W = g(O_A)` must be established pointwise or almost everywhere under the stated measure. Naming `W` a shape or work quantity does not establish that equation.

## 8. Compact possible checked-client set and remaining work

No scope is frozen. A compact connected set, if the unit is pursued, is:

1. The saved Fin3 `selected/rank3/law3` count and an actual `restrictedOrder` observation: derive the four sliced masses, the order-dependent 2/5 weight formula, and the ordinal-weight result using `first_position_bridge`.
2. A supported complete own-order conditioning consequence, plus one zero count event and one unsupported list. Keep positive-mass normalization separate from the all-events fiber formula.
3. Reuse the saved Fin5 remaining-set/`firstTwo`/`left5`/`right5` observations to connect a preserved actual order law to current `hasLaw_filter_pair`, including the same-sample projection equality. No new count operation or independent samples.
4. Empty subset, full subset, singleton, Empty index type, and tied priorities, preferably by consuming the existing boundary statements and new public invariance/independence result.
5. Retain the saved global-head and adaptive-minimum limitations and the actual `W=C_A` factorization failure. The two-atom nonconstant-marginal example gives a precise additional independence boundary; the overlap fixture is already available and need not be re-enumerated.
6. One generic current-`HasLaw Π μ ν` composition client, or an equivalent proof-level consequence, to demonstrate actual-sample transport and real integrability without assuming finite `Ω`.

The proposed event theorem, count invariance/independence, and needed weighted identity are sufficient semantic additions. Closed formulas for the complete count distribution, public conditional-expectation wrappers, an external-set count, broad action abstractions, and additional exhaustive examples are unnecessary to establish these connections.

No concrete mathematical correction to the retained fixed-A proposal was found. The refinements above keep its weakest assumptions, both conditional directions, the private-helper boundary, and the actual-variable requirements explicit. They do not resolve any treap-specific adaptive/history bridge, prove source work bounds, compile the draft probability units, or grant acceptance. Edits stop after this report.
