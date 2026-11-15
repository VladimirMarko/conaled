# Fixed-subset placement and internal order: mathematical/API preflight

## Status and conclusion

This is bounded read-only preparation in the retained FDSA workflow. The proposed statements below are not frozen requirements or implemented Lean. No compiler, Git/ref/index action, project checker or hash helper, source edit, dependency/cache change, gate change or chapter activation was performed. The report path was absent before this write. No finite enumeration campaign was run.

**The proposed independence is valid for a fixed subset under the original uniform global permutation.** Its count version is slightly more general than the suggested nonempty, injective-priority statement: independence needs neither nonemptiness nor injectivity of the priorities. Those conditions enter the interpretation as an actual first position and the substitution of the explicit mean, respectively.

The proof is a small extension of XU02's existing relabeling argument. Relabeling keys within the subset changes their internal order transitively while preserving their occupied priority-label set, and hence `beforeCount`. Apply that symmetry to each count event, partition it by the supported internal orders, and normalize by the number of orders. Existing Mathlib independence and integration theorems then give the weighted expectation formula. No new probability carrier, independence record, group-action framework, selector or executor is needed.

This does **not** establish the treap charging claim C10-117. A source client still has to identify its actual random weight as a function of this fixed subset's internal order, identify the placement variable, and justify the probability law at the point where the bound is used. A marginal uniform-order law alone gives none of those placement guarantees.

## Inspected source identities

The inspected conaled source is the saved joint-order draft in `conaled-permutation-joint`, reported by root at commit `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e`, with all XU01–XU05 predecessors still unaccepted. No Git command was needed for this investigation. Mathlib is the existing pin `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Primary local sources:

- `Applications/Probability/PermutationOrder.lean`: the actual `restrictedOrder` operation, finite support, factorial cardinality, private relabeling proofs, scalar/map laws and the XU05 generic pair-filter law.
- `Applications/Probability/PermutationExpectation.lean`: `beforeCount`, its definition-only `LT` assumption, its finite bound, actual unconditional means and rank/minimum bridge.
- `Applications/Probability/PermutationTail.lean`: actual first-event conditioning and the generic observed-order law, with no global-environment-uniformity conclusion.
- `Examples/PermutationExpectationBoundary.lean`: the saved singleton placement counterexample under global-head conditioning and the equal singleton order laws under both measures.
- `Examples/PermutationJoint.lean`: an existing client derives Mathlib's `IndepFun` from an actual joint law.
- Pinned Mathlib `Probability/Independence/Basic.lean`, `Probability/Independence/Integration.lean`, `Probability/UniformOn.lean`, `MeasureTheory/Measure/Basic.lean`, `MeasureTheory/Function/L1Space/Integrable.lean` and `Data/Set/Card.lean`.

The named arithmetic below reuses `research/permutation-expectation-calculations.json` and `research/finite-ranking-calculations.json`. The former already records the Fin3 count distribution and the two actual conditional orders. New weighted arithmetic is a direct algebraic consequence, not a new enumeration or Lean validation.

## 1. Exact fixed-set statement and hypothesis split

Let `I` be an arbitrary index type and let `positions : List I` be complete and have no duplicates:

```lean
(hnd : positions.Nodup)
(hcomplete : ∀ a, a ∈ positions)
```

As in XU02, these assumptions supply a local finite enumeration; no additional public `Fintype I`, `Finite I`, `Nonempty I`, order on `I`, or measurable structure on `I` is necessary. The actual operation `restrictedOrder` requires `[DecidableEq I]`. The permutation sample space has the supplied measurable space and measurable singletons. It is nonempty even when `I` is empty, since it contains the identity permutation.

For a fixed `A : Finset I`, a fixed `priority : I → P`, and a sampled key-to-label permutation `π`, abbreviate only within this note:

```text
μ = uniformOn (Set.univ : Set (Equiv.Perm I))
O π = PermutationOrder.restrictedOrder positions A π
B π = PermutationExpectation.beforeCount priority A π
N = Nat.card I,   s = A.card
```

`O π` is `filter A (positions.map π.symm)`, with inverse orientation. `B π` is the ordinary Nat cardinality of `{b | ∀ a ∈ A, priority (π b) < priority (π a)}`. No new operation is proposed.

The desired mathematical statement is

```text
IndepFun B O μ.
```

It is true under `[LT P]` alone, with no injectivity or measurability of `priority`, no order on `I`, and no nonempty-A assumption. To state `IndepFun` a measurable space on `List I` must be supplied. A direct finite-event proof does not need `MeasurableSingletonClass (List I)`: all relevant preimages are subsets of the finite discrete sample space. A product-map statement using the existing uniform-on-orders target would additionally use the target singleton hypothesis of XU02, but a new public map wrapper is not necessary for the weighted application.

The source-relevant strengthening substitutes the actual mean. Under `[LinearOrder P]` and `Function.Injective priority`, XU04 gives

```text
Eμ[B] = (N − s)/(s + 1),
```

with the subtraction performed in Nat before the appropriate cast. Thus, for a fixed function `g : List I → ENNReal`,

```text
∫⁻ π, (B π : ENNReal) * g (O π) ∂μ
  = (((N − s : Nat) : ENNReal) / ((s + 1 : Nat) : ENNReal))
      * ∫⁻ π, g (O π) ∂μ.
```

For `g : List I → Real`, the analogous real identity holds. In this finite-sample setting all real-valued composites and products are genuinely integrable; no global bound on `g` over all lists is needed. Equality also holds for signed real `g`. Nonnegativity is needed when multiplying an upper bound on the coefficient by the expected weight. For that purpose the minimal natural premise is `∀ xs ∈ orders positions A, 0 ≤ g xs`, since unsupported lists are never observed.

These scalar integral statements need no public measurable-space assumption on `List I`: their proof can introduce a local discrete list space and discharge measurability there. Alternatively, a client may provide a measurable `g` in its existing list space and use the public `IndepFun` conclusion directly. There is no measurable-space requirement on the priority target `P` in either route.

### What is meant by “internal order”

The independence result holds for **any fixed complete enumeration** `positions`, including one not sorted by `priority`. Relabeling preserves the occupied label set regardless of the chosen enumeration. However, a source claim that a treap shape or another algorithmic weight is `g (O π)` still has to identify `O` with the actual priority order used by that algorithm. If `priority` is numeric, an arbitrary unsorted `positions` is not that correspondence. This is the same value-semantic distinction retained by XU02; uniform marginal laws cannot repair a wrong pointwise observation.

## 2. Deterministic invariance and the exact relabeling direction

Take any `σ : Equiv.Perm I` satisfying

```lean
hA : ∀ a, σ a ∈ A ↔ a ∈ A
```

and transform the sample by `π ↦ π * σ.symm`. This composes on the **key domain**, not on the priority-label range. The existing private XU02 law is exactly:

```lean
restrictedOrder positions A (π * σ.symm) =
  (restrictedOrder positions A π).map σ
```

Meanwhile, the newly needed deterministic observation law is

```text
beforeCount priority A (π * σ.symm) = beforeCount priority A π.
```

It needs only `[LT P]` and `hA`. To prove it, write `Dπ` for the counted set. Since `σ` preserves `A` in both directions,

```text
D(π * σ.symm) = σ.symm ⁻¹' Dπ.
```

The actual inspected cardinality theorem is:

```lean
Set.ncard_preimage_of_injective_subset_range
  {s : Set β} (H : Function.Injective f) (hs : s ⊆ Set.range f) :
  (f ⁻¹' s).ncard = s.ncard
```

Apply it to the equivalence `σ.symm`; its surjectivity proves the range premise. This argument even respects `Set.ncard`'s infinite-set-to-zero convention without a finiteness assumption. The probability theorem subsequently derives finite `I` from `positions`.

The same invariance can be understood as preservation of the occupied image `π(A)`. XU02's extension need not fix every key outside `A`: preserving `A` already preserves its complement, and the counted set is merely bijectively relabeled. This suffices for the aggregate count. It does not establish invariance of an observation about one named outside key, or of a weight depending on additional outside identities.

## 3. Scalar fiber formula and proof reuse

For an arbitrary `C : Set Nat` and arbitrary list `xs`, the concrete finite-event consequence is

```text
μ {π | B π ∈ C ∧ O π = xs}
  = if xs ∈ orders positions A
    then μ {π | B π ∈ C} / (A.card! : ENNReal)
    else 0.
```

No measurability hypothesis on `C` is needed for this source-event formula: its preimage is a finite set of permutation samples. Nor is a target-list measurable space needed. The statement includes count events of mass zero and `A = ∅`.

The exact proof mechanism already present in `PermutationOrder.lean` is:

1. `exists_map_eq_of_nodup` uses `Equiv.Perm.exists_extending_pair` to extend a positionwise bijection between two distinct-element lists.
2. `exists_relabel_orders positions hnd hcomplete A xs ys hxs hys` obtains `σ` with `xs.map σ = ys` and `∀ a, σ a ∈ A ↔ a ∈ A`.
3. `restrictedOrder_relabel` gives the actual observation transport under `π ↦ π * σ.symm`.
4. `fiber_mass_eq` compares sample-event cardinalities using `Set.encard_preimage_of_bijective (Group.mulRight_bijective σ.symm)` and `uniformOn_univ`.
5. `uniformOn_restrictedOrder_eq` partitions the sample by `orders positions A`, whose cardinal is `Nat.factorial A.card`.

For the new claim, run steps 2–4 on the sliced events `{π | B π ∈ C ∧ O π = xs}`. The deterministic count invariance makes the extra conjunction stable under the same sample bijection. For a fixed `C`, all supported order fibers therefore have equal sliced mass.

Partition the count event using the existing theorem:

```lean
MeasureTheory.sum_measure_preimage_singleton
  (s : Finset β) {f : α → β}
  (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) :
  (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' (s : Set β))
```

Use the restricted measure `μ.restrict {π | B π ∈ C}` and the actual order observation. `restrictedOrder_mem_orders` proves support coverage. The sum is the original count-event mass, so factorial-cardinality normalization gives the displayed formula. The denominator is positive and finite even when `s = 0`, since `0! = 1`. There is no division by the count-event mass, so null events cause no conditional-probability corner case.

### Smallest plausible helper refactor

The current relabeling/transitivity helpers are **private**. The public unconditional marginal law does not imply the desired joint fact, and the new module cannot simply invoke those private names.

The economical reuse proposal is one ordinary event-fiber theorem in the existing order module: if a sample event `E` is invariant under all these `A`-preserving right relabelings, then

```text
μ (E ∩ {π | O π = xs})
  = if xs ∈ orders positions A then μ E / (A.card! : ENNReal) else 0.
```

Its invariance premise is the explicit proposition

```text
∀ σ, (∀ a, σ a ∈ A ↔ a ∈ A) →
  ∀ π, (π * σ.symm ∈ E ↔ π ∈ E).
```

This is a semantic statement about the actual existing observation and sample measure, not a new action record or framework. It has the concrete `beforeCount` events as its immediate client and reuses the existing private machinery without exposing proof-only existence helpers. It also keeps Bochner integration and `PermutationExpectation` out of the basic order module. Any future implementation would be a new candidate preserving the saved old statements and cases; this preflight edits none of them.

A small placement/order client module can then import `PermutationOrder`, `PermutationExpectation` and Mathlib's independence integration API. If the general invariant-event statement is not wanted as public scope, the specialized count proof could instead be colocated with the private order helpers, at the cost of an added expectation-module dependency, or reconstruct the short extension argument privately in the client. Exporting all current private helpers solely to bypass their scope is unnecessary.

## 4. Existing independence and weighted-integration APIs

### Direct independence avoids a redundant product-law layer

The exact theorem in `Probability/Independence/Basic.lean` is:

```lean
ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul :
  IndepFun f g μ ↔
    ∀ s t, MeasurableSet s → MeasurableSet t →
      μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t)
```

For any target order event `t`, filter the finite support `orders positions A` by membership in `t`. Sum the sliced scalar formula over that finite support, and use XU02's unconditional scalar law for the second factor. This proves the right-hand side and hence `IndepFun B O μ`. Because the calculation uses measurable **sample fibers**, it does not require measurable list singletons. No product-measure instance or new independence wrapper is required.

If a client actually wants the product map, the existing theorem provides it:

```lean
indepFun_iff_map_prod_eq_prod_map_map
  [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
  IndepFun f g μ ↔
    μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g)
```

Both observations are measurable from the finite sample space. With the additional list-singleton hypothesis, substitute XU02's `map_restrictedOrder_uniformOn` for the right marginal. The left marginal remains the actual pushed-forward count law; no new closed distribution formula is needed.

### Composition and nonnegative weights

The existing composition theorem is:

```lean
IndepFun.comp (hfg : IndepFun f g μ)
  (hφ : Measurable φ) (hψ : Measurable ψ) :
  IndepFun (φ ∘ f) (ψ ∘ g) μ
```

`IndepFun.comp₀` is also available with AEMeasurable source variables and transforms under their pushed-forward measures. For this finite global experiment, measurable composition suffices. Apply it with the Nat-to-ENNReal cast and the requested weight function. Then use the exact API in `Probability/Independence/Integration.lean`:

```lean
lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
  (h_meas_f : AEMeasurable f μ) (h_meas_g : AEMeasurable g μ)
  (h_indep_fun : IndepFun f g μ) :
  (∫⁻ ω, f ω * g ω ∂μ) =
    (∫⁻ ω, f ω ∂μ) * (∫⁻ ω, g ω ∂μ)
```

No finiteness assumption on an ENNReal weight or its lower integral is necessary. The theorem includes `∞` using the usual ENNReal multiplication convention; for example a zero count times an infinite weight is zero. Substitute the already saved `lintegral_beforeCount_uniformOn priority hinj A` only after imposing its injective-linear-order hypotheses.

For real-valued observations the inspected API is:

```lean
IndepFun.integral_fun_mul_eq_mul_integral
  (hXY : IndepFun X Y μ)
  (hX : AEStronglyMeasurable X μ)
  (hY : AEStronglyMeasurable Y μ) :
  (∫ ω, X ω * Y ω ∂μ) =
    (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)
```

The general pinned theorem does not demand explicit integrability arguments. For the source result, still establish genuine integrability of the two observations and their product with:

```lean
Integrable.of_finite [Finite α] [MeasurableSingletonClass α]
  [IsFiniteMeasure μ] {f : α → β} : Integrable f μ
```

This is in `MeasureTheory/Function/L1Space/Integrable.lean`; its normed-space context specializes to Real. Finite `Equiv.Perm I` follows from `positions`, and the existing `instIsProbabilityMeasure_uniformOn_univ` supplies probability normalization. No undefined-real-integral behavior is being used. The inspected composition variant `IndepFun.integral_fun_comp_mul_comp` is an alternative when working directly with the pushforward domains.

## 5. Useful weighted consequences and exact limitations

Let `c = ((N − s : Nat) : Real) / ((s + 1 : Nat) : Real)` under the XU04 hypotheses. For a nonnegative weight on supported orders,

```text
Eμ[B * g(O)] = c * Eμ[g(O)].
```

If `c ≤ C`, nonnegativity of `Eμ[g(O)]` gives

```text
Eμ[B * g(O)] ≤ C * Eμ[g(O)].
```

The same factorization applies to `B + 1` by measurable composition. For an actual rank equivalence `rank : I ≃ Fin U` and `A.Nonempty`, reuse `beforeCount_rank_eq` to identify `B+1` with

```text
((A.image (fun a => rank (π a))).min' nonemptyProof).val + 1.
```

Reuse `integral_firstPosition_uniformOn` for its mean `(U+1)/(s+1)`. This yields the actual ordinal-first-position weighted formula. No arbitrary numeric minimum is assigned that mean. A nonlinear transform, such as a logarithm of the ordinal, can be composed with the independence law, but its mean bound and any Jensen premises are separate existing analytic work, not proved by this preflight.

The weight premise must be a real observation equality, for example `W π = g (O π)` pointwise or almost everywhere under the stated measure. Merely calling a random weight a “shape cost”, or knowing its own expectation is bounded, is insufficient. Dependence on the occupied ranks, external keys, additional priority comparisons, a sample-dependent subset, or a conditioning history must be justified separately. A law of `O` alone cannot supply a law of `(B,O)`.

### Empty, full, tied and conditioned boundaries

| Case | Exact behavior |
| --- | --- |
| `A = ∅` | `B = Nat.card I` and `O = []` pointwise. Independence and the weighted count formula remain valid; coefficient is `N`. There is no minimum element or first-position interpretation. |
| Full `A`, with `[Preorder P]` | `B = 0` by self-comparison, while the order may be nonconstant. Independence is valid and all weighted count integrals are zero. Under only an arbitrary `LT` relation, the invariance/independence theorem remains valid, but the zero-count claim needs irreflexivity, supplied here by the preorder. |
| Empty index type | There is one permutation sample, the empty subset and empty order, and count zero. No default index or nonempty-key assumption is needed. |
| Tied priorities | Independence remains valid, but the injective-priority mean must not be substituted. The existing constant-priority singleton case has count zero rather than the formula's positive value. |
| Selected-head event of this same fixed `A` | It is a function of `O_A`. For a member `a`, its mass is `1/s`; independence implies the count distribution is unchanged after this conditioning. This is a mathematical consequence, not a proposed extra conditional API in the first unit. |
| A global-head event, or a head event for another subset | It need not be a function of `O_A`; the original placement mean cannot be transferred merely from a retained uniform relative-order law. |
| Adaptive `A(π)` | The symmetry premises do not follow. The saved adaptive singleton chosen from the global minimum has count zero, unlike a fixed singleton. |

The existing concrete caveat survives unchanged: in `Fin 3`, take `A = {1}` and condition on global first key 0. The only possible global orders are `[0,1,2]` and `[0,2,1]`, each with conditional mass `1/2`. The actual count is respectively 1 and 2, so its mean changes from 1 to `3/2`. The singleton observation `O_A` is `[1]` under both laws. Even independence from this constant observation says nothing about whether the original mean is preserved. XU03's `HasLaw` conclusion is about the observed order under the changed environment, not an assertion that the environment is still the original uniform permutation measure.

## 6. Bounded connected cases without new enumeration

One nontrivial candidate case is `I = Fin 3`, `A = {0,1}`, standard rank and label order. The already saved count law is `P(B=0)=2/3`, `P(B=1)=1/3`; XU02 supplies the two internal orders with mass `1/2` each. The new joint theorem should establish:

| Internal order | `B = 0` joint mass | `B = 1` joint mass |
| --- | ---: | ---: |
| `[0,1]` | `1/3` | `1/6` |
| `[1,0]` | `1/3` | `1/6` |

For the genuinely order-dependent weight `g([0,1])=2`, `g([1,0])=5`, its mean is `7/2`, the count-weight mean is `7/6`, and the ordinal-weight mean is `14/3`. These are exact target consequences of the new law and existing marginal results, with no extra distribution enumeration claimed.

A useful boundary uses a weight depending on placement instead: set `W π = B π` in the same example. Since this count is 0 or 1, `E[B*W]=1/3`, whereas `E[B]E[W]=1/9`. Thus a generic random-weight replacement would be false. This directly tests the meaningful `g(O_A)` requirement.

The saved global-head/singleton case above supplies the separate changed-environment boundary. Empty and full cases test zero coefficients and zero factorial arguments. There is no need for another exhaustive small-universe campaign.

## 7. Proposed public surface and remaining proof obligations

No interface is frozen. A coherent small extension would consist of:

1. One ordinary invariant-event fiber formula in `PermutationOrder`, reusing its existing private transitivity/transport helpers. Proposed call order: `uniformOn_inter_restrictedOrder_eq positions hnd hcomplete A E hInvariant xs`.
2. A concrete count/order `IndepFun` theorem in a small client module importing order and expectation. Proposed call order: `indepFun_beforeCount_restrictedOrder positions hnd hcomplete priority A`; `[LT P]` is enough. There is no new independence predicate or record.
3. The source-use weighted count identity, with ENNReal and/or Real corollaries as actually needed by the client. Proposed call order: `integral_beforeCount_mul_order_uniformOn positions hnd hcomplete priority hinj A g`. Its priority hypotheses are exactly those of XU04; the pure equality need not require nonnegative real `g`. The bounded inequality adds nonnegativity on supported orders.

The scalar count-fiber formula can remain a direct instance of item 1 rather than another public alias, and product maps, count-plus-one factors and transforms can initially remain existing-API consequences. The proposal deliberately avoids importing expectation into the basic order module or exporting proof-only helpers.

The remaining source proof work is concrete: prove the `Set.ncard` relabeling identity, extend equal-fiber normalization to an invariant event, sum the finite fibers for the standard independence predicate, and connect finite integrability and existing XU04 means to the weighted formula. Later treap use additionally needs the separately assessed actual-variable and history/conditioning bridges. Neither the new independence result nor any XU01–XU05 marginal law automatically establishes those bridges. All saved formal drafts and all chapters remain unaccepted.

Root's follow-up explicitly leaves this event-fiber refactor and all other interfaces as proposals; no new unit is being frozen or implemented. The separate source investigation reports a counterfamily in which recursive minimum-position conditioning grows with subtree size. Its proof and a possible frontier/search-path alternative belong to that separate investigation, not to this API report. The fixed-set result above therefore remains a useful documented possibility, not a proposed resolution of C10-117.
