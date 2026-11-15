# Fixed placement and internal order: bounded source scope for a possible shared unit

Prepared 2026-11-02. This is source and mathematical preparation for a possible XU06 unit, not frozen scope, Lean implementation, either final review axis, or acceptance. Chapter 1 remains the prerequisite; all chapters and shared candidates remain unaccepted. The old Chapter 1 gate 80227 is unchanged. Only this new report was written; its path was checked absent. No compiler, checker, project hash helper, Git/ref operation, cache change, new enumeration, or remote source campaign was run.

## 1. Recommendation and retained evidence

The smallest useful addition is the previously proposed **independence of the actual existing aggregate `beforeCount` and the actual relative order of one fixed subset, under the original uniform global permutation law**. An invariant-event fiber identity can reuse XU02's private relabeling proof; the ordinary Mathlib independence interface and XU04's existing mean then give the intended weighted consequence. Transfer to an arbitrary environment is valid when the observation of the **whole global permutation** has that uniform law. A law of the subset's relative order alone is insufficient.

There is no new fixed-B counter in this proposal. A selected-order conditioning example can be a checked consequence, without a new public conditioning API. Nor is a shuffle representation, group-action record, independent priority sampler, or general history framework required by this result. The complementary API assessment is `research/permutation-placement-unit-api-preflight.md`; exact signatures and implementation scope are not fixed by either preparation note.

This report refines, without changing, the following retained evidence:

| Local source | Relevant evidence and scope |
|---|---|
| `research/permutation-placement-order-preflight.md`, §§1–7 | Original fixed-set theorem, `Set.ncard` relabeling, invariant-event normalization, weighted identities, boundaries, and proposed small public surface. Its recorded SHA-256 is `3fe9a8d80a6a57faa4265ecb85267216039dae9f39164cf928560c1bae9cba81`; it is a proposal, not an accepted dependency. |
| `reviews/permutation-placement-order-source-preflight.md`, Result and Limits | Separate source assessment agrees with the mathematics and preserves all global-law, measurability, integrability, and treap limits. It is not final review or acceptance. |
| `research/treap-conditional-work-preflight.md`, §§3–9 | Exact recursive-conditioning counterfamily, actual `join2`/split qualification, and distinct frontier/common-charge/weighted-cluster proof route. Recorded SHA-256 `99e7c6128c5a941d0dbef0b473c0f4f27e73d8f75b69aa64d347937dd4b2dcc1`. |
| `research/quicksort-conditional-mean-preflight.md`, §§1–3 and scope conclusion | Actual first-pivot input, specified-head conditional child laws, comparator-filter bridge, genuine integrability, and expectation transport. The mean proof needs conditional marginals, not a joint distribution or placement independence. |
| `research/quicksort-average-proof-plan.md`, distribution, metric, AFP correspondence, and acceptance sections | Distinct-key average input versus uniformly sampled pivot occurrence; actual costs, duplicate counterexample, and separate randomized execution. |
| `research/chapter02-obligations.md`, C02-024; `research/chapter10-obligations.md`, C10-112–118 | The original sorting and treap requirements remain unchanged and open. |
| `research/permutation-expectation-calculations.json` and `research/finite-ranking-calculations.json` | Previously saved count distributions, global-head boundary, and rank examples. The small calculations below reuse these and the original placement report; no enumeration was rerun. |

The primary identities behind those source plans are the July 27, 2026 book PDF (`book-source/functional_data_structures_algorithms.pdf`, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`); `Sorting.thy` at Isabelle revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`; the dated AFP `Quick_Sort_Cost` archive of 2026-10-26 (exact metadata in `provenance/afp-quicksort-cost-source.json`); and Blelloch–Ferizovic–Sun's *Joinable Parallel Balanced Binary Trees*, DOI <https://doi.org/10.1145/3512769>, local `book-source/joinable-2022.pdf`, SHA-256 `c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`. The paper's relevant proof is on article pp.7:24–28. These identities are retained provenance, not fresh retrieval or rehashing in this pass.

Actual saved source declarations reread here are in `conaled-permutation-joint/Applications/Probability/PermutationExpectation.lean` and `PermutationOrder.lean`; the existing Mathlib pin is `56a005855ea17e0b0958f73ec801ae140b0a1679`. The saved source is unaccepted. Source inspection does not establish elaboration or execution of those declarations.

## 2. Actual observations and exact premise split

Let `positions : List I` be Nodup and complete: every index belongs to it. This supplies finiteness locally without a new public enumeration record or an extra `Nonempty I` premise. The permutation space is nonempty even for an empty index type. Preserve the original key-to-label orientation: a sampled `π : Equiv.Perm I` sends a key to its assigned label, so the actual ordered key list uses `π.symm`.

For one **fixed** `A : Finset I`, use the existing operations, with abbreviations only in this report:

```text
μ       = uniformOn (univ : Set (Perm I))
O_A π   = restrictedOrder positions A π
        = (positions.map π.symm).filter membership-A
C_A π   = beforeCount priority A π
        = Set.ncard {b | ∀ a ∈ A, priority (π b) < priority (π a)}
N       = Nat.card I
s       = A.card.
```

`restrictedOrder` and `orders` are the existing XU02 definitions (`PermutationOrder.lean`, lines 55–63). `beforeCount` is the existing XU04 definition (`PermutationExpectation.lean`, lines 40–46). It is a mathematical `Set.ncard` observation, not a newly instrumented algorithm or a claim about the work needed to compute the count.

| Claim | Exact mathematical premises and limits |
|---|---|
| `IndepFun C_A O_A μ` | A fixed complete Nodup `positions`, fixed `A`, fixed `priority`, the original uniform permutation law, and the finite sample measurability hypotheses. Only an `LT P` relation is needed for invariance/independence. No priority injectivity or nonempty-A premise is needed. |
| Count excludes every member of A; `C_A ≤ N−s` | Irreflexivity is needed. The existing public bound uses `[Preorder P]` and `[Finite I]`, with no injectivity or probability premise (`beforeCount_le`, lines 54–66). |
| `E C_A = (N−s)/(s+1)` | Existing XU04 mean requires `[LinearOrder P]` and injective `priority`, with finite I and permutation measurability/singletons (`lintegral_beforeCount_uniformOn`, line 116; `integral_beforeCount_uniformOn`, line 155). Natural subtraction precedes the cast. |
| `C_A+1` is the first ordinal position of A | A nonempty A and a genuine rank equivalence `rank : I ≃ Fin U`, with the existing actual minimum-image bridge `beforeCount_rank_eq`. It is not an arbitrary numeric priority minimum. |
| `O_A` is the priority order used by a source algorithm | An additional pointwise bridge between `positions` and increasing priority order, or an appropriate fixed rank enumeration. Uniformity and count/order independence alone do not supply that semantic interpretation. |

In particular, **under a bare `LT P`, calling `C_A` an outside-key count is unjustified**: the relation can satisfy `x < x`, and then members of A can belong to the counted set. The full-A zero claim requires a lawful irreflexive relation. With ordinary tied priorities the lawful count is still defined, and independence still holds, but the injected-priority mean need not hold.

Neither an order nor measurability on I or P is needed for the abstract independence. `restrictedOrder` needs its usual equality decision on I. A scalar fiber statement requires only the permutation sample's measurable structure and measurable singletons. `IndepFun` additionally names a target measurable space for `List I`; weight composition must respect that space, or the scalar weighted proof may use a local discrete list space. No new global measurable instance should be introduced.

The enumeration need not increase numeric priority for the independence theorem itself. This matters when using a weight `g(O_A)` to represent a treap shape, search path, or another actual algorithm observation: if the displayed list order differs from priority order, that representation still needs a proof. Applying the count-mean theorem itself to an injective negative or gappy priority function needs only its established injectivity, not a monotone enumeration.

## 3. Small proof route and actual-law transfer

The retained A-preserving symmetry is sufficient for this aggregate client. Let `σ : Perm I` preserve A setwise, and act on a sample by `π ↦ π * σ.symm`. Then

```text
O_A (π * σ.symm) = (O_A π).map σ
C_A (π * σ.symm) = C_A π.
```

For the count equality, if `D(π)` is its defining set, the exact set transport is `D(π * σ.symm) = σ.symm ⁻¹' D(π)`. Bijectivity preserves `Set.ncard`. The universal comparisons are reindexed over A; no order law or injectivity of `priority` enters this argument. The inverse direction in this set equation is consequential and remains as in the separately assessed original report.

For any event E invariant under these relabelings, the existing transitivity between supported internal lists makes every slice `E ∩ {π | O_A π = xs}` have equal mass. The slices partition E. The resulting scalar identity is

```text
μ (E ∩ {π | O_A π = xs})
  = if xs ∈ orders positions A
    then μ E / (s! : ENNReal)
    else 0.
```

Normalize by the positive finite factorial, **not by μ E**. Thus the fiber identity includes null events, empty A, and an empty universe. Its concrete count instances take `E = {π | C_A π ∈ Q}`. Summing supported fibers yields the ordinary `IndepFun` statement; the two marginal laws alone would not yield this joint fact.

The original order module's relabeling helpers are private. A small invariant-event theorem in that same module can reuse them while preserving existing statements. A separate concrete client can import the order and expectation modules and use ordinary Mathlib independence/integration. There is no need to export all proof helpers or create a general symmetry framework. The stronger interface allowing invariance only under permutations fixing A's complement pointwise is feasible, but it is **not necessary for this aggregate beforeCount client** and is deferred here. No named-B count is added to motivate it.

For a generic environment `Ω` and current measure `ν`, a reusable transport premise is the actual

```text
HasLaw Π (uniformOn (univ : Set (Perm I))) ν,
```

where `Π : Ω → Perm I`. The conclusion concerns **the actual composite observations** `C_A (Π ω)` and `O_A (Π ω)`. This premise provides the full global law required by the proof. Existing `HasLaw` transport can carry the finite-target joint relation, moments, and genuine integrability back to Ω; Ω itself need not be finite. It must not be weakened to `HasLaw (O_A ∘ Π) (uniformOn (orders positions A)) ν`, which says nothing about placement among other keys.

This is also not permission to reassert the full global-law premise under a recursively conditioned measure. Even conditioning on a specified first member of A generally changes the global permutation law; any surviving count distribution in that case is a consequence of the original independence and the special form of the event, not a new uniform-environment premise.

## 4. Weighted benefit without a new cost model

For an order-only weight `g`, the concrete equality is

```text
Eμ[C_A * g(O_A)] = Eμ[C_A] * Eμ[g(O_A)].
```

The expectation on the right is the mean of the actual existing count. With XU04's injective linear-priority hypotheses this becomes

```text
Eμ[C_A * g(O_A)] = ((N−s)/(s+1)) * Eμ[g(O_A)].
```

The finite global sample gives genuinely integrable real-valued composites and their product, even if a real `g` is unbounded on all lists. In the generic Ω formulation, transport this integrability from the finite permutation target; do not invoke finite-source integrability on an arbitrary Ω. Equality allows signed real weights. To multiply a coefficient upper bound into an inequality, require nonnegativity on the supported order lists (or the corresponding almost-everywhere condition).

An ENNReal version may allow infinite weights and infinite lower integrals, using the usual `0 * ∞ = 0` convention. This is a separate correctly typed consequence of independence, not a reason to silently coerce an extended expectation into a real integral. The original report already identifies the existing Mathlib product-integral APIs; this source preparation does not require a new integration abstraction.

Composition gives the analogous factorization for `C_A+1`. With a nonempty subset and a genuine rank bridge its mean coefficient is `(U+1)/(s+1)`, as in XU04. No first-position interpretation exists for empty A, and no general formula for the expected raw numeric minimum follows. A logarithm of a position would require its own expectation bound and analytic premises; it is not additional scope for this unit.

The weight restriction is substantive. An arbitrary random work charge may depend on placement, outside priorities, adaptive interval membership, or previously revealed history. Such a weight is not automatically `g(O_A)`. Neither its nonnegativity nor its boundedness alone makes the factorization valid.

## 5. Conditioning directions and reused connected cases

Two different consequences must remain separate:

| Event under the original global law | What a positive-event consequence preserves | What it does not preserve |
|---|---|---|
| H depends only on this fixed `O_A` | The full distribution of `C_A`, hence its mean. A specified first member of A is an instance. | The unconditional distribution of `O_A`, or the full global permutation law. |
| E is invariant under A-preserving relabelings | The uniform internal-order law of `O_A`, by the invariant-event fibers. A count event is an instance. | The original count distribution or count mean. E may select exactly one placement outcome. |

A normalized conditional probability conclusion requires positive event mass. The unnormalized fiber identity itself covers zero events, so no arbitrary null-event normalization should be presented as a probability law. These consequences can be connected examples using existing conditioning APIs; a new public conditional wrapper is unnecessary for the first unit.

Reuse the original report's Fin3 example with `A={0,1}`, identity rank, and `positions=[0,1,2]`. The recorded marginal count law and the intended new joint law give:

| Actual `O_A` | `C_A=0` joint mass | `C_A=1` joint mass |
|---|---:|---:|
| `[0,1]` | 1/3 | 1/6 |
| `[1,0]` | 1/3 | 1/6 |

Each order has mass 1/2; the count mean is 1/3. For `g([0,1])=2` and `g([1,0])=5`, the expected weight is 7/2, the count-weight mean is 7/6, and the `(C_A+1)`-weight mean is 14/3. These tests must observe the actual count and actual restricted list and invoke the new joint/weighted result, rather than independently defining the desired numeric distribution.

The same table gives two concise conditional checks without another enumeration:

- On `H={O_A=[0,1]}` (mass 1/2), the count probabilities remain 2/3 and 1/3.
- On `E={C_A=1}` (mass 1/3, equivalently key 2 first globally in this example), the two internal orders still have probability 1/2 each, while the count mean becomes 1. Uniform internal order therefore cannot transport the old mean 1/3.

For a placement-dependent weight `W=C_A`, the same example has `E[C_A W]=1/3` while `E[C_A] E[W]=1/9`. This is a direct boundary to arbitrary-weight extraction.

The already saved XU04 boundary remains useful: take fixed `A={1}` in Fin3 and condition on key 0 first globally. The two global orders `[0,1,2]` and `[0,2,1]` are equally likely. The actual count is 1 or 2, with mean 3/2 instead of its original mean 1, while `O_A=[1]` under both measures. A relative-order HasLaw alone is insufficient even when it is exact and unchanged. Similarly the saved adaptive singleton `A(π)={π.symm 0}` has count zero for identity rank; it does not satisfy the fixed-A theorem's premises.

Additional boundary obligations for any eventual small unit can reuse existing cases: empty A gives count N and order `[]`; empty I gives one permutation and count zero; full A has count zero under a lawful irreflexive order; a fixed singleton can have a nonconstant count despite constant internal order; constant tied priorities preserve independence but fail the injected-priority mean for a proper singleton. The bare-LT theorem must not silently strengthen the full-A zero conclusion.

## 6. Source benefit and what remains open

### Chapter 2: no new prerequisite for the mean proof

C02-024 retains the book's average-input and randomized-pivot assertions in §2.3, printed pp.16–17. The saved AFP correspondence and the newer conditional-mean plan already distinguish them. For average input, the actual list is `O_S π`, and on a specified first-key event the source's two comparator filters must be proved equal to the corresponding fixed membership filters of the remaining order. XU03 supplies their conditional marginal laws. Linearity and actual finite-measure integrability suffice for the expectation recurrence; XU05's disjoint product law is stronger than that mean-only argument needs, and this new placement independence is unnecessary for it.

The measured two-way recurrence still needs its actual empty cost 1 and nonempty comparison/filter/entry tariff `4*(n−1)+3`, together with the uncharged-append qualification. The distinct-key and lawful-comparator assumptions, actual recursive partition lengths, harmonic solution, randomized occurrence sampling/removal, duplicate-bearing quadratic family, and append/choice-cost distinctions remain algorithm-specific. A fixed-global placement theorem does not certify any of them. The proposed unit must not become an artificial prerequisite or substitute for those C02 obligations.

### Chapter 10: a valid fixed-law weighted tool, not C10-117

The retained paper model fixes the two input key sets before sampling one global distinct ranking of their union; common keys receive the same priority in both trees. When the universe is that fixed union and the strict order is lawful, aggregate `C_A` automatically counts the relevant keys outside A; no separate selected-B counter is needed for that top-level observation. A simple pointwise join-depth domination by `C_A+1` can then use the fixed-law mean, and a proven order-only weight can use the new factorization. The operation/value and priority-order bridges must still identify those actual variables.

The source's recursive weighted work does not automatically have that form. In particular, the retained treap report refutes transporting the constant root-position bound to every ancestor-conditioned descendant. Its fixed-input family reaches a subproblem `(S,B)` after exposing k lower A keys and has

```text
E[local first position of S | ancestor event]
  = 1 + s*(k+1)/(k+t+1),  where |S|=t and |B|=s.
```

The choice `t=2s`, `k=4s²` still lies in the strict larger-subproblem branch and gives a mean at least `1+(2/3)s`. This does not contradict the new theorem: an event determined by the larger A-order is not necessarily determined only by the descendant S-order, and the desired observation is the descendant's placement. Fixed initial sets do not imply the original global law at every recursive call.

The paper's random rank-cluster factor and weight also require the separate fixed-key/frontier conditional analysis recorded in `treap-conditional-work-preflight.md`, not an unsupported extraction of `E[d]` from `E[d Z]`. The proposed frontier proof uses current-order and disjoint-group laws, conditional harmonic path charges, and a conditional cluster bound; the displayed unconditional factorization is not a replacement. The actual paper/book `join2` recurrences, common logarithmic charge versus literal join≤split claim, rank-window coverage, actual recurrence costs, and final layer sum remain open. No part of C10-117 is accepted or silently reclassified by this preparation.

### Relationship to XU04/XU05

XU04 supplies the existing aggregate count, its lawful bound, its actual unconditional mean, and the ordinal bridge. The new missing fact is their **joint** relationship with internal order. XU05 supplies an actual pair of **internal orders of fixed disjoint subsets**, including the generic `hasLaw_filter_pair positions hnd hcomplete S hY A B hAS hBS hAB`. That generic premise is a uniform whole-order observation under the current environment; it need not give global placement information. Disjoint-order independence therefore cannot be cited as if it already proved the new count/order theorem.

The new fixed-A theorem does not need a second disjoint subset. Where a later client combines it with XU05, the latter retains its own fixed subsets, disjointness, and inclusion premises. Overlapping source input sets retain shared priorities, and recursive subsets that become fixed only on a history atom require the corresponding conditional laws. No general adaptive-set or whole-history result follows from either unit.

## 7. Bounded next steps if scope is later frozen

1. Reuse the original A-preserving relabeling proof and establish the invariant-event fiber identity, with null-event, empty-subset, and empty-universe normalization handled explicitly.
2. Prove the exact existing `beforeCount` invariance and derive ordinary count/order independence. Transfer it through an actual full-global-permutation HasLaw if that interface is retained; do not weaken that premise to a marginal order law.
3. Connect the existing XU04 mean and genuine integrability to the weighted identity. Keep the count-plus-one and selected-order conditional statements as ordinary consequences unless a concrete client warrants more public surface.
4. Use the retained Fin3 joint and weighted observations plus the meaningful global-head/adaptive/placement-weight boundaries. No new exhaustive enumeration or general probability framework is needed.

These are proposed proof tasks, not authorization to implement them. The original placement report and separate source assessment remain unchanged. No source inventory, frozen requirement, tracker state, chapter order, gate, or acceptance status was modified.
