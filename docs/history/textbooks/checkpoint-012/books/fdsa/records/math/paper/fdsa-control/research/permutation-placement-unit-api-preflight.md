# Fixed placement and internal order: bounded unit API preflight

## Status and recommendation

This is read-only preparation for a possible XU06 unit, not frozen scope, implemented Lean, a compiler result, either final review axis, or chapter acceptance. The sole new report path was checked absent before writing. No repository source, previous report, requirement, ticket, ref, cache, configuration or gate was changed. No compiler, checker, project hash helper, Git operation, remote request or enumeration campaign was run. The old Chapter 1 gate remains unchanged.

**The retained plan still provides the smallest useful route.** Add one ordinary invariant-event fiber law beside the existing private order-fiber proof. Use it to prove independence of the existing aggregate `beforeCount` and the actual `restrictedOrder`. Transport that conclusion from the actual global permutation through Mathlib's existing `HasLaw`, then combine it with the saved count mean and existing product-integral theorems. No shuffle decomposition, new count operation, probability carrier, independence predicate, sampler or executor is needed.

The global-law premise matters. A `HasLaw` for the selected subset's internal order alone cannot supply its placement distribution. Nor does this result justify resetting a recursive treap environment to a uniform global law. The retained C10-117 counterfamily and the separate source assessment remain unresolved source obligations.

Selected-order conditioning should initially be a connected consequence of the new independence result and existing `cond` APIs, not an additional public conditional wrapper. Root clarified that the intended operation remains the aggregate count over all identifiers. There is no new selected-outsider-set count in this proposal.

## 1. Inspected sources and current reusable surface

The conaled source inspected is `conaled-permutation-joint`, reported by root at saved draft `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e`. No Git command was used to establish a new identity. All XU01–XU05 predecessors remain unaccepted. Pinned Mathlib is `56a005855ea17e0b0958f73ec801ae140b0a1679`; all dependency declarations below were read from that local pin.

The following retained records were read in full:

- `research/permutation-placement-order-preflight.md`, root-recorded SHA-256 `3fe9a8d80a6a57faa4265ecb85267216039dae9f39164cf928560c1bae9cba81`.
- `reviews/permutation-placement-order-source-preflight.md`, the separate bounded source assessment. It requested no correction and explicitly did not close C10-117 or freeze an implementation.

Current source reads covered the actual order/count definitions, single-order private relabeling and normalization proof, the relevant XU05 public laws, the complete count/mean/rank module, and the existing private conditional-law transport in the tail module. The current `AGENTS.md` and linked architectural/domain guidance were consulted. This proposal reuses ordinary observations and law transport, separates mathematical domains from examples, and avoids exporting private proof machinery just to cross a module boundary.

| Current declaration | Exact useful contract / limitation |
| --- | --- |
| `PermutationOrder.restrictedOrder positions A π` | `(positions.map π.symm).filter membershipA`; keys map to labels, so observation uses the inverse. |
| `PermutationOrder.orders positions A` | The existing finset of permutations of `positions.filter membershipA`. |
| `restrictedOrder_mem_orders positions hnd hcomplete A π` | Pointwise finite support of the actual observation. |
| `orders_card positions hnd hcomplete A` | Support cardinality is `Nat.factorial A.card`. |
| Private `exists_relabel_orders positions hnd hcomplete A xs ys hxs hys` | Produces `σ`, `xs.map σ = ys`, and `∀ a, σ a ∈ A ↔ a ∈ A`. It need not fix the complement. |
| Private `restrictedOrder_relabel positions A π σ hA` | `restrictedOrder positions A (π * σ.symm) = (restrictedOrder positions A π).map σ`. |
| Private `fiber_mass_eq`; public `uniformOn_restrictedOrder_eq` | Actual source fibers are equiprobable, then normalized over `orders`; off-support mass is zero. |
| `map_restrictedOrder_uniformOn positions hnd hcomplete A` | Actual order pushforward is the existing uniform-on-orders measure; adds list measurable-space/singleton premises. |
| `hasLaw_filter_pair positions hnd hcomplete S hY A B hAS hBS hAB` | XU05 transports disjoint fixed relative orders from an observed whole-order law. It contains no placement-law assertion. |
| `PermutationExpectation.beforeCount priority A π` | `Set.ncard {b \| ∀ a ∈ A, priority (π b) < priority (π a)}`; definition needs only `LT P`. |
| `beforeCount_empty priority π` | Equals `Nat.card I`, with the existing infinite-set-to-zero convention. |
| `beforeCount_le priority A π` | Under `[Finite I] [Preorder P]`, at most `Nat.card I - A.card`; irreflexivity is needed to exclude members of A. |
| `lintegral_beforeCount_uniformOn priority hinj A` / `integral_beforeCount_uniformOn priority hinj A` | Under finite I, lawful linear order and injective priority, mean is `(Nat.card I - A.card)/(A.card+1)`, with Nat subtraction before casting. |
| `beforeCount_rank_eq rank A hA π` | Nonempty-A bridge to the actual minimum of the finite image under `rank ∘ π`, for `rank : I ≃ Fin U`. |
| `integral_firstPosition_uniformOn rank A hA` | Actual one-based ordinal mean `(U+1)/(A.card+1)`; not the mean of arbitrary numeric priority values. |

These declarations do not already imply the desired new joint fact. A marginal count mean and a marginal uniform order law cannot simply be multiplied. XU05's independence of two disjoint internal orders also does not identify the placement coordinate.

## 2. Exact hypotheses and proposed semantic statements

Keep independent universes for identifiers, priorities and the current environment:

```lean
I : Type u
P : Type v
Ω : Type w
```

For order statements retain `[DecidableEq I]`, `positions : List I`, `hnd : positions.Nodup`, and `hcomplete : ∀ a, a ∈ positions`. Completeness supplies `letI := Fintype.ofList positions hcomplete` locally. Do not add public `Fintype I`, `Finite I`, `Nonempty I`, an identifier order or a measurable space on I. The finite permutation sample is nonempty even when I is empty because it contains the identity permutation.

In the formulas below, the following are explanatory abbreviations only, not new proposed definitions:

```text
μ0 = uniformOn (Set.univ : Set (Equiv.Perm I))
O π = restrictedOrder positions A π
B π = beforeCount priority A π
K = orders positions A
q = (Nat.factorial A.card : ENNReal)
```

### 2.1 Ordinary invariant-event fiber law

Proposed call order in the existing order namespace:

```lean
uniformOn_inter_restrictedOrder_eq
  positions hnd hcomplete A E hInvariant xs
```

The event hypothesis is structural, with the exact existing action orientation:

```lean
hInvariant : ∀ (σ : Equiv.Perm I),
  (∀ a, σ a ∈ A ↔ a ∈ A) →
  ∀ π, (π * σ.symm ∈ E ↔ π ∈ E)
```

The conclusion is:

```text
μ0 (E ∩ {π | O π = xs})
  = if xs ∈ K then μ0 E / q else 0.
```

Only the permutation sample needs `[MeasurableSpace (Equiv.Perm I)]` and `[MeasurableSingletonClass (Equiv.Perm I)]`. No list or priority measurable structure is involved. E need not be separately assumed measurable: it is a subset of the finite discrete sample. No positivity assumption on E is permitted here; the scalar identity includes null events. The denominator is the finite positive factorial, never the event mass.

This theorem has semantic use beyond a proof-only extension witness: it says how the actual order observation slices a structurally invariant event. Its concrete immediate client is every event determined by the existing B.

### 2.2 Deterministic count invariance

Proposed ordinary observation law:

```lean
beforeCount_relabel priority A π σ hA
```

with only `[LT P]`, and

```lean
hA : ∀ a, σ a ∈ A ↔ a ∈ A
```

concluding

```text
beforeCount priority A (π * σ.symm) = beforeCount priority A π.
```

It needs no finite I, decidable equality, injectivity of priority, order laws, inhabited type or measurable structure. In particular it preserves the actual `Set.ncard` convention on infinite sets. A local `classical` proof may supply decision procedures; the theorem need not expose them.

### 2.3 Independence under the actual global law, on arbitrary Ω

A useful minimal public conclusion is the existing `IndepFun` predicate for the actual composites:

```lean
indepFun_beforeCount_restrictedOrder
  positions hnd hcomplete priority A hΠ
```

Here implicit `Π : Ω → Equiv.Perm I` and `μ : Measure Ω` have premise

```lean
hΠ : HasLaw Π
  (uniformOn (Set.univ : Set (Equiv.Perm I))) μ
```

and conclusion

```text
IndepFun (fun ω => B (Π ω)) (fun ω => O (Π ω)) μ.
```

Besides `[LT P]`, this needs the supplied measurable space on Ω, the permutation measurable-space/singleton pair used by μ0, and a measurable space on `List I` to state `IndepFun`. **List measurable singletons are not needed for this direct event formulation.** There is no finite-Ω, strong `Measurable Π`, source-probability, priority-measurability or global-order premise to add. `HasLaw` already gives `AEMeasurable Π`; normalization of μ can be derived when a later calculation needs it.

Specializing `Π := id` and `hΠ := HasLaw.id` recovers the original canonical law without a second public theorem. A suffix such as `_of_hasLaw` would be a naming choice at freeze time, not a new mathematical interface.

### 2.4 Source-use weighted mean

The useful new weighted real statement substitutes the existing explicit count mean. Proposed call order:

```lean
integral_beforeCount_mul_order
  positions hnd hcomplete priority hinj A g hΠ
```

where `[LinearOrder P]`, `hinj : Function.Injective priority`, `g : List I → ℝ`, and hΠ is exactly the full global-law premise above. Its conclusion is

```text
∫ ω, (B (Π ω) : ℝ) * g (O (Π ω)) ∂μ
 = (((Nat.card I - A.card : Nat) : ℝ) / ((A.card + 1 : Nat) : ℝ))
     * ∫ ω, g (O (Π ω)) ∂μ.
```

The real equality permits signed g. It needs no public measurable space on lists and no global bound or measurability assumption on g: the canonical permutation source is finite, so the actual compositions and product are integrable, and that fact transfers through hΠ. A proof can select a local discrete list measurable space when applying `IndepFun.comp`.

An ENNReal version, proposed name `lintegral_beforeCount_mul_order` with the same argument order, is equally sound and permits infinite weights. It need not be frozen automatically if the first source client only needs the real theorem. The generic un-substituted factorization is already a Mathlib consequence of `IndepFun`; it does not need another public wrapper. A bound using an upper bound on the coefficient additionally needs nonnegativity of g on K, not necessarily on every list. Count-plus-one and actual ordinal weighted formulas can initially remain existing-API consequences.

All names in this section are proposals, not declarations added by this investigation.

## 3. Small proof route and exact pinned APIs

### 3.1 Reuse the existing event-fiber calculation

Inside `PermutationOrder.lean`, reuse the private `exists_relabel_orders` and `restrictedOrder_relabel` with the existing witness σ. The same bijection `π ↦ π * σ.symm` now transports

```text
E ∩ {π | O π = ys}
```

to the corresponding xs event. The new hInvariant handles the E component; the original mapped-list injectivity argument handles the order component. Existing pinned APIs are unchanged:

- `Group.mulRight_bijective σ.symm`.
- `Set.encard_preimage_of_bijective ...`.
- `uniformOn_univ` and `Measure.count_apply` on the finite measurable source events.

Partition E by the supported orders. The smallest adaptation is to apply the existing finite-fiber theorem under `μ0.restrict E`:

```lean
MeasureTheory.sum_measure_preimage_singleton (s : Finset β) {f : α → β}
  (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) :
  (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s)
```

This is in `Mathlib/MeasureTheory/Measure/Basic.lean`, line 185. Support makes the right side `μ0 E`; the equal-fiber sum is `K.card * sliceMass`. Apply `orders_card`, then the exact pinned cancellation statement from `Mathlib/Basic/ENNReal/Inv.lean`, line 518:

```lean
ENNReal.eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) :
  b = c / a ↔ a * b = c
```

Here a is the cast factorial, not μ0 E. `Nat.factorial_ne_zero` and the finite Nat cast discharge its two premises. The off-support event is empty by the existing pointwise support law. This proof handles A empty and E null without a separate distribution construction.

A small private generalized equal-fiber lemma may replace duplicated lines in the existing private proof. If an implementation chooses to recover the old `fiber_mass_eq` from E=univ, record that old-proof edit and retain every old public statement and case. Exporting the existing extension witnesses is unnecessary.

### 3.2 Count invariance is a set bijection, not an assumed probability law

Let `D π := {b | ∀ a ∈ A, priority (π b) < priority (π a)}`. Reindexing the selected a by σ gives the exact identity

```text
D (π * σ.symm) = σ.symm ⁻¹' D π.
```

This uses only hA and permutation inverse laws. Then use the pinned `Mathlib/Data/Set/Card.lean`, line 842:

```lean
Set.ncard_preimage_of_injective_subset_range
  {s : Set β} (H : Function.Injective f) (hs : s ⊆ Set.range f) :
  (f ⁻¹' s).ncard = s.ncard
```

Take f=σ.symm; its injectivity and surjectivity discharge the hypotheses. No finiteness theorem or default priority is needed. Consequently `E := {π | B π ∈ C}` satisfies hInvariant for every set C of natural counts.

The existing A-preserving action may move named outside identifiers. The proof preserves the **aggregate count** by a bijection of those identifiers; it does not prove invariance of each named outsider's individual event.

### 3.3 From count fibers to existing independence

The exact pinned event criterion is `ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul` in `Probability/Independence/Basic.lean`, line 643:

```lean
IndepFun f g μ ↔
  ∀ s t, MeasurableSet s → MeasurableSet t →
    μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t)
```

For a count event E and any list event H, sum the invariant-event fiber formula over `K.filter (fun xs => xs ∈ H)`. The same finite-fiber theorem for μ0 supplies the order-event marginal. Pull out μ0 E with `Finset.mul_sum`. This proves the event criterion without adding a full product-map theorem or needing measurable list singletons. All canonical preimages are finite measurable sets, even if the caller's list measurable space is coarse.

To transfer it to the actual Π on arbitrary Ω, use the pinned `HasLaw.measure_eq` for each canonical intersection and marginal event:

```lean
HasLaw.measure_eq (hX : HasLaw X ν μ)
  {p : β → Prop} (hp : MeasurableSet {x | p x}) :
  μ {ω | p (X ω)} = ν {x | p x}
```

This is `Mathlib/Probability/HasLaw.lean`, line 48. `measurable_of_finite` supplies all canonical event measurability using the local finite enumeration and the supplied permutation singleton class. The proof never upgrades Π to strongly measurable and never replaces it by a new independent draw.

If a client wants a product-law statement, existing `indepFun_iff_map_prod_eq_prod_map_map` (Basic, line 702) and `indepFun_iff_hasLaw_prodMk_prod` (HasLaw, line 243) already supply it under finite source measure and the component AEMeasurable/HasLaw premises. That does not justify another public wrapper in this unit.

## 4. Integration and actual-law transport

The relevant exact pinned declarations are already present:

| Declaration | Important premises and result |
| --- | --- |
| `HasLaw.isProbabilityMeasure` | A probability target plus hΠ gives `IsProbabilityMeasure μ`; no finite Ω is required. |
| `HasLaw.comp` / `HasLaw.fun_comp` | A law of a function on the target, then hΠ, transports that actual composition. |
| `HasLaw.integrable_comp hΠ hf` | `Integrable f μ0` gives `Integrable (f ∘ Π) μ`. |
| `HasLaw.integral_comp hΠ hf` | For `hf : AEStronglyMeasurable f μ0`, `∫ ω, f (Π ω) ∂μ = ∫ π, f π ∂μ0` (up to ordinary composition notation). |
| `HasLaw.lintegral_comp hΠ hf` | For ENNReal f and `AEMeasurable f μ0`, the analogous lower-integral equality. |
| `Integrable.of_finite` | `[Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ]` gives integrability of real-valued f on α. |
| `IndepFun.comp hfg hφ hψ` | Independent f,g stay independent after measurable component maps φ,ψ. |
| `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX hY hXY` | AEMeasurable ENNReal X,Y and their independence give product factorization; no finite-positive-weight premise. |
| `IndepFun.integral_fun_mul_eq_mul_integral hXY hX hY` | For real X,Y with the stated AEStronglyMeasurable premises, gives the ordinary product-integral identity. |

Primary locations: `HasLaw.lean` lines 101–120 and 161–180; `MeasureTheory/Function/L1Space/Integrable.lean` line 171; `Probability/Independence/Basic.lean` lines 755–766; `Probability/Independence/Integration.lean` lines 130–133 and 423–426. The real API itself is broader than the intended client; the new source statement should still establish genuine integrability of the composites and product, not rely on default values of a nonintegrable integral.

A small robust proof order is:

1. On the finite canonical permutation space, obtain integrability of `B`, `g ∘ O` and their product using `Integrable.of_finite`.
2. Apply the new count/order independence and existing measurable composition/integration. A local top list measurable space makes arbitrary g measurable; local finiteness of I gives countability of `List I`. This local choice does not add a public list-measurability premise to the scalar integral statement.
3. Substitute XU04's exact unconditional count mean, retaining lawful linear order and injectivity.
4. Transport each actual integral and its integrability through hΠ. This handles infinite or non-discrete Ω with only the original AEMeasurable HasLaw premise.

For ENNReal weights, repeat with the lower-integral API. Infinite weights are allowed with the existing ENNReal convention `0 * ∞ = 0`. No division by a weight or by an event mass occurs. The real coefficient uses Nat subtraction before casting, and its denominator `A.card+1` is positive. For an actual ordinal result use `beforeCount_rank_eq` with `A.Nonempty`, then add one; do not replace B by a minimum numeric priority without a separate value bridge.

## 5. Positive conditioning: valid consequences, no extra wrapper required

There are two different consequences. Keeping them separate prevents the unchanged-marginal error in later recursive clients.

| Conditioning event of positive mass | What stays unchanged | What may change |
| --- | --- | --- |
| An A-preserving invariant sample event E, for example a predicate of B | O has its original uniform-on-K law. The invariant-event slice formula proves this. | B's law and mean can change. Do not reuse the original count coefficient automatically. |
| An event H(O) determined only by this fixed A's internal order | B has its original law and mean, by independence. | O is conditioned by H, and the full permutation environment generally changes. |

The pinned `Probability/ConditionalProbability.lean` has precisely the required elementary APIs:

```lean
cond_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
  μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)

cond_apply' (ht : MeasurableSet t) (μ : Measure Ω) :
  μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)

cond_isProbabilityMeasure [IsFiniteMeasure μ] (hcs : μ s ≠ 0) :
  IsProbabilityMeasure μ[|s]

cond_eq_zero_of_meas_eq_zero (hμs : μ s = 0) : μ[|s] = 0
```

For canonical samples all events are measurable. Finite probability makes every event mass different from ∞. Thus the invariant-event formula plus `ENNReal.inv_mul_cancel` gives the conditional order fiber formula after a positive E; summing the independence identity gives the unchanged count law after a positive order-only event. These can be demonstrated directly as connected cases. Null conditioning is the zero measure, never a normalized uniform law.

For a later arbitrary-Ω client, do not apply `cond_apply` to a pullback merely because Π is AEMeasurable. Such a pullback can be only null-measurable. The existing private `PermutationTail.hasLaw_cond` already gives the correct short proof route:

```text
HasLaw Π μ0 μ
  ⇒ HasLaw Π (μ0[|E]) (μ[|Π ⁻¹' E])
```

for measurable E in the permutation target. Its proof uses `cond_absolutelyContinuous`, `Measure.map_smul`, and the exact pinned map/restriction theorem:

```lean
Measure.restrict_map_of_aemeasurable (hf : AEMeasurable f μ)
  (hs : MeasurableSet s) :
  (μ.map f).restrict s = (μ.restrict (f ⁻¹' s)).map f
```

This is `MeasureTheory/Measure/AEMeasurable.lean`, line 351. Compose a canonical conditional observation law with this transported law using `HasLaw.fun_comp`. That is a private existing-API calculation, not a need for a new conditional executor or law record. There is no reason to expose the tail module's private helper solely to bypass its scope, or to import tail into the basic order module. Should a later accepted client need a shared semantic conditioning theorem, its scope can be decided then.

Under invariant E, intersecting E with a count event is also invariant. Hence the same calculation can establish count/order independence under that conditioned measure, but its coefficient is the conditioned count mean. This is a proof consequence, not permission to reuse the unconditional XU04 coefficient or an additional proposed public theorem here.

## 6. Why the stronger local-action refinement is deferred

A refinement considered during this pass restricts symmetry to σ that fix every key outside A. That allows events referring to named outside keys. Pinned Mathlib already supports the construction, so no shuffle machinery is necessary:

- `Equiv.Perm.subtypePerm σ hA : Perm {a // a ∈ A}`.
- `Equiv.Perm.ofSubtype : Perm (Subtype p) →* Perm I`.
- `ofSubtype_apply_of_mem`, `ofSubtype_apply_of_not_mem`, and `ofSubtype_apply_mem_iff_mem` in `Mathlib/Algebra/Group/End.lean`, lines 366–465.

Given the current σ, `ofSubtype (σ.subtypePerm hA)` agrees with σ on A and is the identity outside A. It still maps any supported xs to ys. This is a valid use of `subtypePerm` because hA proves that the subset is invariant; it is not a representation of arbitrary relative-order restriction.

The refinement weakens the event-invariance premise but needs an extra localization proof. The concrete aggregate B is already invariant under every A-preserving σ. Root explicitly retained that existing operation and did not request named-outside observations. Therefore the original helper is enough and the local-action extension should remain deferred. In particular, do not silently use the current non-complement-fixing witness to claim that a named outside-key event is unchanged.

## 7. Placement, imports, boundaries and connected cases

### Proposed placement and minimal work

- Extend `Applications/Probability/PermutationOrder.lean` only with the semantic invariant-event fiber result and private proof reuse. Keep all old statements, examples and XU05 behavior intact. It must not import the later expectation or tail modules.
- A small `Applications/Probability/PermutationPlacement.lean` could import the existing order and expectation modules plus `Mathlib.Probability.Independence.Integration`, proving the ordinary deterministic count transport, actual global-HasLaw independence and the source-use weighted identity. The module name is a proposal. If the helper uses `ENNReal.eq_div_iff` directly, its defining supported `Mathlib.Basic.ENNReal.Inv` import is the narrow explicit dependency.
- Keep conditioning, rank/minimum composition and concrete distributions in Examples unless a genuine repeated client needs an additional semantic theorem. Existing `IndepFun`, `HasLaw`, `Measure.map`, `Measure.prod` and integration APIs already express the consequences.

The new formal work is bounded: event slicing, count invariance, actual-law transfer and its explicit weighted source application. It does not require a distribution record, a new operation, a complete joint-position distribution, independent numeric-priority draws, an order-statistic library, arbitrary-history conditioning or a generic expectation framework.

### Boundaries that the statements and cases must retain

- A may be empty. Then O=[] and B=`Nat.card I`; the original global permutation law is normalized, even for empty I.
- For full A, B=0 follows under a lawful strict relation such as `[Preorder P]`. Under arbitrary `[LT P]` the relation might be reflexive, so do not label B an outside count or assert this zero fact at the independence theorem's minimal assumptions.
- Constant tied priorities still satisfy the independence conclusion but invalidate the injective-priority mean specialization when the selected set is a proper nonempty subset.
- A nonsorted complete positions list still defines a valid order observation independent of B. Identifying it with increasing numeric-priority order needs the same separate value bridge as XU02.
- A fixed g of O is allowed. A weight depending on B, an adaptive choice of A, or a function of unspecified recursive history is not justified merely by the new theorem.
- The generic premise is `HasLaw Π μ0 μ`. `HasLaw (O ∘ Π) uniformOrders μ` is strictly insufficient, including when it is obtained from XU03 under a changed environment.
- Positive-event hypotheses are needed only for normalized conditional consequences. The scalar event-fiber formula itself handles zero events without cancellation.

### Reuse the retained small cases; no new enumeration is needed

For Fin 3, A={0,1}, standard ranks and positions, the saved count law has B=0 with mass 2/3 and B=1 with mass 1/3. The two orders [0,1] and [1,0] each have mass 1/2. Their joint cells have masses 1/3 and 1/6 respectively. A useful checked client should invoke the new event theorem for at least one actual count/order cell, not merely recompute unrelated fractions.

Taking g([0,1])=2 and g([1,0])=5 gives mean weight 7/2 and mean product 7/6. Adding one to the actual count gives mean weighted position 14/3. These are the retained arithmetic expectations, not results newly enumerated or validated here. The main weighted theorem should be used to derive one of them, retaining the actual g composed with the actual order.

The same case distinguishes the two conditioning directions. E={B=1} has mass 1/3 and leaves the order half/half while changing the count mean to 1. H={O=[0,1]} has mass 1/2 and preserves the count masses 2/3,1/3. Existing `cond_apply`, the new scalar law and `IndepFun.measure_inter_preimage_eq_mul` suffice; no extra public conditional wrapper is needed.

The already saved Fin 3 singleton boundary is stronger than a fresh abstract counterexample: for A={1}, conditioning on global first key 0 leaves the selected order identically [1], yet B is 1 or 2 with equal probability, mean 3/2 rather than the unconditional mean 1. This is the actual changed environment from XU04's boundary module, not an independent substitute draw. It demonstrates why a uniform internal-order HasLaw cannot be promoted to a global-placement law.

Empty/full/tied cases can reuse the existing XU04 boundaries; the new independence conclusion adds a real connection rather than replacing them. A generic-Ω client may take a measurable environment with an actual Π having the specified global law, or specialize the theorem to id; no finite environment premise should appear in its signature.

## 8. Remaining work and stop condition

No mathematical obstruction was found for the bounded fixed-set unit. The substantive remaining Lean work would be the event-restricted finite normalization, the inverse-image count transport, the finite-order sum for `IndepFun`, and the actual HasLaw/integrability compositions. Exact casts, local instances, function-composition notation and ENNReal normalization still need compilation under the matching future candidate; source inspection does not certify elaboration.

No conditional treap complexity theorem follows automatically. The client must prove that its actual weight is a function of this fixed A's order, that its placement variable is the existing aggregate count or a proved ordinal specialization, and that the relevant global-law or event-invariance premises hold. The retained recursive counterfamily prevents assuming those premises from subtree size or a uniform internal-order marginal. C10-117 and the later coarse-history/search-path argument remain separate.

This report is the only file written in the pass. Its byte/line identity is reported to root for the next coordinated capture; no source hash helper or acceptance action was run. Edits stop after this report.
