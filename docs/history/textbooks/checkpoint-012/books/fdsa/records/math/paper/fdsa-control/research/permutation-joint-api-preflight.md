# Fixed disjoint subsets: joint relative-order API preflight

## Status and scope

This is read-only preparation for a possible next shared unit. It does not freeze requirements, implement Lean, activate a chapter, or accept any earlier draft. The inspected checkout is `conaled-permutation-expectation`, candidate base `11923e9ffd17246b6f22c5594002a1ba0434e43c`. Mathlib is pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679`; the saved Lean list source is from `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Existing project drafts are still uncompiled/unaccepted. No compiler, project hash helper, Git mutation, cache/gate change, or repository-source edit was made for this note.

The companion source assessment is `research/permutation-joint-source-preflight.md`, SHA-256 `83bbceb6a6f74434b80e3eec13d3bc59a8f21025ae3a93b1f387b3a8ccf86f64`. Root's named-case calculations are `research/permutation-joint-calculations.json`, SHA-256 `a7c8be932999da48c13c7291dbd68ee013d3ab1d7da65a978a2d7c8f9463bad4`. They are independent mathematical expectations for the specified cases, not Lean validation. No enumeration was rerun here.

## Recommendation

Extend the existing `Applications.Probability.PermutationOrder` namespace in `Applications/Probability/PermutationOrder.lean` with three semantic results:

1. The universal joint-output fiber formula for two fixed disjoint subsets.
2. The map of the actual pair observation is the product of the two existing uniform order laws.
3. An ordinary `HasLaw` transfer for the actual pair of filters of a uniformly distributed whole order, under an arbitrary current environment measure.

Keep the observation as an ordinary pair of existing `restrictedOrder` calls, and keep both factors as the existing `uniformOn (orders positions T)`. No new order carrier, ranking record, sampler, executor, independence predicate, or uniform-distribution framework is needed.

Adding the results to the existing module lets the proof reuse its private finite-list extension and relabeling helpers without exporting implementation machinery. A later candidate can add private pair-specific lemmas and a small shared local calculation where it actually avoids duplication. It need not generalize the old scalar proof into an abstract finite-action framework. The previous commits remain unchanged; any later extension needs the existing XU02 cases and gates as well as its new cases. The module description must then state the new disjoint joint law accurately, replacing its current blanket sentence that the module does not assert independence.

Likely direct additional dependencies are `Mathlib.Data.Finset.Prod` and `Mathlib.Probability.HasLaw`. The latter already brings the ordinary product-measure machinery at this pin. The directly used product declarations live in `Mathlib.MeasureTheory.Measure.Prod`; an explicit import of that module is also reasonable if needed by the final dependency presentation. No broad `Mathlib` import is proposed. Import closure and elaboration remain for the later permitted build.

## Proposed public statements and argument order

Write, only within this note:

- O_T(π) = `restrictedOrder positions T π`.
- η_T = `uniformOn (orders positions T : Set (List I))`.
- μ₀ = `uniformOn (Set.univ : Set (Equiv.Perm I))`.

All three results retain `[DecidableEq I]`, an ordinary `positions : List I`, `hnd : positions.Nodup`, and `hcomplete : ∀ a, a ∈ positions`. These are the established XU02 interfaces. A local `Fintype.ofList positions hcomplete` supplies the finite index enumeration in proofs. There is no public `Fintype I`, `Finite I`, `LinearOrder I`, `Inhabited I`, or measurable structure on I.

### 1. Universal source fiber

Suggested call:

```lean
uniformOn_restrictedOrder_pair_eq
  positions hnd hcomplete A B hAB xs ys
```

Premises additionally are `hAB : Disjoint A B`, `[MeasurableSpace (Equiv.Perm I)]`, and `[MeasurableSingletonClass (Equiv.Perm I)]`. The statement is:

```lean
μ₀ {π | (restrictedOrder positions A π,
           restrictedOrder positions B π) = (xs, ys)} =
  if xs ∈ orders positions A ∧ ys ∈ orders positions B then
    ((Nat.factorial A.card * Nat.factorial B.card : Nat) : ℝ≥0∞)⁻¹
  else 0
```

The tuple equality is equivalent to the conjunction of the two component fiber equations. This formulation directly matches the finite partition used in the proof. It needs no measurable structure on output lists or their product. The all-output formula already supplies off-support zero; a redundant public zero-probability wrapper is unnecessary.

### 2. Actual pair pushforward

Suggested call:

```lean
map_restrictedOrder_pair_uniformOn
  positions hnd hcomplete A B hAB
```

Add the caller's `[MeasurableSpace (List I)]` and `[MeasurableSingletonClass (List I)]`. Use the canonical product measurable space on `List I × List I`; do not request an unrelated additional product-space instance.

```lean
μ₀.map (fun π => (restrictedOrder positions A π,
                  restrictedOrder positions B π)) =
  (uniformOn (orders positions A : Set (List I))).prod
    (uniformOn (orders positions B : Set (List I)))
```

The observations on the left use the same π. The right side identifies their actual law; it does not replace the experiment with two fresh samples.

### 3. Generic observed-law client

Suggested call, consistent with the earlier filter-client convention:

```lean
hasLaw_filter_pair_of_hasLaw
  positions hnd hcomplete S hY A B hAS hBS hAB
```

For `{Ω : Type*} [MeasurableSpace Ω]`, `{μ : Measure Ω}`, `{Y : Ω → List I}`, the premise and conclusion are:

```lean
hY : HasLaw Y
  (uniformOn (orders positions S : Set (List I))) μ

hAS : A ⊆ S
hBS : B ⊆ S
hAB : Disjoint A B

HasLaw
  (fun ω => ((Y ω).filter (fun a => decide (a ∈ A)),
             (Y ω).filter (fun b => decide (b ∈ B))))
  ((uniformOn (orders positions A : Set (List I))).prod
    (uniformOn (orders positions B : Set (List I))))
  μ
```

Only the list measurable-space/singleton premises accompany the generic theorem. A discrete permutation-sample space can be introduced locally in its canonical proof; it is not a public premise. There is no finiteness assumption on Ω, no requirement that μ be a global uniform permutation law, and no stronger `Measurable Y` premise. `HasLaw` already supplies exactly the required `AEMeasurable Y μ`.

There is no requirement that A ∪ B equal S or the whole index population. The discarded labels can be nonempty. Empty A, empty B, empty S, and Empty I are valid wherever the stated containment premises hold.

The generic finite-order fact can mathematically be stated more widely without a globally complete enumeration, using only finite relevant support and a separate finite-support measurability proof. That is not needed to serve the current complete-position API. The proposed small unit retains the existing enumeration instead of adding a second support-only proof path.

## Reuse in the current project

| Existing declaration | Use |
| --- | --- |
| `restrictedOrder`, `orders` | Actual observation and finite target support; no replacement definitions. |
| `mem_orders` | Each supported list is a permutation of the corresponding filtered base list. |
| `orders_nonempty` | Every target support, including the empty-subset support, is nonempty. |
| `restrictedOrder_mem_orders` | The actual pair always lies in the Cartesian product of supports. |
| `orders_card` | The two support cardinalities are A.card! and B.card!. |
| `filter_restrictedOrder_of_subset` | The two filters of O_S are O_A and O_B under A,B ⊆ S. |
| `map_restrictedOrder_uniformOn` | Transports the new canonical pair result to the existing whole-S law. |
| private `exists_map_eq_of_nodup` | Extends a positionwise map between two concatenated orders to one global permutation. |
| private `restrictedOrder_relabel` | Establishes the correct key-to-label orientation for each component under relabeling. |
| private `fiber_mass_eq` | Existing proof pattern for invariant count measure and normalization; it is scalar, so a pair proof is genuinely additional. |

The private helpers occur at lines 151 and 186 of the inspected module; the scalar fiber and map declarations occur at lines 232 and 295. Their privacy is a reason for colocating this directly related extension, not a reason to add public helper APIs solely for access.

The later module `PermutationTail.lean` already has a private `filter_hasLaw_orders` with the one-filter transport pattern. The new pair transport can follow that short proof without importing Tail into Order or exposing its private helper. There is no dependency cycle. The public `hasLaw_tail_cond_first` and `hasLaw_filter_tail_cond_first` remain clients of Order.

## Finite relabeling and exact normalization

Let C be `(orders positions A).product (orders positions B)`. Consider any two supported pairs (xs,ys) and (xs',ys').

From `mem_orders`, completeness, and the filtered base Nodup proofs, derive that xs and xs' are Nodup with support A and equal lengths, and ys and ys' are Nodup with support B and equal lengths. Disjoint A B implies `List.Disjoint xs ys` and `List.Disjoint xs' ys'`. Thus xs ++ ys and xs' ++ ys' are Nodup lists of equal length.

Apply the existing private `exists_map_eq_of_nodup` to those concatenations. It supplies a global σ with:

```lean
(xs ++ ys).map σ = xs' ++ ys'
```

Rewrite `List.map_append`, then split the equality using `List.append_inj` and the already proved equal first-component lengths. Obtain `xs.map σ = xs'` and `ys.map σ = ys'`. Membership transport through injective `List.map` proves separately:

```lean
∀ a, σ a ∈ A ↔ a ∈ A
∀ b, σ b ∈ B ↔ b ∈ B
```

No requirement that σ fix the complement or preserve an intermediate S is needed. The canonical proof concerns only A and B. The generic S-client is derived afterward through the existing observation maps.

The established multiplication orientation is:

```lean
restrictedOrder positions T (π * σ.symm) =
  (restrictedOrder positions T π).map σ
```

Use it for T = A and T = B. The bijection π ↦ π * σ.symm transports one supported joint fiber to the other. As in the scalar proof, `Set.encard_preimage_of_bijective`, `Group.mulRight_bijective`, `uniformOn_univ`, and `Measure.count_apply` show equal source masses. This does not need a new global uniform-pushforward theorem.

All actual observations lie in C. Applying `sum_measure_preimage_singleton` to the pair observation partitions the sample space; all terms have the same mass, and their sum is one. `Finset.card_product` and the existing `orders_card` identify C.card with A.card! * B.card!. The same `ENNReal.eq_inv_of_mul_eq_one_left` normalization used by XU02 gives the required reciprocal. Unsupported fibers are empty by component support.

This proof does not calculate interleaving binomial coefficients, the factorial cardinality of the global sample, or a separate extension count. Those are unnecessary intermediate obligations for this law.

### Exact pinned finite APIs

| API and source | Relevant signature |
| --- | --- |
| `List.Nodup.append`, `Mathlib/Data/List/Nodup.lean:176` | `(d₁ : l₁.Nodup) (d₂ : l₂.Nodup) (dj : List.Disjoint l₁ l₂) : (l₁ ++ l₂).Nodup`. |
| `List.nodup_append'`, same file:167 | `(l₁ ++ l₂).Nodup ↔ l₁.Nodup ∧ l₂.Nodup ∧ List.Disjoint l₁ l₂`. |
| `List.append_inj`, saved `book-source/LeanList-Lemmas.lean:1663` | `(h : s₁ ++ t₁ = s₂ ++ t₂) (hl : s₁.length = s₂.length) : s₁ = s₂ ∧ t₁ = t₂`. Equality is the first argument. |
| `Equiv.Perm.exists_extending_pair`, `Mathlib/Logic/Equiv/Fintype.lean:158` | `[Finite α] (f g : α → β) (hf : Injective f) (hg : Injective g) : ∃ σ : Perm β, ∀ a, σ (f a) = g a`. β need not be finite. |
| `Finset.disjoint_left`, `Mathlib/Data/Finset/Disjoint.lean` | `Disjoint A B ↔ ∀ ⦃a⦄, a ∈ A → a ∉ B`. |
| `Finset.mem_product`, `Mathlib/Data/Finset/Prod.lean:61` | `p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t`. |
| `Finset.coe_product`, same file:68 | `(↑(s ×ˢ t) : Set (α × β)) = (s : Set α) ×ˢ (t : Set β)`. |
| `Finset.card_product`, same file:141 | `(s ×ˢ t).card = s.card * t.card`. |
| `sum_measure_preimage_singleton`, `Mathlib/MeasureTheory/Measure/Basic.lean:185` | `(s : Finset β) {f : α → β} (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s)`. No measurable structure on β is needed for this partition. |

## The product target and its singleton equations

The product target should be proved by ordinary measure extensionality; no new uniform-product wrapper is needed.

Establish local `IsProbabilityMeasure η_A` and `IsProbabilityMeasure η_B` using the existing lemma `isProbabilityMeasure_uniformOn`, the finsets' finite-to-set proofs, and `orders_nonempty`. It is a lemma, not an automatic normalization instance for arbitrary finite supports. The local instances also supply `SFinite` for product-measure theorems.

This is substantive: the pinned definition of `Measure.prod μ ν` uses zero as a fallback when ν is not SFinite. Here both factors are explicitly finite probability measures, so the usual product equations apply.

Complete finite I makes `List I` countable, not generally finite. Use `Measure.ext_of_singleton` on the countable pair of lists. At (xs,ys):

1. `Measure.map_apply` reduces the source singleton to the new joint fiber, since the source permutation space is finite with measurable singletons.
2. Rewrite the target singleton as `{xs} ×ˢ {ys}`.
3. `Measure.prod_prod` gives η_A {xs} * η_B {ys}.
4. `uniformOn_apply_finset` and `orders_card` evaluate each factor. If either list is unsupported, the product is zero.
5. For supported outputs, `ENNReal.mul_inv` with the finite positive factorial casts identifies the product of reciprocals with the reciprocal of the cast natural product.

Exact declarations:

```lean
-- Mathlib/MeasureTheory/Measure/Dirac/Basic.lean:60
Measure.ext_of_singleton [Countable α]
  {μ ν : Measure α} (h : ∀ a, μ {a} = ν {a}) : μ = ν

-- Mathlib/Data/Set/Prod.lean:111
Set.singleton_prod_singleton :
  ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)}

-- Mathlib/MeasureTheory/Measure/Prod.lean:234
Measure.prod_prod [SFinite ν] (s : Set α) (t : Set β) :
  μ.prod ν (s ×ˢ t) = μ s * ν t

-- Mathlib/Probability/UniformOn.lean
uniformOn_apply_finset [DecidableEq Ω] {s t : Finset Ω} :
  uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s
```

The signatures above have their enclosing measurable-space hypotheses; `ext_of_singleton` and the uniform finite formulas also use measurable singletons. `prod_prod` itself does not require s or t measurable. The canonical product has `Prod.instMeasurableSingletonClass` when the factors do, from `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`.

The product's finite/probability instances are `Measure.prod.instIsFiniteMeasure` and `Measure.prod.instIsProbabilityMeasure` in `Measure/Prod.lean:313–330`. `ENNReal.mul_inv` has the two explicit side conditions `a ≠ 0 ∨ b ≠ ∞` and `a ≠ ∞ ∨ b ≠ 0`; finite Nat casts suffice for the needed branches. Alternatively the positive factorial facts can discharge zero exclusions.

An existing `ProbabilityTheory.uniformOn_pi [Fintype ι] [Finite Ω]` identifies uniform measure on a finite function-product set with `Measure.pi`. It is not the appropriate shortcut here: the ambient list type is not finite, its output is an ordinary pair, and the theorem alone does not identify the actual shared-permutation observation. Passing through finite-support subtypes and a Fin 2 function encoding would add work that the direct singleton proof avoids.

## Generic HasLaw transport and a changed environment

Let F be the ordinary pair-filter function on lists. Prove privately:

```lean
HasLaw F (η_A.prod η_B) η_S
```

Use local finite enumeration and a local discrete measurable structure on `Equiv.Perm I` only. The list domain is countable with measurable singletons, so `measurable_of_countable F` provides the actual measurability proof.

For the map equation, rewrite η_S backward using the existing `map_restrictedOrder_uniformOn`. Apply:

```lean
Measure.map_map (hg : Measurable g) (hf : Measurable f) :
  (μ.map f).map g = μ.map (g ∘ f)
```

Then `Prod.ext` and two uses of `filter_restrictedOrder_of_subset` identify F ∘ O_S with the actual pair (O_A,O_B). The new pair-map theorem finishes the canonical law.

The public generic result is exactly composition with the supplied observed law. The pinned API is:

```lean
-- Mathlib/Probability/HasLaw.lean:120
HasLaw.fun_comp
  (hOuter : HasLaw F ν η) (hInner : HasLaw Y η μ) :
  HasLaw (fun ω => F (Y ω)) ν μ
```

Thus use `hCanonical.fun_comp hY`. The outer law is the receiver/first argument, and the existing observed law is second. This automatically keeps the almost-everywhere measurability boundary. Do not replace `HasLaw` by bare map equality or force `Measurable Y`.

For conditional recursion, apply the existing XU03 result first:

```lean
hTail := hasLaw_tail_cond_first positions hnd hcomplete S a ha hY
```

Then apply the generic pair result with the support `S.erase a`, observation `fun ω => (Y ω).tail`, and current measure `μ[|firstEvent Y a]`. The output is the actual pair of filters of that same tail. All uses retain the original complete positions list. The partial tail is never supplied as a supposedly complete enumeration of I.

If a concrete example needs original global projections O_A/O_B rather than filtered-tail syntax, the existing on-event tail/restriction value bridges, `ae_cond_of_forall_mem`, and `HasLaw.congr` provide the appropriate almost-everywhere identification. That does not require another public conditional joint wrapper. The law of this observation can be a product even though the full conditioned environment differs from μ₀.

### Existing independence client, without a new wrapper

The pin already has exactly the useful equivalence in `Mathlib/Probability/HasLaw.lean:243`:

```lean
ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod
  [IsFiniteMeasure P]
  (hX : HasLaw X μ P) (hY : HasLaw Y ν P) :
  X ⟂ᵢ[P] Y ↔
    HasLaw (fun ω => (X ω, Y ω)) (μ.prod ν) P
```

A connected example can assemble the two old marginal HasLaws from XU02's map equations and the joint HasLaw from the new pair map, then use:

```lean
(indepFun_iff_hasLaw_prodMk_prod hA hB).mpr hPair
```

For the conditioned-tail client, the existing `hasLaw_filter_tail_cond_first` provides each marginal, while the new generic theorem provides the joint. If the source finiteness instance is not already present, normalize the finite target and use `HasLaw.isProbabilityMeasure` (or `HasLaw.isFiniteMeasure`) to derive it. No new source-normalization premise is needed in the generic public theorem. The alias `IndepFun.hasLaw_prod` gives the reverse direction of the same equivalence; it does not prove independence from marginals alone.

## Consequential cases and scope boundaries

Root's saved named cases are well targeted:

- Fin 4, A = {0,2}, B = {1,3}: both order factors are nontrivial, with each supported pair mass 1/4; malformed left/right lists have mass zero.
- Fin 5, A = {0}, B = {1,2,3}, with label 4 outside the union: unequal support sizes give mass 1/(1!·3!) = 1/6. This checks a proper union and excludes an accidental cover premise.
- Empty/full subsets and Empty I: the empty order support is the singleton containing [], with 0! = 1; Perm Empty is still inhabited by identity.
- The actual first-key-2 conditional tail on Fin 5: the XU03 observed-law premise feeds the generic result under the changed measure. It must not be replaced by a fresh uniform global sample.
- Overlapping subsets with common first key 1: the actual common-first event has mass 1/3 while the product of its two marginal masses is 1/4. This preserves a material boundary to dropping disjointness.

The source note connects the law to the full quicksort cost-distribution argument: pinned AFP `Quick_Sort_Average_Case` uses `partition_random_permutations` and `pair_pmf` at lines 146–153. A recurrence for expectations alone needs only the marginals; the stronger product law is justified by distributional and conditional clients, not by pretending linearity of expectation requires independence.

Fixed disjoint subset laws do not supply arbitrary adaptive-subset independence, arbitrary-history invariants, independent priorities for overlapping treap operands, a cost model, or a weighted charging argument. Later clients still must show that their actual subproblem orders are these observations, that their subset/rank/pivot conventions match, and that every conditioned law used in induction has been proved. XU03 supplies a first-key conditional observed-law step, not uniformity of the whole hidden environment.

## Bounded assessment

No mathematical or pinned-API blocker was found for this three-result unit. The actual new argument is simultaneous relabeling of disjoint supports followed by finite normalization; the map and generic-law layers reuse existing APIs directly.

The concrete remaining implementation risks are routine but real: coercions between finset products and set products, splitting concatenated mapped-list equalities at the correct length, maintaining the π * σ.symm orientation, local normalization instances for arbitrary finite supports, factorial casts in ENNReal, and countable-list/product measurability. The current underlying XU02/XU03 drafts themselves remain uncompiled. This source preflight is not evidence that any prospective Lean proof elaborates or passes conaled's gates.

