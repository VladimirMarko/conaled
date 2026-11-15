# Preceding counts and ordinal first positions: API preflight

Recorded 2026-11-02. This is bounded read-only preparation in the existing
FDSA workflow, following sections 5A–B of
[finite-ranking-api-preflight.md](finite-ranking-api-preflight.md).
No new scope is frozen. Only this note was written; no compiler, project
hash helper, Git mutation, repository source, requirement, ticket, cache or
gate was changed. The current source is the root-reported saved draft
`a0597381f02eddd074ee96cabaa974f2062285f8` in `conaled-permutation-tail`.
It and its dependencies remain unaccepted.

The relevant local contract is
`Applications.Probability.PermutationMinimum.uniformOn_minimumEvent`
(XU01). Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The existing [finite-ranking-calculations.json](finite-ranking-calculations.json)
supplies independent finite examples. No additional enumeration or external
search was performed. Source interpretation is coordinated separately in
[permutation-expectation-source-preflight.md](permutation-expectation-source-preflight.md).
Its completed version, including the conditional placement boundary, has
SHA-256 `b6f0245a6b4b0e585a58b6bba2d7303c79ead487675dce16230d0f4906a97a5e`.
Root subsequently saved bounded arithmetic for that boundary and selected
rank/numeric-priority cases in
[permutation-expectation-calculations.json](permutation-expectation-calculations.json),
SHA-256 `37c25e61646617234caab34968e7c50f6abedcb4b42164eea802f9e7a89997f8`.

## 1. Recommendation

Add at most one ordinary count observation and a small sequence of
deterministic/expectation theorems, plausibly in
`Applications/Probability/PermutationExpectation.lean`. Reuse XU01 directly;
neither the whole-order nor conditional-tail units are needed for this
unconditional expectation. No probability carrier, sampling executor,
selector, expectation record, default key or generic integration framework
is missing.

For fixed priority function `priority : I → P`, fixed `S : Finset I`, and
the existing key-to-priority-label permutation `π`, let

```lean
noncomputable def beforeCount [LT P]
    (priority : I → P) (S : Finset I) (π : Equiv.Perm I) : ℕ :=
  Set.ncard {b | ∀ a ∈ S, priority (π b) < priority (π a)}
```

This operation requires no enumeration, decidable equality, measurable
structure, nonempty index type or order on I. Its finite-count meaning is
used under `[Finite I]`: `Set.ncard` is totalized to zero on infinite sets,
so the operation alone is not an assertion about infinite priority domains.
The probability theorem permits an infinite priority target P.

The recommended public laws, with names still provisional, are:

| Law | Necessary assumptions beyond supplied arguments | Result |
|---|---|---|
| `beforeCount_empty` | `[LT P]` | The count at empty S is `Nat.card I`. |
| `beforeCount_le` | `[Finite I] [Preorder P]` | Pointwise count is at most `Nat.card I - S.card`; injectivity is unnecessary. |
| `lintegral_beforeCount_uniformOn` | `[Finite I] [LinearOrder P]`, injective priority, sample measurable space and measurable singletons | ENNReal mean is the natural complement cardinal divided by `S.card + 1`. |
| `integral_beforeCount_uniformOn` | Same as the ENNReal law | The real integral has the corresponding real value, with genuine finite-sample integrability justified. |
| `beforeCount_rank_eq` | `rank : I ≃ Fin U`, `S.Nonempty` | Count equals the actual minimum assigned rank's zero-based value. |
| `integral_firstPosition_uniformOn` | Rank equivalence, `S.Nonempty`, sample measurable space and measurable singletons | The real mean of the actual minimum rank plus one is `(U + 1)/(S.card + 1)`. |

The expectation statements do **not** need public `[Fintype I]`,
`[DecidableEq I]`, `[Nonempty I]`, a measurable structure on I/P, or
measurability of the priority map. A local `Fintype.ofFinite I` and classical
decisions are enough for proof sums. The rank equivalence supplies finiteness
locally for the ordinal results, so those need no additional public
`[Finite I]`. Finset image uses the existing decidable equality on `Fin U`.

## 2. Exact mean statements and their quantifiers

Write `μ₀ = uniformOn (Set.univ : Set (Equiv.Perm I))` in this note.
There is no proposed new measure definition. Under

```lean
[Finite I] [LinearOrder P]
[MeasurableSpace (Equiv.Perm I)]
[MeasurableSingletonClass (Equiv.Perm I)]
(priority : I → P) (hinj : Function.Injective priority)
(S : Finset I)
```

the two conclusions should be written with unambiguous casts:

```lean
(∫⁻ π, (beforeCount priority S π : ℝ≥0∞) ∂μ₀) =
  ((Nat.card I - S.card : ℕ) : ℝ≥0∞) / ((S.card + 1 : ℕ) : ℝ≥0∞)

(∫ π, (beforeCount priority S π : ℝ) ∂μ₀) =
  ((Nat.card I - S.card : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ)
```

S is fixed before the random sample; no nonempty-S hypothesis is needed.
The natural subtraction is harmless because `S.card ≤ Nat.card I`.
For consumers wanting `(Nat.card I : ℝ) - (S.card : ℝ)`, rewrite using
`Nat.cast_sub` with that proved inequality. Do not silently mix truncated
natural subtraction, real subtraction, and ENNReal subtraction.

The sample space is nonempty even if I is empty: it contains the identity
permutation. Thus the ordinary existing normalized-uniform-universe
instance applies; no key needs to be manufactured.

## 3. Count-to-indicator proof and pinned APIs

For a fixed outside key `b ∉ S`, define E_b only within the proof as the
strict-before event. Its exact equivalence is

```lean
{π | ∀ a ∈ S, priority (π b) < priority (π a)} =
  PermutationMinimum.minimumEvent priority (insert b S) b
```

This is where injectivity matters. Forward, strict comparisons imply the
required non-strict comparisons, and b compares to itself by reflexivity.
Reverse, for `a ∈ S`, `a ≠ b`; injectivity of π and priority rules out equal
assigned priorities, so the minimum's non-strict comparison is strict.
For `b ∈ S` the strict-before predicate is false by its self-comparison.
An explicit-insert helper needs decidable equality on I in its statement;
it can stay private, with the public mean retaining no such instance.

Consequently the actual count satisfies the pointwise identity

`(beforeCount priority S π : ℝ≥0∞) = Σ b∈univ\S, E_b.indicator 1 π`.

The right side counts each outside label once. It does not assert that
the events are independent. Apply finite integral linearity, integrate
each indicator, and use the already existing XU01 theorem:

```lean
uniformOn_minimumEvent priority hinj (insert b S) b (Finset.mem_insert_self b S)
```

Every summand is `((S.card + 1 : ℕ) : ℝ≥0∞)⁻¹`, and there are exactly
`Nat.card I - S.card` outside labels. This proves the ENNReal formula
without a new symmetry, action, permutation-fiber, or order-statistic proof.

The following are exact pinned declarations, not new infrastructure:

- In [Data/Set/Card.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Card.lean):
  `Set.ncard_eq_toFinset_card (s) (hs : s.Finite := ...)`,
  `Set.ncard_coe_finset (s : Finset I)`,
  `Set.ncard_univ (I)`,
  `Set.ncard_le_ncard (hst : s ⊆ t) (ht : t.Finite := ...)`,
  `Set.ncard_compl (s) (hs : s.Finite := ...)`, and
  `Set.ncard_le_card [Finite I] (s)`.
- In `Mathlib.Data.Finset.Card`:
  `Finset.card_insert_of_notMem (h : b ∉ S)` gives
  `(insert b S).card = S.card + 1`, and
  `Finset.card_sdiff_of_subset (h : S ⊆ T)` gives
  `(T \ S).card = T.card - S.card`.
  In `Mathlib.Data.Fintype.Card`, `Finset.card_le_univ S`,
  `Finset.card_univ` and `Finset.card_univ_sdiff S` handle the local
  Fintype proof; `Nat.card_eq_fintype_card` removes its enumeration.
- `Finset.sum_indicator_eq_sum_filter` is the additive declaration generated
  from `prod_mulIndicator_eq_prod_filter` in
  [Group/Finset/Indicator.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/BigOperators/Group/Finset/Indicator.lean).
  Its additive shape is
  `∑ i∈s, (t i).indicator (f i) (g i) = ∑ i∈s with g i∈t i, f i (g i)`.
  This and `Finset.sum_const` identify an indicator sum with a filter's
  cast cardinal. Alternatively use `Finset.card_eq_sum_ones`, cast the
  natural sum, and rewrite the finite-set membership; no public counting
  adapter is needed.

The sharp deterministic bound needs only `[Preorder P]`: the strict-before
set is contained in `(S : Set I)ᶜ`. Apply `Set.ncard_le_ncard`, then
`Set.ncard_compl` and `Set.ncard_coe_finset`. Empty S reduces to the universal
set by vacuity and `Set.ncard_univ`. These proofs are separate from the
injectivity and uniform-law assumptions.

For integration use supported names from
[Integral/Lebesgue/Add.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean):

```lean
lintegral_finsetSum' (s : Finset β) {f : β → Ω → ℝ≥0∞}
    (hf : ∀ b ∈ s, AEMeasurable (f b) μ) :
    (∫⁻ ω, ∑ b ∈ s, f b ω ∂μ) = ∑ b ∈ s, ∫⁻ ω, f b ω ∂μ

lintegral_finsetSum (s : Finset β) {f : β → Ω → ℝ≥0∞}
    (hf : ∀ b ∈ s, Measurable (f b)) :
    (∫⁻ ω, ∑ b ∈ s, f b ω ∂μ) = ∑ b ∈ s, ∫⁻ ω, f b ω ∂μ
```

In `Integral/Lebesgue/Basic.lean`,
`lintegral_indicator_one (hE : MeasurableSet E)` concludes
`∫⁻ ω, E.indicator 1 ω ∂μ = μ E`.
Every event is finite, so `(Set.toFinite E).measurableSet` discharges its
measurability. More directly,
`measurable_of_finite [Finite Ω] [MeasurableSingletonClass Ω] (f : Ω → B)`
from `MeasurableSpace/Basic.lean` proves measurability of each required
observation. No priority-target measurable-space assumption is introduced.

## 4. Genuine integrability and ENNReal-to-real transport

The sample is finite and its uniform law is a probability measure.
`ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ`
in `Mathlib.Probability.UniformOn` requires `[Finite Ω] [Nonempty Ω]`
and supplies `IsProbabilityMeasure (uniformOn Set.univ)`; the surrounding
module supplies the sample measurable-space assumptions. Its derived finite
measure instance justifies the exact standard result

```lean
MeasureTheory.Integrable.of_finite
    [Finite Ω] [MeasurableSingletonClass Ω] [IsFiniteMeasure μ]
    {f : Ω → ℝ} : Integrable f μ
```

The underlying lemma is more general over a normed additive group; this is
the needed specialization from
[Function/L1Space/Integrable.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean).
Use it directly for the real count and ordinal observation, rather than
adding a generic finite-integrability wrapper. The deterministic complement
bound also independently explains why the real count has finite expectation.

The shortest transport in
[Integral/Bochner/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
is:

```lean
integral_toReal {f : Ω → ℝ≥0∞}
    (hfm : AEMeasurable f μ) (hf : ∀ᵐ ω ∂μ, f ω < ∞) :
    (∫ ω, (f ω).toReal ∂μ) = (∫⁻ ω, f ω ∂μ).toReal
```

Take `f π = (beforeCount priority S π : ℝ≥0∞)`. Its hypotheses follow
from finite-sample measurability and `ENNReal.natCast_lt_top`.
Rewrite the new ENNReal mean and simplify with
`ENNReal.toReal_natCast` and `ENNReal.toReal_div`.
`integral_toReal` itself does not assume global integrability and can
transport a totalized infinite integral to zero; the separate finite-sample
integrability and the finite ENNReal answer here are therefore substantive,
not optional mathematical qualifications.

An equally direct route explicitly consumes integrability in the proof:

```lean
ofReal_integral_eq_lintegral_ofReal {f : Ω → ℝ}
    (hfi : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ ω, f ω ∂μ) = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ
```

Use `hfi := Integrable.of_finite`, natural-cast nonnegativity,
`ENNReal.ofReal_natCast`, then apply `ENNReal.toReal` to the resulting
equality. `integral_nonneg` supplies the premise of
`ENNReal.toReal_ofReal`. This avoids even the appearance that a totalized
nonintegrable real integral supplies the claimed expectation. Either route
is sound; a second independent real indicator proof is unnecessary.

The denominator is a positive finite natural successor. The relevant
ENNReal APIs are `natCast_ne_top`, `natCast_lt_top`, and
`div_lt_top (hnum : x ≠ ∞) (hden : y ≠ 0)` in
`Mathlib.Basic.ENNReal.Inv`. Its `toReal_div (a b)` needs no extra
hypotheses, but that does not excuse omitting the finite-denominator
argument when interpreting the result as an expectation.

## 5. Actual ordinal bridge

Supply `rank : I ≃ Fin U`, not merely an injective numeric priority map.
For `hS : S.Nonempty`, set, within the theorem,

```lean
Rπ := S.image (fun a => rank (π a))
mπ := Rπ.min' (hS.image (fun a => rank (π a)))
```

The pointwise bridge should establish

```lean
beforeCount rank S π = mπ.val
```

and hence the requested one-based identity
`beforeCount rank S π + 1 = mπ.val + 1`.
The rank minimum is an actual `Fin U` obtained on the supplied nonempty
domain. It is never an arbitrary default or a numeric minimum of an
unrelated priority map.

Proof route:

1. `e := π.trans rank : I ≃ Fin U` satisfies `e b = rank (π b)`.
2. `Finset.lt_min'_iff Rπ hR` identifies `e b < mπ` with the strict
   comparisons to every element of Rπ. `Finset.mem_image` turns those
   into the defining comparisons against `a ∈ S`.
3. Thus the counted set is `e ⁻¹' Set.Iio mπ`. The existing
   `Set.ncard_preimage_of_injective_subset_range e.injective` applies;
   the range condition follows from `e.surjective`. Equivalently use
   `Set.ncard_image_of_injective` and the resulting image equality.
4. Rewrite `Set.Iio mπ` as the coercion of `Finset.Iio mπ`, use
   `Set.ncard_coe_finset`, then `Fin.card_Iio mπ`.

These are exact pinned APIs. `Finset.lt_min'_iff` is generated by the
`to_dual` attribute from `max'_lt_iff` in `Data/Finset/Max.lean`; its
statement is `x < s.min' H ↔ ∀ y ∈ s, x < y`.
The set preimage cardinal lemma in `Data/Set/Card.lean` is

```lean
Set.ncard_preimage_of_injective_subset_range
    {s : Set β} (H : Function.Injective f) (hs : s ⊆ Set.range f) :
    (f ⁻¹' s).ncard = s.ncard
```

`Fin.card_Iio (b : Fin U) : (Finset.Iio b).card = b.val` is in
[Order/Interval/Finset/Fin.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Interval/Finset/Fin.lean).
`Finite.of_injective rank rank.injective` in
`Mathlib.Data.Fintype.EquivFin` supplies local finiteness; the exact
`Nat.card_eq_of_equiv_fin rank : Nat.card I = U` is in
`Mathlib.SetTheory.Cardinal.Finite`.

The real ordinal theorem should display the actual integrand

```lean
fun π =>
  ((((S.image (fun a => rank (π a))).min'
      (hS.image (fun a => rank (π a)))).val + 1 : ℕ) : ℝ)
```

and conclude `(U + 1 : ℝ) / (S.card + 1 : ℝ)`.
Apply the pointwise bridge, real count mean, `integral_add`, and
`integral_const`; normalization makes the constant-one integral one.
The actual signatures are `integral_add hf hg` with both integrability
proofs, and `integral_const (c)` giving `μ.real Set.univ • c`.
Finally use `S.card ≤ U`, `Nat.cast_sub` and the positive denominator to
show `1 + (U - S.card)/(S.card + 1) = (U + 1)/(S.card + 1)` in ℝ.
No ENNReal subtraction is needed for this algebra.

## 6. Connected cases, imports and remaining boundaries

The existing calculation receipt already supplies useful connections:

| Fixed source case | Count mean | One-based ordinal mean | Purpose |
|---|---:|---:|---|
| `I = Empty`, `S = ∅` | 0 | Not defined by a nonempty minimum | Identity permutation still normalizes the sample. |
| `I = Fin 3`, `S = ∅` | 3 | Not a first position | Empty-S mean is valid without inventing a key. |
| `I = Fin 3`, `S = {0,1}` | 1/3 | 4/3 | Nonintegral count and actual rank bridge. |
| `I = Fin 4`, `S = {0,3}` | 2/3 | 5/3 | Count has values 0,1,2; exercises a nontrivial distribution. |
| `I = Fin 3`, `S = univ` | 0 | 1 | No outside labels. |

Connect selected cases through the new general theorems, not by recomputing
their averages independently. The saved `100 + 10 * rank` boundary has
expected raw minimum `310/3`, while the same order's first-position mean is
`4/3`. This distinguishes the numeric-value and ordinal observations.
For another direct mathematical boundary, tied constant priorities on two
indices with singleton S give count zero in every sample, whereas the
injective-priority formula would give `1/2`; injectivity cannot be dropped.
This observation requires no new enumeration.

A focused module can import the existing `PermutationMinimum` plus
`Mathlib.Algebra.BigOperators.Group.Finset.Indicator`,
`Mathlib.MeasureTheory.Integral.Lebesgue.Add`,
`Mathlib.MeasureTheory.Integral.Bochner.Basic`, and
`Mathlib.Order.Interval.Finset.Fin`.
The count/card, finite-permutation and uniform-measure imports already come
from XU01; supported `Mathlib.Basic.ENNReal.Inv` supplies the explicit
reciprocal/real-transport lemmas if not already transitively available.
Do not import a blanket `Mathlib` or create duplicate expectation lemmas.

There is no identified mathematical or API-level blocker. The missing work
is the small count/indicator equivalence, its finite sum proof, the justified
real transport, and the actual rank-minimum bridge. Routine elaboration
risks are set/finset coercions, generated dual/additive theorem arguments,
natural-subtraction casts, and local finite instances; no compiler has
tested proposed proof terms or imports.

These laws concern one fixed subset under one uniform global ranking.
They provide a real expectation suitable for a later treap client, but do
not prove conditional/adaptive subset statements, conditional Jensen
premises, random-input/algorithm correspondences, independence, or an
exchange of correlated depth and charging factors. Those source obligations,
including the Chapter 10 charging bridge, remain separate and queued.

## 7. Relative-order HasLaw does not determine global placement

Root proposed, and the source contributor independently checked, one small
cross-unit boundary. It is suitable as a connected example; it does not
require a generic conditional-mean theorem or any additional core API.

Take `I = Fin 3`, `rank = Equiv.refl (Fin 3)`, complete positions `[0,1,2]`,
and the target count subset `S = {1}`. Let O be the actual full-universe
`restrictedOrder positions Finset.univ`, E be `firstEvent O 0`, and
`ν = μ₀[|E]`. Under ν, the two actual global orders are `[0,1,2]` and
`[0,2,1]`, each of mass `1/2`. Thus the actual preceding counts for S are
1 and 2, giving mean `3/2`. The new unconditional count theorem gives mean
1 under μ₀. Under **both** measures, the S-relative-order observation is
identically `[1]` and has the same uniform singleton-order law.

This shows precisely why a premise
`HasLaw (restrictedOrder positions S) (uniformOn (orders positions S)) ν`
cannot replace the global-uniform premise of the count theorem. Unlike the
tail/filter observations, `beforeCount` depends on positions occupied by
outside labels and does not factor through the relative order of S.

A compact formal connection uses only the actual current APIs:

1. `PermutationTail.uniformOn_firstEvent` with full S=`univ`, a=0 gives
   `μ₀ E = 1/3`. Install the standard
   `cond_isProbabilityMeasure [IsFiniteMeasure μ₀] (h : μ₀ E ≠ 0)` for ν.
2. Let `F = {π | (O π).tail = [2,1]}`. XU03's
   `cond_tail_eq positions hnd hcomplete Finset.univ 0 ha [2,1]`
   gives `ν F = 1/2` through the actual source fiber.
3. On E, prove the concrete value identity
   `(beforeCount rank {1} π : ℝ) = 1 + F.indicator 1 π`.
   The new `beforeCount_rank_eq` reduces the count to `(π 1).val`;
   the finite global-order/head constraints determine whether that rank is
   1 or 2. The identity is required only on E, not outside it.
4. `ae_cond_of_forall_mem hE` transports that pointwise identity to ν-a.e.
   equality. Use `integral_congr_ae`, `integral_add`, `integral_const` and
   `integral_indicator_one hF` to obtain
   `1 + ν.real F = 1 + 1/2 = 3/2`. Each real integrand is integrable by
   `Integrable.of_finite`; ν has already been proved a probability measure.
5. For the same S-observation's unchanged law, use
   `map_restrictedOrder_cond_first positions hnd hcomplete Finset.univ 0 ha
     {1} hT` under ν, and XU02's `map_restrictedOrder_uniformOn` under μ₀.
   Pair each map equality with finite-sample measurability to form the
   existing `HasLaw`. This exercises the conditioning interfaces rather
   than defining a fresh independent ranking experiment.

The exact integration declarations are
`integral_congr_ae (h : f =ᵐ[ν] g)` in `Integral/Bochner/Basic.lean` and
`integral_indicator_one (hF : MeasurableSet F) :
  (∫ π, F.indicator 1 π ∂ν) = ν.real F`
in `Integral/Bochner/Set.lean`. `Measure.real` is the ENNReal measure's
`toReal`, so the already proved finite mass `1/2` transports directly.
No generic law-of-expectation framework is needed. `HasLaw.integral_comp`
and `integral_fintype` also exist, but do not shorten this two-value event
proof enough to justify more machinery.

Only this example needs imports of XU03 and `Integral/Bochner/Set`;
the proposed shared core continues to depend on XU01 and ordinary
integration/cardinality APIs. This additional boundary was checked by
mathematical case analysis, with no new enumeration or compiler run.

## 8. Proposed names and argument order for later coordination

These are recommendations, not frozen requirements or implemented APIs.
The suggested namespace is `Applications.Probability.PermutationExpectation`.
Keep I, P, universes, instances and U inferred where their argument types
already determine them.

```text
beforeCount priority S π
beforeCount_empty priority π
beforeCount_le priority S π
lintegral_beforeCount_uniformOn priority hinj S
integral_beforeCount_uniformOn priority hinj S
beforeCount_rank_eq rank S hS π
integral_firstPosition_uniformOn rank S hS
```

`beforeCount_rank_eq` states the zero-based equality in section 5; applying
`congrArg (fun n : ℕ => n + 1)` gives the exact one-based identity, so a
second alias is unnecessary. `integral_firstPosition_uniformOn` displays
the actual nonempty finite-image minimum plus one as its integrand. The
strict-before/inserted-minimum equivalence and indicator-sum mechanics can
remain private. Ordinary `Integrable.of_finite` supplies the integrability
contracts without a redundant public wrapper.
