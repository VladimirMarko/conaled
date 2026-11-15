# Conditional remaining order: API and design preflight

Recorded 2026-11-02. This is bounded read-only preparation in the continuing
FDSA workflow. No new unit scope is frozen, and this note supplies no
implementation, compiler validation, review acceptance, or chapter credit.
Only this note was written. No compiler, project hash helper, Git, cache,
gate, repository source, tracker, or requirements were changed.

The inspected whole-order draft is the root-reported committed candidate
`4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`, being preserved in checkpoint
0018. Its source and dependencies remain unaccepted. Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`; saved Lean list sources are from
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (Lean 4.35.0).

This note follows [permutation-order-api-preflight.md](permutation-order-api-preflight.md)
and coordinates with the source contributor's
[permutation-tail-source-preflight.md](permutation-tail-source-preflight.md).
The completed source note has SHA-256
`b81176f85c477674aa73133f567d655038f6d09324adfddb614364dcbd17646e`
(including its independently assessed observed-law transport addendum).
The root's independently enumerated examples are in
[permutation-tail-calculations.json](permutation-tail-calculations.json),
SHA-256 `b614ea7eb98b3aaba5c15006a967e1d8da51fc373d5b963c99cdccce6b4632eb`.
They are mathematical preparation, not checked Lean specializations.

## 1. Recommendation

Use ordinary event conditioning and the existing whole-order fiber law.
The smallest new combinatorial fact is the correspondence between a
supported order beginning with `a` and a supported order of `S.erase a`.
No new ranking carrier, sampling executor, conditional-probability record,
group action, or general finite-uniform framework is needed.

Let the following be ordinary abbreviations in this discussion:

```lean
O S := restrictedOrder positions S
mu := uniformOn (Set.univ : Set (Equiv.Perm I))
E := {pi | (O S pi).head? = some a}
R := S.erase a
tailObs := fun pi => (O S pi).tail
```

The pinned conditional-measure API is **`ProbabilityTheory.cond`**, with
notation `mu[|E]`; it is not named `Measure.cond`. It conditions the
original global permutation law. For `a ∈ S`, the proposed results are:

1. `mu E = (S.card : ℝ≥0∞)⁻¹`, hence positive and finite.
2. `mu[|E] = uniformOn E` as measures on the original permutation space.
3. Under this conditional measure, the actual observation `tailObs` is
   uniform on `orders positions R`; expose both its universal fiber
   formula and its `Measure.map` equality.
4. On E, `tailObs pi = restrictedOrder positions R pi`.
5. For any fixed `T ⊆ R`, the original observation
   `restrictedOrder positions T` also has the existing uniform order law
   under `mu[|E]`.

Item 5 fits the same small unit as a composition corollary. It requires no
new counting argument or partial-enumeration theorem. It would be useful
immediately for the separate conditional branch-order obligations in
quicksort and selection. It does not discharge their algorithm/history
correspondence or work analysis.

For recursive reuse, the public conditional tail law can also take the
existing `HasLaw Y (uniformOn (orders positions S)) mu` for an ordinary
observation `Y : Omega → List I`. Section 6 gives a small transport proof
using existing APIs. This is a useful generalization within the same
mathematics: the full environment may already be conditioned and
nonuniform, while its current order observation has the required law.
Retain the actual global permutation specialization and its
`mu[|E] = uniformOn E` identity; that particular identity does not
generalize to an arbitrary environment law.

## 2. Exact existing project interfaces and minimal assumptions

All relevant project declarations are in namespace
`Applications.Probability.PermutationOrder`:

| Existing declaration | Direct use |
|---|---|
| `restrictedOrder positions S pi` | Actual inverse-permutation/filter observation; retain its direction. |
| `orders positions S` | Existing finite set of permutations of the filtered base list. |
| `mem_restrictedOrder positions S pi x` | General membership, without completeness; an observed head belongs to S. |
| `restrictedOrder_nodup positions hnd S pi` | The observed first key does not recur in the tail. |
| `mem_restrictedOrder_of_complete positions hcomplete S pi x` | Complete support for the cons/tail correspondence. |
| `restrictedOrder_perm positions hnd hcomplete S pi` | Supported whole outputs. |
| `mem_orders positions S xs` | Membership is precisely permutation of the filtered base. |
| `orders_nonempty positions S` | Remaining-order support includes the sole empty list when R is empty. |
| `orders_card positions hnd hcomplete S` | Cardinality is `Nat.factorial S.card`. |
| `uniformOn_restrictedOrder_eq positions hnd hcomplete S xs` | Probability of the full list `a :: xs`, including off-support zero. |
| `map_restrictedOrder_uniformOn positions hnd hcomplete S` | Equality of the actual global observation law and finite uniform list law. |
| `filter_restrictedOrder_of_subset positions S T pi hTS` | Composition using the same permutation; no completeness or probability premise. |

Keep `[DecidableEq I]` for the existing computations. Use one generic
ordinary event `firstEvent (Y : Omega → List I) a :=
{omega | (Y omega).head? = some a}`. This definition itself does not even
need decidable equality, and needs no completeness, Nodup, order,
inhabitedness, or measurable structure. Its actual-global specialization
is `firstEvent (restrictedOrder positions S) a`; a second event alias
would be redundant.
`List.tail` is already total, and `List.head?` keeps absence explicit.
A second tail operation or a separate global-law definition is unnecessary.

The probability statements inherit exactly the sample assumptions of the
whole-order law:

```lean
[MeasurableSpace (Equiv.Perm I)]
[MeasurableSingletonClass (Equiv.Perm I)]
(positions : List I) (hnd : positions.Nodup)
(hcomplete : ∀ x, x ∈ positions)
(S : Finset I) (a : I) (ha : a ∈ S)
```

Completeness supplies `Fintype.ofList positions hcomplete` locally, then
finiteness of `Equiv.Perm I`. The latter is nonempty even if I is empty.
Do not add a public finite enumeration, `Nonempty I`, index order, or a
measurable space on I. The member-specific positive theorem simply cannot
be instantiated with an element of an empty S.

Neither the head probability nor the conditional tail **source-fiber**
formula needs measurable structure on `List I` or `Option I`. The finite
permutation events are measurable from sample measurable singletons.
The map equalities additionally require the caller's existing
`[MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]`.
Finite I makes `List I` countable, not finite.

The on-E deterministic tail identity needs only `positions.Nodup` and
the particular head equality. Completeness is unnecessary there: every
retained key already belongs to S, and Nodup prevents another a in its
tail. The conditioning-to-`uniformOn E` identity needs only the complete
finite sample and event measurability; it does not require Nodup or ha.

## 3. Smallest direct proof route

### Deterministic cons and tail bridges

For every ordinary list l, without a nonempty or Nodup assumption,

```lean
l.head? = some a ∧ l.tail = xs ↔ l = a :: xs
```

follows by list cases, or from `List.head?_eq_some_iff` and `List.tail_cons`.
Consequently the event identity

```lean
E ∩ {pi | tailObs pi = xs} = {pi | O S pi = a :: xs}
```

is pointwise and needs no distribution assumptions. This identity is the
main reason to prefer the prefix/fiber proof over another symmetry proof.

Under hnd, hcomplete, and ha, establish

```lean
(a :: xs) ∈ orders positions S ↔ xs ∈ orders positions (S.erase a)
```

using `mem_orders`, `List.perm_ext_iff_of_nodup`, permutation membership
transport, `List.nodup_cons`, and `Finset.mem_erase`. In the forward
direction, Nodup excludes a from xs; membership of `a :: xs` is exactly S.
In the reverse direction, xs has exactly erase support, so prefixing a
restores a Nodup list with exactly support S. This route avoids dependence
on a new list-erasure implementation or a subtype permutation.

For a public deterministic helper, full completeness is stronger than
necessary: hnd, `a ∈ positions`, and ha already suffice for this cons
equivalence, by comparing actual filtered memberships. The probability
client obtains `a ∈ positions` from hcomplete. Alternatively a universal
cons-support equivalence can include both memberships on its right-hand
side. This is a routine hypothesis refinement, not a reason to introduce
another list representation or a more elaborate occurrence-count API.

To prove the on-E identity, write `O S pi = a :: xs`. Filter this list to
`S.erase a`. Its head is dropped and all tail entries survive because they
belong to S and differ from a. `List.filter_eq_self` and the existing
nested-filter theorem identify the result with `O (S.erase a) pi`.
This equality must remain conditional on E; it is generally false on
the rest of the sample space.

### Head mass and normalization

Let `B := orders positions (S.erase a)`, `m := S.card`, and
`n := (S.erase a).card`. The event E is the disjoint finite union, over
`xs ∈ B`, of `{pi | O S pi = a :: xs}`. Each member has mass
`(Nat.factorial m : ℝ≥0∞)⁻¹` by the existing whole-order theorem.
`measure_biUnion_finset` sums these fibers; alternatively use
`sum_measure_preimage_singleton` on the finset of prefixed lists.

Existing `orders_card`, `Finset.card_erase_add_one ha`, and
`Nat.factorial_succ` yield

\[
\mu(E)=n!\,(m!)^{-1}=(m)^{-1},\qquad n+1=m.
\]

All arithmetic is in ENNReal after natural-number casts, not natural
division. `Finset.card_ne_zero_of_mem ha` and `Nat.factorial_ne_zero`
supply nonzero denominators; `ENNReal.natCast_ne_top` supplies finiteness.
Use explicit `ENNReal.mul_inv`/cancellation premises. The n=0 case is
already covered by `0! = 1`; no extra positive-tail-size premise belongs
in the theorem.

Unfolding `uniformOn` gives `Measure.count[|Set.univ]`. Applying the
existing `cond_cond_eq_cond_inter` to count, univ, and E gives

```lean
(uniformOn Set.univ)[|E] = uniformOn E
```

because the counting measure on the finite permutation space has its
existing `IsFiniteMeasure` instance. This equality holds for null E too;
there is no need for a new public generic conditioning wrapper.

Now `cond_apply` and the joint-fiber identity give the universal formula

```lean
(mu[|E]) {pi | tailObs pi = xs} =
  if xs ∈ orders positions (S.erase a)
  then (Nat.factorial (S.erase a).card : ℝ≥0∞)⁻¹
  else 0
```

for ha. The supported branch reduces to
`m * (m * n!)⁻¹ = (n!)⁻¹`; the unsupported branch is zero. Keep the
source event on the left, rather than defining an independent uniform
tail draw and describing it as conditional.

Finally use `Measure.ext_of_singleton`, `Measure.map_apply`, and
`uniformOn_apply_finset` exactly as in the whole-order module to obtain

```lean
(mu[|E]).map tailObs =
  uniformOn (orders positions (S.erase a) : Set (List I))
```

An `IsProbabilityMeasure (mu[|E])` witness follows from
`cond_isProbabilityMeasure` and the proved positive head mass. Do not
install an overlapping global instance on event parameters or samples.

### Why event-preserving relabeling is larger here

An alternative is mathematically sound: extend the positional
correspondence between `a :: xs` and `a :: ys` to a global permutation
sigma. Matching the first entries forces `sigma a = a`; common support
forces preservation of S. Then `pi ↦ pi * sigma.symm` preserves E and
transports tail fibers. Normalize their equal conditional masses.

The earlier whole-order extension/equivariance helpers are private. This
alternative would repeat machinery or motivate changing its visibility,
while still needing head mass or a separate normalizing argument. The
already-public full fiber theorem makes that unnecessary. Do not expose
a general stabilizer/action interface merely to use this alternate proof.

## 4. Fixed remaining-subset restriction fits by composition

Let `nu := mu[|E]`, `R := S.erase a`, and fix `T ⊆ R`. Let
`f := restrictedOrder positions R` and
`g := fun xs => xs.filter (fun x => decide (x ∈ T))`.

The on-E tail identity and `ae_cond_of_forall_mem` give equality of the
two maps under nu using `Measure.map_congr`. The tail theorem and the
existing unconditional whole-order theorem therefore give

\[
\nu\mathbin{.\mathrm{map}}f
=\operatorname{uniformOn}(\mathrm{orders}\;\mathrm{positions}\;R)
=\mu\mathbin{.\mathrm{map}}f.
\]

Map this equality through g. `Measure.map_map` and the current
`filter_restrictedOrder_of_subset positions R T pi hT` identify both
composites with `restrictedOrder positions T`. Applying the existing
unconditional map law for T finishes

```lean
(mu[|E]).map (restrictedOrder positions T) =
  uniformOn (orders positions T : Set (List I))
```

Every application of the whole-order theorem uses the original complete
positions list. No tail is passed as a purported enumeration of I.
`measurable_of_countable g` is available after the local enumeration of
I and standard `List.countable`; `measurable_of_finite f` handles the
sample observation. No list topology or index measurable instance is
needed. A separate public uniform-filter theorem is optional reuse,
not a prerequisite of this corollary.

T may be a specified function of the already fixed revealed key a, such
as a source branch's set of occurrence indices. For each a, it remains
fixed outside the permutation sample. This is not a theorem for a subset
adaptively chosen from further hidden comparisons or an arbitrary prior
history. It establishes individual conditional marginals, with no
disjoint-branch independence claim.

## 5. Exact pinned measure and list APIs

The signatures below were inspected in the pinned source. Implicit
measurable-space parameters and ordinary ambient type variables are
omitted from this display where they are not the relevant requirement.

```lean
-- Mathlib.Probability.ConditionalProbability
ProbabilityTheory.cond (mu : Measure Omega) (s : Set Omega) : Measure Omega
-- Definition: (mu s)⁻¹ • mu.restrict s

cond_apply (hms : MeasurableSet s) (mu : Measure Omega) (t : Set Omega) :
  mu[t | s] = (mu s)⁻¹ * mu (s ∩ t)

cond_cond_eq_cond_inter (hms : MeasurableSet s) (hmt : MeasurableSet t)
    (mu : Measure Omega) [IsFiniteMeasure mu] :
  mu[|s][|t] = mu[|s ∩ t]

cond_isProbabilityMeasure [IsFiniteMeasure mu] (hcs : mu s ≠ 0) :
  IsProbabilityMeasure mu[|s]

ae_cond_of_forall_mem (hs : MeasurableSet s) {p : Omega → Prop}
    (h : ∀ x ∈ s, p x) : ∀ᵐ x ∂mu[|s], p x

cond_empty (mu : Measure Omega) : mu[|∅] = 0
cond_eq_zero_of_meas_eq_zero (h : mu s = 0) : mu[|s] = 0
cond_eq_zero : mu[|s] = 0 ↔ mu s = ∞ ∨ mu s = 0

-- Mathlib.MeasureTheory.Measure.Basic
measure_biUnion_finset {s : Finset J} {f : J → Set Omega}
    (hd : Set.PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) :
  mu (⋃ b ∈ s, f b) = ∑ b ∈ s, mu (f b)

sum_measure_preimage_singleton (s : Finset B) {f : Omega → B}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) :
  (∑ b ∈ s, mu (f ⁻¹' {b})) = mu (f ⁻¹' ↑s)

-- Mathlib.MeasureTheory.Measure.Map
Measure.map_apply (hf : Measurable f) (hs : MeasurableSet s) :
  mu.map f s = mu (f ⁻¹' s)

Measure.map_map (hg : Measurable g) (hf : Measurable f) :
  (mu.map f).map g = mu.map (g ∘ f)

Measure.map_congr (h : f =ᵐ[mu] g) : mu.map f = mu.map g

-- Mathlib.MeasureTheory.Measure.Dirac.Basic
Measure.ext_of_singleton [Countable B] {mu nu : Measure B}
    (h : ∀ x, mu {x} = nu {x}) : mu = nu

-- Mathlib.MeasureTheory.MeasurableSpace.Basic
measurable_of_finite [Finite A] [MeasurableSingletonClass A] (f : A → B) :
  Measurable f
measurable_of_countable [Countable A] [MeasurableSingletonClass A] (f : A → B) :
  Measurable f
```

`Measure.count.isFiniteMeasure [Finite Omega]` is in
`Mathlib.MeasureTheory.Measure.Count`. `uniformOn := Measure.count[|s]`,
`uniformOn_empty_meas`, `uniformOn_apply_finset`, and
`instIsProbabilityMeasure_uniformOn_univ [Finite Omega] [Nonempty Omega]`
are in `Mathlib.Probability.UniformOn`.

For an alternate map-first proof, existing
`Measure.restrict_map (hf : Measurable f) (hs : MeasurableSet s)` gives
`(mu.map f).restrict s = (mu.restrict (f ⁻¹' s)).map f`.
`Measure.map_smul c hf` takes an `AEMeasurable f mu` witness. These suffice
to derive conditioning/pushforward compatibility locally; no existing
direct `map_cond` theorem was found in the inspected conditional/map
modules, and the recommended fiber proof does not need one.

The elementary list APIs are `List.head?_eq_some_iff`,
`List.mem_of_head?`, `List.cons_head?_tail`, `List.tail_cons`,
`List.nodup_cons`, `List.Nodup.notMem`, `List.filter_eq_self`, and
`List.perm_ext_iff_of_nodup`. The source `head?` and filter statements were
checked in the pinned saved `Init/Data/List/Lemmas.lean`; the Mathlib
`List.Basic` and `List.Nodup` modules supply the additional contracts.

`Finset.card_erase_add_one ha`, `Finset.card_ne_zero_of_mem ha`,
`Nat.factorial_succ n`, and `Nat.factorial_ne_zero n` suffice for the
factorial arithmetic. For ENNReal cancellation, use the supported
`Mathlib.Basic.ENNReal.Inv` APIs:

```lean
ENNReal.mul_inv (ha : x ≠ 0 ∨ y ≠ ∞) (hb : x ≠ ∞ ∨ y ≠ 0) :
  (x * y)⁻¹ = x⁻¹ * y⁻¹
ENNReal.mul_inv_cancel (h0 : x ≠ 0) (ht : x ≠ ∞) : x * x⁻¹ = 1
ENNReal.inv_mul_cancel (h0 : x ≠ 0) (ht : x ≠ ∞) : x⁻¹ * x = 1
ENNReal.inv_pos : 0 < x⁻¹ ↔ x ≠ ∞
ENNReal.natCast_ne_top (n : Nat) : (n : ℝ≥0∞) ≠ ∞
```

Primary pinned sources: [ConditionalProbability](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/ConditionalProbability.lean),
[UniformOn](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/UniformOn.lean),
[Measure/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Basic.lean),
[Measure/Map](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Map.lean),
[Measure/Restrict](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Restrict.lean),
[Finset/Card](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Finset/Card.lean),
[Nat/Factorial/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/Factorial/Basic.lean),
and [ENNReal/Inv](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Basic/ENNReal/Inv.lean).

## 6. Observation-law transport for a changing environment

The existing `ProbabilityTheory.HasLaw` in
`Mathlib.Probability.HasLaw` is exactly the appropriate law interface:

```lean
structure HasLaw (Y : Omega → B) (nu : Measure B) (mu : Measure Omega) : Prop where
  protected aemeasurable : AEMeasurable Y mu
  protected map_eq : mu.map Y = nu
```

This display suppresses its existing default measure argument and default
proof tactic. Its standard `HasLaw.comp` composes observed laws;
`HasLaw.measure_eq` transports measurable event masses, and
`HasLaw.isProbabilityMeasure` transfers normalization from the output law
to the source. No new law record is necessary. An equivalent public pair
`AEMeasurable Y mu` and `mu.map Y = nu` avoids the `HasLaw` import if that
dependency is undesirable, without changing the mathematical content.

There is a short conditional-map identity for any AEMeasurable Y and
measurable output event H:

```lean
(mu[|Y ⁻¹' H]).map Y = (mu.map Y)[|H]
```

It requires neither a finite source space nor a positive-event premise.
Unfold `ProbabilityTheory.cond`, then use these exact existing APIs:

```lean
Measure.restrict_map_of_aemeasurable
    (hY : AEMeasurable Y mu) (hH : MeasurableSet H) :
  (mu.map Y).restrict H = (mu.restrict (Y ⁻¹' H)).map Y

Measure.map_smul c hY.restrict
Measure.map_apply_of_aemeasurable hY hH
```

The first declaration is in
`Mathlib.MeasureTheory.Measure.AEMeasurable`, not the ordinary `Restrict`
file. `AEMeasurable.restrict` supplies the map-scaling hypothesis.
Moreover `hY.mono_ac cond_absolutelyContinuous` gives AEMeasurability of
Y under the conditioned source. Thus the same calculation yields

```lean
HasLaw Y nu mu →
  HasLaw Y (nu[|H]) (mu[|Y ⁻¹' H])
```

when H is measurable. This uses only existing fields and elementary
measure transport; a private helper suffices unless a separate client
justifies a public generic lemma. No regular conditional kernel is
required. Null events remain zero in this identity.

The relevant exact ambient contracts are:

```lean
AEMeasurable.restrict (hY : AEMeasurable Y mu) {s} :
  AEMeasurable Y (mu.restrict s)
AEMeasurable.mono_ac (hY : AEMeasurable Y mu) (hnu : nu ≪ mu) :
  AEMeasurable Y nu
ProbabilityTheory.cond_absolutelyContinuous : mu[|s] ≪ mu

Measure.map_smul (c : R) (hY : AEMeasurable Y mu) :
  (c • mu).map Y = c • mu.map Y
-- Ambient: [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞].
-- Here R = ℝ≥0∞ and hY is supplied for mu.restrict (Y ⁻¹' H).

Measure.map_apply_of_aemeasurable (hY : AEMeasurable Y mu)
    (hH : MeasurableSet H) : mu.map Y H = mu (Y ⁻¹' H)

HasLaw.comp (hZ : HasLaw Z rho nu) (hY : HasLaw Y nu mu) :
  HasLaw (Z ∘ Y) rho mu
HasLaw.fun_comp (hZ : HasLaw Z rho nu) (hY : HasLaw Y nu mu) :
  HasLaw (fun omega => Z (Y omega)) rho mu
HasLaw.isProbabilityMeasure [IsProbabilityMeasure nu]
    (hY : HasLaw Y nu mu) : IsProbabilityMeasure mu
```

For this task, choose `H := {xs : List I | xs.head? = some a}`.
The local finite enumeration of I, `List.countable`, and measurable list
singletons make H and `List.tail` measurable. No measurable space on
`Option I` is necessary to express this particular set. The desired
general statement can therefore have the following shape, with the same
positions/hnd/hcomplete/S/a/ha as above:

```lean
-- Proposed interface, not an implemented or elaborated declaration.
theorem hasLaw_tail_cond_first
    {Omega : Type*} [MeasurableSpace Omega]
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ x, x ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S)
    {mu : Measure Omega} {Y : Omega → List I}
    (hY : HasLaw Y (uniformOn (orders positions S : Set (List I))) mu) :
    HasLaw (fun omega => (Y omega).tail)
      (uniformOn (orders positions (S.erase a) : Set (List I)))
      (mu[|{omega | (Y omega).head? = some a}])
```

There is no finiteness, measurable-singleton, or uniformity hypothesis on
Omega or mu. The output uniform measure is a probability measure because
its finite support is nonempty; `hY.isProbabilityMeasure` can supply a
source normalization instance when needed. The positive head mass follows
from `hY.measure_eq` and the same canonical output-event count.

Recommended common argument orders for coordinated clients are:

| Proposed name | Explicit call arguments | Conclusion |
|---|---|---|
| `head_mass_of_hasLaw` | `positions hnd hcomplete S a ha hY` | `mu (firstEvent Y a) = (S.card : ℝ≥0∞)⁻¹`. |
| `hasLaw_tail_cond_first` | `positions hnd hcomplete S a ha hY` | The displayed conditional HasLaw for the actual tail. |
| `hasLaw_filter_tail_cond_first` | `positions hnd hcomplete S a ha hY T hT` | The displayed remaining-filter HasLaw below, with `hT : T ⊆ S.erase a`. |

Omega, mu, and Y should be implicit and inferred from hY; the source
measurable instance and output-list measurable/singleton instances remain
ordinary typeclass parameters. These names and orders are proposals for
the later freeze, not new declarations. A source-event specialization can
choose a local discrete list measurable instance in its proof, so it need
not expose output measurability merely to state a scalar probability.

One feasible proof order preserves all existing work. First prove the
global-permutation conditional tail theorem by Section 3. Apply the
conditional-map identity to `O S` and the existing XU02 pushforward law.
Compose with `List.tail` to obtain the canonical theorem for
`(uniformOn (orders positions S))[|H]`. For an arbitrary hY, transport Y
through H as above and apply existing `HasLaw.comp` with that canonical
tail law. This adds equational transport, not another permutation/counting
proof. Conversely the same interface can be implemented with the
canonical finite-list proof first and the global experiment as its
checked specialization. Both orders leave the actual experiment explicit.
When a proof uses the canonical global experiment internally, local
discrete instances on its permutation sample suffice; no new global
measurable instance or public source-space parameter is introduced.

For filtering the remaining observed list, obtain the ordinary canonical
law

```lean
HasLaw (fun xs : List I => xs.filter (fun x => decide (x ∈ T)))
  (uniformOn (orders positions T : Set (List I)))
  (uniformOn (orders positions (S.erase a) : Set (List I)))
```

from XU02's map equalities and nested-filter law as in Section 4. It needs
`T ⊆ S.erase a`; all occurrences of positions retain their original
completeness. The function's measurability is `measurable_of_countable`.
The generic tail theorem then composes through it by `HasLaw.fun_comp`,
giving the precise recursive observation contract

```lean
HasLaw (fun omega => (Y omega).tail.filter (fun x => decide (x ∈ T)))
  (uniformOn (orders positions T : Set (List I)))
  (mu[|{omega | (Y omega).head? = some a}])
```

No new conditional theorem or framework is required to express this
composition. The canonical filter law can be a private helper initially;
expose an ordinary filtering corollary if the eventual client benefits.
Under the same conditioned measure, filtering Y directly has the same
law because the removed head a is not in T. In the actual global
specialization, the observed remaining filter equals
`restrictedOrder positions T` on E by XU02's nested-filter theorem and
the tail/erase bridge. This is suitable for a later induction invariant
on the observed current order, without claiming that previously
conditioned global priorities are again uniformly distributed.

An hY law gives support and Nodup **almost everywhere**, not necessarily
at every omega. Thus an outsider first event can be a nonempty null set
for an arbitrary Y; the consequence is zero measure and zero conditioning,
not pointwise emptiness. The literal empty-event and on-event pointwise
claims in Sections 2–3 belong to the actual restrictedOrder specialization.
The transport proof respects this distinction and works already with
AEMeasurability, without requiring an unnecessary globally measurable Y.

For later histories, note the precise remaining boundary:
`cond_cond_eq_cond_inter` requires measurable conditioning events. An
arbitrary AEMeasurable Y supplies a null-measurable head preimage, so one
must prove the relevant event measurability or use appropriate a.e.
transport before invoking that particular intersection identity. The
one-step HasLaw transport above already handles AEMeasurability and does
not depend on that identity. Successive applications can retain the nested
conditioned measures explicitly. Finite concrete permutation examples
have measurable events automatically.

This layer is small enough to recommend for the first unit. The root's
concrete proposed use starts with Fin 4 and S=`{0,2,3}`, conditions on
first0, and calls this changed measure nu. Its actual tail Y has the
uniform-order HasLaw for `{2,3}`. Apply the generic head theorem to obtain
`nu (firstEvent Y 2) = 1/2`, then the generic tail theorem at that same
HasLaw to obtain the sole remaining list `[3]` after the second
conditioning. The original complete positions are reused throughout.
Separately `nu (firstEvent (O S) 0) = 1` while
`mu (firstEvent (O S) 0) = 1/3`, proving that the full environment really
changed. This tests the observed-law interface directly; it does not
prove arbitrary recursive histories or an algorithm/global-ranking
coupling.

For public-surface discipline, retain this one generic conditional-tail
HasLaw, its head-mass result and useful filter corollary, plus actual
global specializations with their weaker source-event assumptions and
pointwise observation bridges. The actual global conditional-measure
identity and the source-fiber/map statements express distinct useful
contracts. Extra aliases for both `uniformOn E` and `mu[|E]` forms of
every result would only repeat interfaces; callers can rewrite using the
single conditional-measure identity. No specialized conditional executor
or new law structure is justified.

Primary pinned sources: [HasLaw](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/HasLaw.lean)
and [Measure/AEMeasurable](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/AEMeasurable.lean).

## 7. Existing kernels do not require an extension

`Applications.Probability.Table.comp`, `Table.deterministic`,
`Table.kernel`, `Table.kernel_comp`, and `Table.steps` already provide
finite exact execution and interpretation into ordinary Mathlib kernels.
This task is a law about conditioning one existing experiment, so it does
not need another table operation or an executor. `List I` is countable,
and introducing a finite support subtype solely to fit a new Table would
add interface work without proving more.

Mathlib already has `ProbabilityTheory.condDistrib Y X mu : Kernel B C`
and `condDistrib_apply_of_ne_zero`. Its ambient assumptions include a
standard Borel, nonempty output space; the pointwise formula requires
measurable X and Y, measurable conditioning singletons, and positive
mass of the given conditioning fiber. It returns a Markov kernel whose
null-fiber version is not determined by the original experiment. Ordinary
`cond` instead returns zero on a null event. These distinctions make
`condDistrib` unnecessary for this first finite positive-event law.
Later kernel clients can prove the relevant connection through existing
APIs without changing this observation or its probability statements.

## 8. Consequential cases, remaining work, and placement

The saved Fin 4 calculation uses positions `[0,1,2,3]`, S=`{0,2,3}`,
and a=0. E contains 8 of 24 global permutations. The two tails `[2,3]`
and `[3,2]` each have joint mass 1/6 and conditional mass 1/2. The global
order `[1,0,2,3]` is in E even though its global first key is 1. Thus this
is conditioning on the first key *within S*, not on the first global key
or on a particular numeric rank. This case should exercise the generic
head mass, conditional measure identity, conditional fiber, and map law.

The same data supports fixed remaining-subset specializations. A larger
full S can additionally give a proper two-element T inside a
three-element remainder, if a nontrivial proper restriction is desired;
that is an example choice, not a new mathematical requirement.

The saved singleton S=`{2}`, a=2 case has E=univ and tail `[]` with
probability one. By contrast, empty S or an outsider a has E=empty:
`mu[|E]=0` and every mapped observation has zero measure. Meanwhile
`orders positions (S.erase a)` is still nonempty and its uniform law is
a probability measure. Consequently ha cannot be silently removed from
the uniform conditional-tail conclusion. An empty ambient index type
still has a normalized global permutation law and `head? = none`; it
does not provide a candidate a for the positive member theorem.

Containment is also substantive. The saved Fin 3 counterexample conditions
on 0 first in S=`{0,1}` and observes T=`{1,2}`. Although 0 is not in T,
the conditional order masses are 1/3 for `[1,2]` and 2/3 for `[2,1]`.
Thus `a ∉ T` alone cannot replace `T ⊆ S.erase a`. Conditioning can
affect comparisons with keys outside S.

A likely module is `Applications/Probability/PermutationTail.lean`,
importing the ordinary whole-order module and directly used existing
conditional/measure/list/cardinality modules, plus `HasLaw` if the standard
bundled law interface is chosen. Keep finite union and
factorial-normalization helpers private where they have no independent
client use. A named `firstEvent` and the useful on-E observation equality
are sufficient new vocabulary. No abstract probability framework or
new operation on payloads is justified.

There is no identified mathematical blocker. The genuinely new work is
the cons-support lemma, finite head-event partition, on-event tail bridge,
and assembly of the existing conditional and pushforward APIs, including
the small observation-law transport above. Likely
elaboration pressure is limited to boolean membership/filter rewrites,
finite disjoint unions or image sums, and explicit finite/nonzero ENNReal
cancellations. This preflight has not compiled any proposed statement.
The earlier whole-order and minimum-law drafts remain unaccepted
dependencies, and their eventual compilation could require local proof
repairs before this extension is attempted.

Arbitrary histories, adaptive subsets, joint disjoint restriction laws,
fresh-pivot/global-ranking coupling, algorithm implementation, expected
work, and treap charging remain separate obligations. This one-step law
is useful input to those proofs, not their completion.
