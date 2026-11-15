# Finite-ranking minimum law: API and architecture preflight

Recorded 2026-11-02. This is read-only preparation in the continuing FDSA
workflow, not frozen requirements, implementation, validation, or chapter
acceptance. The old Chapter 1 gate remains unchanged. Only this note was
written; no compiler, hash helper, Git, cache, gate, source, or tracker action
was run.

The coordinated mathematical/source scope is
[finite-ranking-source-preflight.md](finite-ranking-source-preflight.md).
Earlier probability reuse and source boundaries remain in
[probability-api-preflight.md](probability-api-preflight.md) and
[probability-source-preflight.md](probability-source-preflight.md).

## 1. Recommendation

Start with one minimum-event probability theorem. For a finite index type I,
fix an injective priority map `priority : I → P` into a linearly ordered type
P, draw one uniform `π : Equiv.Perm I`, and assign index a the priority
`priority (π a)`. For a fixed finset S and a member a, prove

\[
\Pr[\forall b\in S,\;priority(\pi(a))\le priority(\pi(b))]
=|S|^{-1}.
\]

Existing Mathlib supplies the probability carrier, finite measure,
permutations, transpositions, finite minima, cardinality invariance and
disjoint-event summation. The missing work is the small combinatorial
connection: relabeling two members exchanges their minimum events, and those
events partition the permutation space. No new probability/ranking record,
sampler, executor, action instance, or minimum selector is needed.

The minimum event itself needs only an order relation on P. Its probability
law needs a linear order and injectivity to obtain unique minima. Neither I
nor the source payloads need an order or measurable structure; P needs no
finiteness or measurable structure. Use `[Finite I]` publicly and choose
`Fintype.ofFinite I` locally in the classical proof. Give probability laws
explicit existing `MeasurableSpace (Equiv.Perm I)` and
`MeasurableSingletonClass (Equiv.Perm I)` parameters. Do not install a global
measurable-space instance on permutations.

A count of indices preceding S has a short further expectation proof, but
it adds an actual count/indicator bridge and is a separate possible unit.
Full relative-order restriction and conditional remaining-order laws add
substantially different representation and distribution arguments. None is
required merely to prove the first-member law.

## 2. Existing conaled interfaces

The inspected local probability modules already interpret ordinary finite
stochastic tables as Mathlib kernels. `Applications.Probability.Table.comp`,
`Table.deterministic`, `Table.kernel`, `Table.kernel_comp` and
`Table.kernel_deterministic` in `Applications/Probability/FiniteKernel.lean`
cover their established operational/interpretation jobs. They do not need
extension for a fixed uniform-permutation event theorem.

`Examples.ProbabilityCorrelation.shared_first`, `shared_second`,
`independent_first`, `independent_second`, `shared_off_diagonal`,
`independent_off_diagonal` and `joint_distributions_differ` already retain
the distinction between shared randomness and a product law. The proposed
overlapping-subset example below uses the same principle with a single
global permutation. It does not require converting a finite ranking into
a table or manufacturing independent subset draws.

The bounded local search found no existing subset-minimum probability or
uniform relative-order restriction theorem. This is a specific missing
combinatorial connection, not evidence that conaled lacks probability
semantics. The new accumulated-work draft is analytic and also supplies no
ranking law; a minimum theorem would establish none of its algorithmic
cost/drift premises by itself.

## 3. Proposed minimal statements and assumptions

The following are proposed signatures, not declarations already present or
compiled. Names are provisional.

```lean
def minimumEvent {I P : Type*} [LE P]
    (priority : I → P) (S : Finset I) (a : I) : Set (Equiv.Perm I) :=
  {π | a ∈ S ∧ ∀ b ∈ S, priority (π a) ≤ priority (π b)}

theorem uniformOn_minimumEvent
    {I P : Type*} [Finite I] [LinearOrder P]
    [MeasurableSpace (Equiv.Perm I)]
    [MeasurableSingletonClass (Equiv.Perm I)]
    (priority : I → P) (hinj : Function.Injective priority)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Equiv.Perm I))
      (minimumEvent priority S a) = (S.card : ℝ≥0∞)⁻¹
```

`ha` already gives `S.Nonempty`; do not add a redundant nonemptiness
argument to this member-specific theorem. The membership conjunct makes
the event empty for outsiders and for an empty S. The reciprocal formula
is only claimed for members, never as a first-element formula for an empty
set. A closed event expression instead of a named `minimumEvent` is also
reasonable if the eventual clients do not reuse the predicate.

No public `[DecidableEq I]`, `[Fintype I]`, `[Nonempty I]`, or `[Inhabited I]`
is needed. Finset membership is a proposition; classical decisions and
enumeration are proof-local. `Equiv.Perm I` always has its identity, even
when I is empty. For arbitrary source payloads, use the finite index or
subtype representing this fixed input; do not impose finiteness on the
entire payload type.

The priority orientation is explicit. In the source-position specialization
`I = Fin U`, `P = Fin U`, `priority = id`, π maps a key index to its priority
position. A position-to-key list enumeration uses `π.symm`. Permutation
multiplication satisfies `(π * τ) a = π (τ a)`, so exchanging key labels is
**right** multiplication by the transposition. Left multiplication changes
priority labels and generally does not preserve their order.

The finite probability law needs measurable singletons: without them,
an outer-measure value on a nonmeasurable minimum event need not be its
cardinality ratio. On this finite sample space those hypotheses make every
event measurable and every map measurable. Concrete examples may choose
`letI : MeasurableSpace (Equiv.Perm I) := ⊤` locally. The inspected standard
instances include `Fin n`, but do not install a default measurable space
for arbitrary `Equiv.Perm I`.

## 4. Exact existing APIs for the first unit

All Mathlib links below refer to the pinned revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Signatures retain the relevant
parameters/hypotheses; ambient type variables are displayed in prose where
their complete library context is routine.

### Finite samples and relabeling

From [Fintype/EquivFin.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Fintype/EquivFin.lean)
and [Fintype/Perm.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Fintype/Perm.lean):

```lean
noncomputable def Fintype.ofFinite (α : Type*) [Finite α] : Fintype α

instance Equiv.instFintype
    [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    Fintype (α ≃ β)

theorem Fintype.card_perm [DecidableEq α] [Fintype α] :
    Fintype.card (Equiv.Perm α) = (Fintype.card α)!
```

Only the instances are needed. The factorial theorem exists but its
evaluation is unnecessary for the proposed proof. The broader
`Mathlib.Data.Finite.Perm` module adds `Nat.card_perm`; its group-theoretic
imports are also unnecessary for this first unit.

[Algebra/Group/End.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Group/End.lean)
provides `Equiv.Perm.mul_apply (f g : Equiv.Perm α) (x) :
(f * g) x = f (g x)`. Its imported
[Group/Units/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Group/Units/Equiv.lean)
provides, under `[Group G]`:

```lean
Equiv.mulRight (g : G) : Equiv.Perm G
Equiv.coe_mulRight (g : G) : ⇑(Equiv.mulRight g) = fun x => x * g
Group.mulRight_bijective (g : G) : Function.Bijective (· * g)
```

For `G = Equiv.Perm I`, use `g = Equiv.swap a b`. From
[Logic/Equiv/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Equiv/Basic.lean),
the relevant equations are `Equiv.swap_apply_left`,
`Equiv.swap_apply_right`, `Equiv.swap_apply_of_ne_of_ne`, and
`Equiv.swap_swap`. Classical equality on I is sufficient. No group-action
typeclass instance on the sample space is required.

### Uniform measure and finite-bijection invariance

[Probability/UniformOn.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/UniformOn.lean):

```lean
def ProbabilityTheory.uniformOn (s : Set Ω) : Measure Ω

theorem ProbabilityTheory.uniformOn_univ [Fintype Ω] {s : Set Ω} :
    uniformOn Set.univ s = Measure.count s / Fintype.card Ω

instance ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ
    [Finite Ω] [Nonempty Ω] :
    IsProbabilityMeasure (uniformOn (Set.univ : Set Ω))

lemma ProbabilityTheory.uniformOn_apply_finset
    [DecidableEq Ω] [MeasurableSingletonClass Ω] {s t : Finset Ω} :
    uniformOn (s : Set Ω) (t : Set Ω) =
      ((s ∩ t).card : ℝ≥0∞) / (s.card : ℝ≥0∞)
```

The two cardinalities in the last conclusion are cast to ENNReal; no
natural-number division is intended. No PMF constructor is needed. At this pin the old
`PMF.uniformOfFintype` name is a deprecated alias of a measure constructor,
not an appropriate remembered API to introduce.

The inspected `UniformOn` module has no dedicated permutation-invariance
or equal-fiber pushforward theorem. Its needed instance is already a short
consequence of these exact APIs:

```lean
-- MeasureTheory/Measure/Count.lean
Measure.count_apply (hE : MeasurableSet E) :
  Measure.count E = E.encard

-- Data/Set/Card.lean
Set.encard_preimage_of_bijective (hf : Function.Bijective f) (E : Set β) :
  (f ⁻¹' E).encard = E.encard

-- MeasureTheory/MeasurableSpace/Basic.lean
measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) :
  Measurable f

-- MeasureTheory/Measure/Map.lean
Measure.map_apply (hf : Measurable f) (hE : MeasurableSet E) :
  μ.map f E = μ (f ⁻¹' E)
```

Sources: [Count](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Count.lean),
[set cardinality](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Card.lean),
[measurability](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean),
[measure map](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Map.lean).

For finite Ω with measurable singletons, every E is measurable by
`E.toFinite.measurableSet`. After selecting a local Fintype, rewrite both
uniform measures with `uniformOn_univ`, both counts with `count_apply`,
and the preimage cardinal with `encard_preimage_of_bijective`. This proves
`uniformOn univ (e ⁻¹' E) = uniformOn univ E` for any `e : Ω ≃ Ω`.
If a pushforward equality is actually needed, `Measure.ext` and
`Measure.map_apply (measurable_of_finite e)` give it. Keep this a local/helper
proof unless concrete second clients justify a public theorem; do not
build a replacement invariant-measure framework.

The group-action route also exists: the instance of
`(Measure.count : Measure G).IsMulRightInvariant`, `measurePreserving_mul_right`,
`SMulInvariantMeasure`, `measure_preimage_smul`, and
`smulInvariantMeasure_map` in
[Group/Measure.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Group/Measure.lean)
and [Group/Action.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Group/Action.lean).
The counting-measure right-invariance instance assumes `[Group G]` and
`[MeasurableMul G]`; the action-map theorem additionally asks for the
appropriate action/measurability and equivariance data. These are useful
existing abstractions, but supplying their instance plumbing is more work
than the finite-bijection argument here. The inspected transitive-action
modules offer orbit/transitivity theorems, not a ready-made finite uniform
subset-minimum law.

### Existence, disjoint partition, and normalization

The generated dual of `Finset.exists_max_image` in
[Finset/Max.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Finset/Max.lean)
has the exact useful form:

```lean
Finset.exists_min_image [LinearOrder P]
    (S : Finset I) (f : I → P) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, f a ≤ f b
```

Use `f = priority ∘ π`. Two such minima coincide by antisymmetry,
`hinj`, and `π.injective`. This supplies both the cover and pairwise
disjointness of the event family without selecting a public minimum.

[Measure/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Basic.lean):

```lean
measure_biUnion_finset {S : Finset I} {E : I → Set Ω}
    (hd : Set.PairwiseDisjoint (↑S) E)
    (hm : ∀ a ∈ S, MeasurableSet (E a)) :
    μ (⋃ a ∈ S, E a) = ∑ a ∈ S, μ (E a)

sum_measure_preimage_singleton (S : Finset I) {f : Ω → I}
    (hf : ∀ a ∈ S, MeasurableSet (f ⁻¹' {a})) :
    (∑ a ∈ S, μ (f ⁻¹' {a})) = μ (f ⁻¹' ↑S)
```

The first directly matches events; the second is available if a later
client already has a minimum selector. There is no reason to introduce a
selector solely to use the second theorem.

Relabeling by `π ↦ π * Equiv.swap a b` gives equal event masses for a,b∈S.
The disjoint union is `Set.univ`; the existing probability instance gives
mass one. `Finset.sum_const` and `nsmul_eq_mul` turn the sum into
`(S.card : ℝ≥0∞) * p = 1`. After commuting the product, use
`ENNReal.eq_inv_of_mul_eq_one_left (h : p * c = 1) : p = c⁻¹` from
[ENNReal/Inv.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Basic/ENNReal/Inv.lean).
This theorem derives its necessary nonzero/finite consequences internally.
An explicit division proof can instead use `ENNReal.eq_div_iff` after
`Finset.card_pos.mpr ⟨a,ha⟩` and `ENNReal.natCast_ne_top`.

An alternative entirely finite counting route already has
`Finset.card_equiv (e : α ≃ β) (h : ∀ i, i∈s ↔ e i∈t) : s.card=t.card`
and `Finset.card_eq_sum_card_fiberwise
(H : (s : Set α).MapsTo f t) : s.card = ∑ b∈t, (s.filter (f · = b)).card`.
The event partition route is shorter here because it avoids introducing f
or calculating fiber sizes explicitly.

## 5. Separately scoped extensions

### A. Count of labels before the subset: feasible without numeric ranks

For the same arbitrary ordered priority target, the actual count

\[
B_S(\pi)=\operatorname{ncard}\{b:I\mid
 \forall a\in S,\;priority(\pi(b))<priority(\pi(a))\}
\]

is defined by existing `Set.ncard`; no new observation carrier is needed.
For b∈S the strict-before predicate is false. For b∉S it is exactly the
minimum event of b in `insert b S`, using injectivity to replace
non-strict comparisons to other elements by strict comparisons. Therefore

\[
\mathbb E[B_S]=\frac{\operatorname{Nat.card}(I)-S.card}{S.card+1}.
\]

This also handles S=∅: the predicate is vacuous, `B_S = Nat.card I`, and
the right side has denominator one. It does not call the empty set's
nonexistent minimum or interpret its count-plus-one as a first position.

The additional proof obligations are an exact finite count/indicator
identity, the outside-event equivalence, and finite integral linearity.
The count is automatically bounded by `Nat.card I`; there is no infinite
integral or stopping-time problem. These are modest but real additions,
so do not silently include them in a first-member unit.

Exact reusable declarations are `Set.ncard_eq_toFinset_card
(s : Set α) (hs : s.Finite := ...) : s.ncard = hs.toFinset.card`,
`Set.ncard_univ`, `Finset.card_insert_of_notMem`,
`Finset.card_sdiff_of_subset`, and `Finset.card_sdiff_add_card_eq_card`.
Choose a local Fintype only to form the proof's finite indicator sum.

For ENNReal expectation, use the supported, nondeprecated names
`lintegral_finsetSum` or `lintegral_finsetSum'` in
[Lebesgue/Add.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean):

```lean
lintegral_finsetSum' (s : Finset β) {f : β → Ω → ℝ≥0∞}
    (hf : ∀ b∈s, AEMeasurable (f b) μ) :
    (∫⁻ ω, ∑ b∈s, f b ω ∂μ) = ∑ b∈s, ∫⁻ ω, f b ω ∂μ
```

`lintegral_indicator_one (hE : MeasurableSet E)` gives
`∫⁻ ω, E.indicator 1 ω ∂μ = μ E`. For the later treap real expectation,
`Integrable.of_finite` supplies integrability under a finite sample type,
measurable singletons and a finite measure. `integral_finsetSum` and
`integral_indicator_one` then give the same proof with real masses; see
[Bochner/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
[Bochner/Set.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Bochner/Set.lean)
and [L1Space/Integrable.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean).
Do not silently use totalized real integrals without this finite-measure
integrability justification.

### B. First global position: a further semantic bridge

For S nonempty, `B_S+1` is the one-based first position in the finite
priority order. To match a concrete source rank, supply
`rank : I ≃ Fin U` and priority `rank`; then prove pointwise that it equals

```lean
(((S.image (fun a => rank (π a))).min' (hS.image _)).val + 1)
```

The rank equivalence itself supplies finiteness of I if needed locally.
The image/preimage cardinality laws and `Fin.card_Iio (b : Fin U) :
(Finset.Iio b).card = b.val` from
[Interval/Finset/Fin.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Interval/Finset/Fin.lean)
establish that every earlier position corresponds to exactly one index.
Then `E[T] = 1+(U-S.card)/(S.card+1) = (U+1)/(S.card+1)`.
Alternatively the count-plus-one definition itself can state the ordinal
position, with its bridge to a numeric rank left explicit.

This expectation is not the expected numeric value of an arbitrary
injective priority map. Gaps, negative values, or a monotone rescaling of
priorities preserve the minimum law but change such numeric expectations.
No full relative-order theorem, independence theorem, or binomial-tail
identity is needed for this expectation route.

### C. Full relative-order restriction: more work and a different output

For `I = Fin U`, the ordinary list expression

```lean
((List.finRange U).map π.symm).filter (fun a => decide (a ∈ S))
```

is an appropriate restricted ordering. Its distribution can be compared
using `Measure.map` with `uniformOn` on the finite set
`(S.sort.permutations.toFinset : Set (List (Fin U)))`. This uses existing
Lists/Finsets, not a new ranking datatype. Alternatively compress the
priorities of S to `Fin S.card`, using the increasing enumeration of
`S.image π`, to produce an ordinary `Equiv.Perm (Fin S.card)` after choosing
a fixed enumeration of S. The list output is closer to the quicksort
filtering client and avoids immediate dependent-cardinality casts.

Relevant existing APIs include:

- `Equiv.Perm.map_finRange_perm σ : (List.finRange U).map σ ~ List.finRange U`
  in [List/FinRange.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/List/FinRange.lean).
- `Finset.sort_perm_toList`, `sort_nodup`, `sort_toFinset`, `map_sort`, and
  `orderIsoOfFin (S : Finset α) (h : S.card = k) : Fin k ≃o S` in
  [Finset/Sort.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Finset/Sort.lean).
- `List.mem_permutations : l ∈ t.permutations ↔ l.Perm t`,
  `List.length_permutations t : t.permutations.length = t.length!`, and
  `List.nodup_permutations t ht` in
  [List/Permutation.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/List/Permutation.lean).
- `Equiv.Perm.ofSubtype : Equiv.Perm (Subtype p) →* Equiv.Perm I`,
  `ofSubtype_apply_of_mem`, `ofSubtype_apply_of_not_mem`, and
  `ofSubtype_apply_mem_iff_mem` extend a permutation of S to a relabeling
  fixing its complement. This supports bijections between entire order
  fibers.

What remains is an actual projection with membership/nodup/order semantics,
an equivariance or equal-fiber theorem for every target order, and normalized
pushforward equality. One can use extended subtype permutations to move
between order fibers, rather than deriving all fiber cardinalities by
factorials. The proof has more structure than the two-label minimum-event
argument and should be separately scoped.

Do not use `Equiv.Perm.subtypePerm π h` as that projection. Its actual
signature requires `h : ∀ x, p (π x) ↔ p x`, and its action is literally
`x ↦ π x` on the same subtype. An arbitrary global ranking maps S into a
set of priority positions, generally not S itself. Restriction of a
self-map preserving S is not restriction/compression of the relative
order induced on S. `subtypePerm` is useful for a relabeling already known
to preserve S, not for silently constructing the desired restricted law.

If a later consumer wants a named law predicate, existing
`ProbabilityTheory.HasLaw X ν μ` already packages `AEMeasurable X μ` and
`μ.map X = ν`, with `HasLaw.comp` and `HasLaw.measure_eq`; see
[Probability/HasLaw.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/HasLaw.lean).
There is no reason to add a parallel uniform-ranking law record.

### D. Conditional laws remain distinct

The unconditional theorem does not make S uniform after S is chosen from
the sampled ranking. Nor does it establish the law of recursive subproblems
after arbitrary observations. `uniformOn_inter` and `uniformOn_add_compl_eq`
are existing conditional normalization/total-probability tools, but the
particular conditioning-event bijection still must be proved. Positive
conditioning mass and the exact information revealed are part of the later
statement. Full disjoint-subset independence is another optional joint
result; overlapping restrictions generally remain correlated.

## 6. Connected cases, placement, and validation limits

The first unit can demonstrate reuse without importing expectation theory:

1. Under one uniform permutation of three indices, let S={0,1}, T={1,2}.
   The event that 1 is minimum in both is exactly its minimum event in
   S∪T. The generic theorem therefore gives joint mass1/3 and marginal
   masses1/2, whose product is1/4. This verifies a real shared-law
   distinction, rather than merely duplicating a scalar calculation.
2. Use an injective priority assignment into Int with nonuniform gaps and
   a negative value, and a two-element S. Each member still has probability
   1/2. This exercises the absence of a finite-target, index-order, or
   numeric-position assumption. Singleton S gives mass1; an empty S has
   no member instance, including on an empty index universe.

The scope remains support for fixed-subset minimum indicators in quicksort
and treap analyses. Actual comparisons, ancestor/root characterizations,
recursive conditioning, joint input construction, and execution costs are
chapter-specific proofs. The expected-position corollary would support one
treap estimate; it would not prove expected set-operation work or justify
factoring correlated random weights.

Suggested narrow placement is
`Applications/Probability/PermutationMinimum.lean`, with connected cases in
`Examples/PermutationMinimum.lean`. The final names are routine choices;
there is no public API change to existing table/kernel/resource modules.
Candidate direct core imports are `Mathlib.Probability.UniformOn`,
`Mathlib.Data.Fintype.Perm`, and `Mathlib.Data.Finset.Max`, plus explicit
support imports only if required by the actual proof. The permutation
module already imports `Algebra.Group.End` and hence `Group.Units.Equiv`.
The expectation and full-list extensions should bring their own imports.

All APIs and proof routes above were inspected in source, not compiled.
Some declarations (`Finset.exists_min_image`, for example) are generated
by the source's `to_dual` attribute; their stated signatures were checked
against that source and existing call sites. The import closure and the
proposed proof elaboration remain to be validated in a later frozen unit.
No artifact hashes were computed under this task's explicit restriction.
