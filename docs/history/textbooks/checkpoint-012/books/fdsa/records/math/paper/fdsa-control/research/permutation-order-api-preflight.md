# Uniform relative order on a fixed subset: API and architecture preflight

Recorded 2026-11-02. This is bounded read-only preparation in the continuing
FDSA workflow, not frozen requirements, implementation, validation, or
chapter acceptance. Only this note was written. No compiler, project hash
helper, Git, cache, gate, source, tracker, or requirement was changed.

The current minimum-law draft is the unvalidated commit
`ff3dd88082c6283df40bcd86a4363841a0360b12`, saved in checkpoint 0016. It was
inspected without modification. This note continues
[finite-ranking-api-preflight.md](finite-ranking-api-preflight.md) and
[finite-ranking-source-preflight.md](finite-ranking-source-preflight.md),
and coordinates with the source contributor's
[permutation-order-source-preflight.md](permutation-order-source-preflight.md).

All Mathlib references below use the existing pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Core list equations were also
checked in the saved Lean 4.35.0 sources at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The discussion introduces no
additional source version or dependency.

## 1. Recommendation

A small full-order unit is feasible using ordinary lists, finsets,
permutations, and `uniformOn`. Fix a list `positions : List I` that contains
every index exactly once. It supplies the order of the priority labels.
For the source convention in which a sampled permutation maps a key to its
priority label, the ordered keys are `positions.map π.symm`. Restricting
that order to a fixed finset S is exactly an ordinary stable filter:

```lean
def restrictedOrder [DecidableEq I]
    (positions : List I) (S : Finset I) (π : Equiv.Perm I) : List I :=
  (positions.map π.symm).filter (fun a => decide (a ∈ S))
```

This name would identify a reusable observation, not a new list algorithm,
ranking carrier, selector, sampling operation, or execution-cost model.
The definition itself needs no finiteness, completeness, `Nodup`, order,
inhabitedness, or measurability assumption.

The coherent first unit is:

1. The exact membership, `Nodup`, and support/permutation contracts under
   the hypotheses where each is true.
2. The pointwise order bridge
   `(restrictedOrder positions S π).map π <+ positions` and the
   filter-again/intersection law. These require no probability hypothesis.
3. A universal output-fiber mass theorem: each permutation of
   `positions.filter (fun a => decide (a ∈ S))` has mass `1 / S.card!`,
   and every other list has mass zero.
4. The corresponding `Measure.map` equality with the existing uniform law
   on that finite set of lists.

The fiber theorem needs measurable structure only on the permutation
sample space. The map equality adds an explicit measurable structure on
`List I` and measurable singletons there. Separate these assumptions rather
than impose output measurability on a discrete source-event theorem.

There is no need for `LinearOrder I`, `S.sort`, a public `Fintype I`, a new
group-action instance, or a bespoke probability framework. Completeness of
`positions` already gives `Fintype.ofList positions hcomplete` locally;
a separate public `[Finite I]` would be redundant. An explicit
`[DecidableEq I]` is justified for the computational filter and
`permutations.toFinset`. The filter alone can be generalized to only a
membership decision, but carrying that additional dependent instance
through every support expression is unnecessary for this proposed unit.

## 2. Proposed statements and semantic boundaries

These signatures describe the proposed scope; they are not implemented or
elaborated declarations. Names remain routine implementation choices.
Let `base := positions.filter (fun a => decide (a ∈ S))` and
`orders := base.permutations.toFinset`. These can remain local expressions;
no public support record or second list datatype is needed.

### Value observations

With the definition above:

| Claim | Sufficient assumptions beyond the definition |
|---|---|
| `a ∈ restrictedOrder positions S π ↔ π a ∈ positions ∧ a ∈ S` | None. Invert membership in `map π.symm`. |
| `a ∈ restrictedOrder positions S π ↔ a ∈ S` | `∀ a, a ∈ positions`. |
| `(restrictedOrder positions S π).Nodup` | `positions.Nodup`. |
| `(restrictedOrder positions S π).map π <+ positions` | None. |
| `(restrictedOrder positions S π).toFinset = S` | Completeness. |
| `(restrictedOrder positions S π).length = S.card` | Completeness and `Nodup`. |
| `restrictedOrder positions S π ~ base` | Completeness and `Nodup`. |
| `(restrictedOrder positions S π).filter (fun a => decide (a ∈ T)) = restrictedOrder positions (S ∩ T) π` | None. |
| The preceding filter equals `restrictedOrder positions T π` | `T ⊆ S`. |

The mapped-sublist fact states the actual ordering relative to the supplied
label enumeration. Map π over `List.filter_sublist`, then cancel
`π ∘ π.symm` with `List.map_map`. It is stronger semantic evidence than
checking only output membership or output distribution. The intersection
identity is `List.filter_filter` plus the boolean membership equivalence;
its nested-subset specialization uses `Finset.inter_eq_right.mpr`.

An arbitrary complete enumeration defines a label order; it is not
automatically increasing for an independently supplied numeric priority
function. For the earlier labels `[-7, 100, 4]`, positions `[0, 2, 1]`
represent their increasing numeric order. Positions `[0, 1, 2]` represent
a different order. The distribution is uniform in either fixed order,
but a source comparison/treap bridge must match the intended one. No extra
priority type or order record is needed in this unit to preserve that
distinction.

### Primary fiber probability

```lean
theorem uniformOn_restrictedOrder_eq
    {I : Type*} [DecidableEq I]
    [MeasurableSpace (Equiv.Perm I)]
    [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ a, a ∈ positions)
    (S : Finset I) (xs : List I) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Equiv.Perm I))
        {π | restrictedOrder positions S π = xs} =
      if xs ∈ (positions.filter (fun a => decide (a ∈ S))).permutations.toFinset
      then (Nat.factorial S.card : ℝ≥0∞)⁻¹
      else 0
```

An equivalent first version can use `orders.card` in the reciprocal and
then rewrite the existing factorial cardinality. The universal form
retains invalid-output mass zero, including wrong support, duplicates,
and wrong length. It does not require a measurable space on I or `List I`.
Finite source fibers are measurable because the sample has measurable
singletons. A local enumeration of I supplies the finite permutation
instance.

Unlike the member-specific minimum theorem, this law needs no nonempty-S
premise: when S is empty, the target support is the singleton containing
the empty list, its cardinality is `0! = 1`, and the projection is constant.
An empty index type is also supported: its permutation space contains its
identity and its complete position list is empty.

### Pushforward meaning

```lean
theorem map_restrictedOrder_uniformOn
    {I : Type*} [DecidableEq I]
    [MeasurableSpace (Equiv.Perm I)]
    [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)]
    [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) :
    (ProbabilityTheory.uniformOn (Set.univ : Set (Equiv.Perm I))).map
        (restrictedOrder positions S) =
      ProbabilityTheory.uniformOn
        ((positions.filter (fun a => decide (a ∈ S))).permutations.toFinset :
          Set (List I))
```

Use the caller's existing sample/output measurable spaces, with local
discrete instances in concrete examples. Do not install a global instance
on permutations or lists. Finite I implies countable `List I`, not finite
`List I`; the latter would be false for any inhabited I. The output support
is finite. `Measure.ext_of_singleton` therefore applies after obtaining the
standard `List.countable` instance.

There is a mathematically weaker output hypothesis for the map theorem:
measurability of this particular finite support would suffice for an
arbitrary-measurable-set proof. The explicit measurable-singleton interface
above is the standard discrete-output form, makes its point-mass meaning
available, and avoids introducing another public theorem merely to weaken
that assumption. No output measurable hypothesis belongs on the primary
fiber theorem.

## 3. Exact pinned reuse

### Ordinary lists and finite enumeration

The following existing declarations supply the representation work.

| Existing API | Role |
|---|---|
| `Fintype.ofList [DecidableEq I] (positions : List I) (hcomplete : ∀ a, a ∈ positions) : Fintype I` | Local finite enumeration; no public `Fintype` or `Finite` argument. |
| `Equiv.instFintype` for equivalences of decidable finite types | Finite `Equiv.Perm I` after the local instance. |
| `List.mem_filter`, `List.mem_map` | Exact support, including the general `π a ∈ positions` condition. |
| `List.Nodup.map`, `List.Pairwise.filter`/`List.Nodup.filter` | Injective inverse mapping and filtering preserve distinctness. |
| `List.perm_ext_iff_of_nodup hxs hys` | Lists with no duplicates are permutations exactly when their memberships agree. Its use is visible in `Equiv.Perm.map_finRange_perm`. |
| `List.Perm.filter` | Alternatively filter the global-list permutation proof. |
| `List.filter_sublist`, `List.Sublist.map`, `List.map_map` | The mapped-sublist order bridge. |
| `List.filter_filter`, `List.filter_congr`, `List.filter_map` | Nested restriction and relabeling equivariance. |
| `List.mem_permutations : xs ∈ base.permutations ↔ xs ~ base` | Exact target-support membership. |
| `List.nodup_permutations (base) hbase : base.permutations.Nodup` | No duplicate target orders. |
| `List.length_permutations (base) : base.permutations.length = base.length!` | Support cardinality, with `List.toFinset_card_of_nodup`. |
| `List.toFinset_card_of_nodup (h : xs.Nodup) : xs.toFinset.card = xs.length` | Output length and factorial support-cardinality calculation. |
| `List.finite_toSet (l) : {x \| x ∈ l}.Finite` | A set-of-permutations presentation is also possible without a public support finset wrapper. |

Primary sources: [Fintype/OfMap](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Fintype/OfMap.lean),
[Fintype/Perm](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Fintype/Perm.lean),
[List/Nodup](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/List/Nodup.lean),
[List/FinRange](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/List/FinRange.lean),
[List/Permutation](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/List/Permutation.lean),
[Finset/Card](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Finset/Card.lean),
and [Set/Finite/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Finite/Basic.lean).
The core filter equations are in
[Init/Data/List/Lemmas](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/List/Lemmas.lean).

In particular, the pinned `List.filter_map` is

```lean
filter p (map f l) = map f (filter (p ∘ f) l)
```

for boolean p. Do not mistake Mathlib's differently shaped `List.map_filter`
lemma, which uses an existential predicate on the image, for this equation.
The simple equation plus membership preservation is the useful one here.

### Moving between whole target orders

[Logic/Equiv/Fintype](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Equiv/Fintype.lean)
already provides:

```lean
theorem Equiv.Perm.exists_extending_pair [Finite α]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm β, ∀ a, σ (f a) = g a
```

For two supported lists xs and ys, take α to be `Fin xs.length`, f to be
`xs.get`, and g to be `ys.get` with the length equality transported.
`List.Nodup.injective_get` supplies injectivity. The equality of lengths
comes from their `List.Perm` proofs. A plain `Equiv.cast` on `Fin` types
can perform the transport if a convenient specialized cast is not used.
List extensionality then gives `xs.map σ = ys`.

Both lists have exactly support S. Consequently σ maps S onto itself,
which proves `σ a ∈ S ↔ a ∈ S` for every a. This direct ambient extension
is sufficient. It does **not** promise to fix the complement, and the
unconditional proof does not require that stronger property.

An available alternative is to construct the permutation on the subtype
`{a // a ∈ S}` and extend it using
`Equiv.Perm.ofSubtype : Equiv.Perm (Subtype p) →* Equiv.Perm I`, under
`[DecidablePred p]`. Its exact useful equations are:

```lean
ofSubtype_apply_of_mem (σ) (ha : p a) : ofSubtype σ a = σ ⟨a, ha⟩
ofSubtype_apply_of_not_mem (σ) (ha : ¬p a) : ofSubtype σ a = a
ofSubtype_apply_mem_iff_mem (σ) (a) : p (ofSubtype σ a) ↔ p a
```

These are in
[Algebra/Group/End](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Group/End.lean).
`List.Nodup.getEquiv` from
[List/NodupEquivFin](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/List/NodupEquivFin.lean)
is another existing way to construct the positionwise equivalence. These
alternatives should not all become public helper layers. Prefer the direct
`exists_extending_pair` proof unless an actual later history argument needs
the fixed-complement property.

`Equiv.Perm.subtypePerm π h` remains the wrong projection: it assumes
`∀ a, p (π a) ↔ p a` and restricts that self-map to the subtype. A global
ranking generally sends S to a different set of priority labels. The
relative order is the filtered inverse list, not that restricted self-map.
Also, `List.formPerm` constructs a cycle from a list; it is not the
positionwise bijection between two orders.

### Existing probability and counting tools

The bounded search inspected `Probability/UniformOn`,
`Probability/Distributions/Uniform`, `Measure/Count`, `Measure/Map`, and
existing finite-cardinality/fiber lemmas. It found no ready-made theorem
saying that an arbitrary equal-fiber finite map pushes `uniformOn` forward
to `uniformOn` on its image. This is a bounded search finding, not a claim
about every possible theorem encoding elsewhere.

`Measure.uniformOfFinset` exists in `Probability/Distributions/Uniform`,
with singleton and cardinality-ratio equations. It supplies no missing
equal-fiber argument and would introduce an unnecessary bridge from the
already chosen `uniformOn` law. Old `PMF.uniformOfFintype` names are
deprecated aliases at this pin; do not introduce a second distribution
representation through them. `pdf.IsUniform` likewise names a law rather
than proving the required combinatorial pushforward.

The exact sufficient APIs are:

```lean
ProbabilityTheory.uniformOn_univ [Fintype Ω] :
  uniformOn Set.univ E = Measure.count E / Fintype.card Ω

Measure.count_apply (hE : MeasurableSet E) : Measure.count E = E.encard

Set.encard_preimage_of_bijective (hf : Function.Bijective f) (E : Set β) :
  (f ⁻¹' E).encard = E.encard

sum_measure_preimage_singleton (orders : Finset β)
    (hf : ∀ y ∈ orders, MeasurableSet (f ⁻¹' {y})) :
  (∑ y ∈ orders, μ (f ⁻¹' {y})) = μ (f ⁻¹' ↑orders)

ENNReal.eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹

measurable_of_finite [Finite Ω] [MeasurableSingletonClass Ω] (f : Ω → β) :
  Measurable f

Measure.map_apply (hf : Measurable f) (hE : MeasurableSet E) :
  μ.map f E = μ (f ⁻¹' E)

Measure.ext_of_singleton [Countable β] (h : ∀ y, μ {y} = ν {y}) : μ = ν
```

The usual measurable-space arguments are implicit in these signatures.
`ProbabilityTheory.uniformOn_apply_finset` gives the target singleton mass
by intersecting `orders` with `{xs}`. `Equiv.mulRight σ.symm` is an existing
permutation of permutation samples, and `Equiv.Perm.mul_apply` identifies
the right composition. `Equiv.inhabited'` supplies the identity permutation
even for empty I. `instIsProbabilityMeasure_uniformOn_univ` normalizes the
finite global law.

Primary sources: [UniformOn](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/UniformOn.lean),
[Count](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Count.lean),
[Set/Card](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Card.lean),
[Measure/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Basic.lean),
[Map](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Map.lean),
[Dirac/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/Dirac/Basic.lean),
and [MeasurableSpace/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean).
`List.countable` is in
[Logic/Equiv/List](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Equiv/List.lean).

For an alternative entirely cardinal proof,
`Finset.card_eq_sum_card_fiberwise` in
[BigOperators/Group/Finset/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean)
sums the finite fiber sizes. There is no need to calculate the individual
fiber size as `|I|! / |S|!`; event-mass normalization avoids that division.

## 4. Concrete proof route and genuine missing work

1. **Support and value semantics.** The mapped global list has no duplicates
   and contains every index. Filter it and use membership to identify its
   support with S. `perm_ext_iff_of_nodup` compares it with base. Prove the
   mapped-sublist and filter-intersection equations directly from standard
   list equations, without probability imports in their hypotheses.

2. **Finite target.** `List.mem_permutations` identifies exactly the supported
   outputs. Base itself is a member, including base=`[]`. The target's card
   is `S.card!` by `nodup_permutations`, `toFinset_card_of_nodup`,
   `length_permutations`, and the base-length contract.

3. **Transitive relabeling.** For supported xs,ys, obtain σ with
   `xs.map σ = ys` using `exists_extending_pair`. Show membership preservation
   from their common support. The required missing list lemma is therefore
   small: two `Nodup` lists of the same support admit a global relabeling
   taking one to the other and preserving that support. It can be private
   unless another concrete client needs the exact statement.

4. **Equivariance and fiber bijection.** Write f for `restrictedOrder positions S`.
   The orientation is

   `f (π * σ.symm) = (f π).map σ`.

   Indeed `(π ∘ σ.symm)⁻¹ = σ ∘ π.symm`; `map_map`, `filter_map`, and
   preservation of S give the identity. For `E_x := {π | f π = xs}`,
   right multiplication by `σ.symm` has `E_y` preimage `E_x`.
   The reverse implication uses injectivity of `List.map σ`, available
   through `List.map_injective_iff`. This is a whole-output fiber bijection,
   not merely a minimum-event argument.

5. **Normalize equal masses.** Source finiteness makes every fiber measurable.
   `uniformOn_univ`, `count_apply`, and `encard_preimage_of_bijective`
   give equal masses. `sum_measure_preimage_singleton orders` sums them
   to one because the projection always lands in orders. Constant-sum
   simplification gives `orders.card * p = 1`; commute and use
   `ENNReal.eq_inv_of_mul_eq_one_left`. Unsupported fibers are empty.
   This proves the universal fiber theorem without target measurability.

6. **Pushforward.** The projection is measurable by `measurable_of_finite`.
   Obtain `Countable (List I)` from the standard `List.countable` instance.
   Apply `Measure.ext_of_singleton`, rewrite `Measure.map_apply`, use the
   fiber theorem, and compare with `uniformOn_apply_finset` on the target.
   This proves equality of the supplied measures, rather than substituting
   a separately sampled subset order without a coupling proof.

Thus the genuine new mathematics is the list relabeling/equivariance
connection and its finite-law assembly. The standard algebra, finite sets,
permutations, and measure semantics are already present. A public generic
equal-fiber theorem or a group-action framework is unnecessary for this
single projection. If a second independent map later justifies extracting
the normalization argument, do that as an ordinary theorem over existing
maps and measures.

The current minimum module's `uniformOn_univ_preimage` is private. It is
not an importable public API, and the minimum probability theorem itself
does not imply uniform full orders. Reuse the same underlying Mathlib
cardinality facts without editing the saved minimum candidate during this
preflight. Any later decision to expose a shared elementary helper belongs
in that unit's explicit implementation scope, not in a new probability
framework.

## 5. Connected cases and consequential boundaries

The already saved independent calculations are
[permutation-order-calculations.json](permutation-order-calculations.json),
SHA-256 `54163e6729373a9c78cd82432d48ae827498321c64e53e3c5160cebb54ca2f80`.
They are arithmetic preparation, not formal validation. The source note
owns additional overlap/history calculations; they are not automatically
extra first-unit obligations.

| Case or boundary | What it establishes |
|---|---|
| `I=Fin 4`, positions `[0,1,2,3]`, S=`{0,2,3}` | Six complete output lists, each of mass `1/6`; each has four global preimages. A generic-law client on a triple distinguishes this unit from a two-element/minimum example. |
| Key-to-label π=`(1,2,0)`, positions `[0,1,2]`, S=`{0,1}` | The inverse list is `[2,0,1]` and the correct output is `[0,1]`; mapping π directly gives `[1,0]`. Both orientations are marginally uniform, so a distribution theorem alone would miss this source error. |
| Empty S and empty I | The sole supported output is `[]` with mass one. No false `1/0` first-member claim or nonempty-index assumption. |
| Singleton S and full S | The singleton output is deterministic; full restriction yields the ordinary uniform global-list order. |
| Restrict a result again to a nested subset | A connected use of the pointwise filter-composition law. It says nothing by itself about conditioning. |
| Incomplete positions `[0]` on Fin2, S=`{0}` | Under the swap, the projection is `[]`, while base is `[0]`. Completeness cannot simply be omitted. |
| Complete but repeated positions `[0,0,1]` on Fin2, S full | The swap produces `[1,1,0]`, outside the permutations of base. Distinct positions cannot simply be omitted. |
| Condition on “1 precedes 2” in Fin3, then observe fixed S=`{0,1}` | Output probabilities become `1/3` and `2/3`; unconditional uniformity is not an arbitrary conditional-history law. |
| Adaptive S=`{0, earlier(1,2)}` | Key 0 is first with probability `1/3`, not `1/2`; S must be fixed before sampling. |
| Uniform even permutations of four keys | The recorded enumeration has uniform minima for every fixed subset but not a uniform full order. The existing minimum theorem is not a sufficient hypothesis for this stronger result. |

The proposed first examples should exercise the triple law, the pointwise
inverse orientation, and the empty/full/nested specializations. Reuse the
existing overlap example when only correlation needs illustration; avoid
an arbitrary example quota or formalizing every exploratory counterexample
merely because it was calculated.

## 6. Placement, imports, and remaining scope

Suggested placement is `Applications/Probability/PermutationOrder.lean`
with connected cases in `Examples/PermutationOrder.lean`. This is a law
about an ordinary list observation of an existing random input; it does
not change `Table`, `Kernel`, measured resource execution, or sequence
interfaces. The existing `Table.comp`, `Table.kernel`, and joint-law
contracts remain their established semantics and need no extension.

Candidate direct imports are `Mathlib.Data.List.Permutation`,
`Mathlib.Data.Fintype.Perm`, `Mathlib.Logic.Equiv.Fintype`, and
`Mathlib.Probability.UniformOn`, with `Mathlib.Logic.Equiv.List` for the
countable-list measure-extensionality route and explicit support imports
where their public export paths require them. No expectation, continuous
density, conditional-expectation, sorting, or group-action hierarchy is
needed. The exact import closure still needs compilation in a later
authorized validation phase.

No mathematical obstruction was found. The actual implementation work
remaining is finite-position transport between xs and ys, the membership
preservation/equivariance proof, and the finite fiber/map assembly. Those
are concrete proof obligations, not accepted declarations. The dependent
`Fin` length transport and the current module export boundaries are the
main source-level elaboration risks; this preflight ran no Lean process.

For Chapter 2, this supports fixed filtered input orders. The law of recursive
subproblems after observed pivots/comparisons, duplicate occurrences, both
recursive branches, and the source's actual cost model remain separate.
For Chapter 10, it supports restrictions of one common ranking; canonical
treap construction/root/ancestor bridges, conditional depth and weighted
charging remain separate. Overlapping outputs use the same π and are not
asserted independent. Conditional histories require the exact revealed
event, positive normalization, and a new invariance/counting proof for that
event. No expectation or preceding-position mean belongs to this unit.
