# Directed limits and continuous partial-spine folds

This development extends the finite observations from the [finite observation model](adwh-partial-spine-observations.md) with directed
limits, one generic ideal interpreter, and continuous partial-spine consumers.
The retained clients consume the existing guarded, paused, emit-once and silent
producer observations. These are denotational statements over fixed labels;
the producer transition counts remain separate operational evidence.

## Ownership and reuse

| Owner | Contract |
|---|---|
| `SquareKit.DirectedLimits` | A named full Pi CPO using standard pointwise data, a scoped instance, evaluation continuity and transport of nonempty directed suprema. |
| `SquareKit.IdealCompletion` | Standard ideal directed unions, a named pointed-ideal CPO, principal density, one generic extension and its transport and parameter laws. |
| `SquareKit.PartialSpine.Cut` | Constructor-budget truncation with an independent prefix/end equation. |
| `SquareKit.PartialSpine.Observations` in `PartialSpine/Limits.lean` | The actual observation CPO, semantic cons, stream limits and semantic fold laws. |
| `PartialSpineLimits` | Producer-connected truncation, first-output and fused consumers, strictness boundaries, and a function-valued family of all cuts. |

The normal entrypoint imports `Examples.PartialSpineLimits` through
`SquareApplications.lean`. `Order.Ideal`, `DirectedOn`, `IsLUB`, `Monotone`,
ordinary `Set.image`, `CompletePartialOrder` and `ScottContinuous` keep their
standard Mathlib owners. There is no additional domain or continuity hierarchy.
The existing finite spine, producer semantics and principal embedding remain
unchanged.

## Full directed completeness and its boundary

For a **nonempty directed** set of ideals, `directedUnion` uses Mathlib's
`Order.isIdeal_sUnion_of_directedOn`. Its membership and least-upper-bound laws
identify the result independently as the set union:

```lean
p ∈ directedUnion S nonempty directed ↔ ∃ I ∈ S, p ∈ I
```

The bottom case is separate. A pointed base preorder gives the existing bottom
ideal, and `pointedSup` uses it for the empty directed family. The named
`pointedIdealCPO` preserves the standard ideal order and bottom and supplies
this supremum operation. It is installed only for
`PartialSpine.Observations α`. A nondirected input to the total `sSup` operation
also uses the fallback bottom; no least-upper-bound claim is made for that
input. Incompatible spine observations are not given a complete-lattice
instance.

`DirectedLimits.piCompletePartialOrder` constructs full directed completeness
for **any dependent index type** and a CPO at each index. It reuses the existing
pointwise order, bottom and `Pi.supSet`; `isLUB_pi` proves its directed limit
law. The instance is scoped to `SquareKit.DirectedLimits`. The example module
checks definitional equality of its supremum data both with `Pi.supSet` and,
where complete lattices are available, with the existing complete-lattice
route. This is full directed completeness, including the empty family, rather
than a result limited to natural-number chains.

`scottContinuous_eval` works under just coordinate preorders and preserves any
existing nonempty directed least upper bound. `map_sSup` supplies the CPO-level
transport rule with explicit nonempty and directed premises. Scott continuity
in this development follows the standard convention: it preserves nonempty
directed limits and need not preserve bottom.

## One generic extension

For any preorder `P`, any ideal `I : Order.Ideal P`, and an interpreter `h`,
the operation is simply:

```lean
IdealCompletion.extend h I = sSup (h '' (I : Set P))
```

The definition only needs supremum data. The laws require a CPO result and
`Monotone h`. The image is directed because the ideal is directed and `h` is
monotone; it is nonempty because the ideal is nonempty. `extend_isLUB`,
`le_extend` and `extend_le` characterize the result by all finite
approximations. `extend_principal` recovers `h p` exactly, and
`extend_monotone` and `extend_scottContinuous` supply the ideal-input laws.
None requires a bottom in the source preorder.

`principal_isLUB` identifies any ideal with the directed limit of its own
observed principal ideals. `continuous_ext` consequently identifies two
Scott-continuous maps that agree on those principal ideals. It needs only a
partial order in the result, because its argument uses existing least upper
bounds rather than an additional supremum operation.

Continuous observers commute with the generic extension through `map_extend`
and `extend_fusion`. These generic laws have no strictness premise: the image
of an ideal is nonempty. Strictness appears later when an observer must
commute with the finite fold's bottom case. `extend_mono_interpreter` and
`extend_param_scottContinuous` handle changing the interpreter. The latter
needs only a preorder on the parameter and pointwise parameter continuity.
Infinite seed continuity reuses this law.

## The final nil consumes a constructor budget

Finite `cut` observes at most its budget of constructors. Its meaning is fixed
by the independent view theorem:

```lean
view (cut n s) =
  ((view s).1.take n, (view s).2 && decide ((view s).1.length < n))
```

The strict comparison is essential. A budget that observes all labels may
still fail to observe the final nil:

| Input and budget | Result |
|---|---|
| `cut 0 nil` | `bottom` |
| `cut 1 nil` | `nil` |
| `cut 1 (ofList [a])` | `cons a bottom` |
| `cut 2 (ofList [a])` | `ofList [a]` |

These four checked cases use the independent view. `cut_le` states that each
cut is an observation of its input; `cut_monotone` allows that finite
interpreter to extend over ideals. `cut_openPrefix` retains an unknown end.

## Semantic cons and independent stream limits

Semantic cons is the generic extension of principal finite cons. Its exact
membership law is:

```lean
q ∈ Observations.cons a I ↔
  q = ⊥ ∨ ∃ t ∈ I, q = PartialSpine.cons a t
```

`cons_principal` connects it to the finite constructor. It is monotone and
Scott continuous, while `cons_bottom` and `cons_not_strict` show that cons
applied to bottom has a known head and an unknown tail. This supplies a
concrete continuous operation that does not preserve the empty supremum.

The pre-existing independent `Stream'` ideal is the least upper bound of all
principal open prefixes. `stream_prefixes_directed`, `stream_prefixes_isLUB`
and `stream_eq_sSup_prefixes` prove this without redefining the carrier from
the new supremum operation. `stream_cons` connects the limit to semantic cons
at the first label and shifted stream. The earlier `stream_ne_principal` still
separates the resulting ideal from every finite spine.

## Fold laws with the required hypotheses

The semantic right fold specializes the shared extension to the already
defined finite partial-spine fold:

```lean
Observations.foldr f e I =
  IdealCompletion.extend (PartialSpine.foldr ⊥ f e) I
```

The operation data and law hypotheses remain distinct. Tail monotonicity of
each step is sufficient for the following laws:

- Finite interpreted observations lie below the result, and any common upper
  bound lies above it.
- The fold is monotone and Scott continuous in the observation ideal.
- Principal ideals recover the finite fold; bottom, nil and ordinary finite
  List embeddings retain their expected values.
- Increasing the seed increases the result.

The semantic cons equation additionally requires Scott continuity of the
**selected head's** tail step. Other steps need only monotonicity. This
slightly strengthens the source's all-steps-continuous sufficient condition
without weakening the mathematical boundary. The proof uses principal
density and `continuous_ext`. Constructor folding is identity on every
observation ideal, including genuine infinite stream ideals.

Finite seed monotonicity and continuity are stated over a result preorder with
any fixed bottom *value*. Their proofs use the standard monotonicity and
continuity laws. Infinite seed continuity requires continuous tail steps and
uses the shared parameter theorem. Labels have no order or continuity
assumption.

For monotone algebras, a Scott-continuous observer `h`, bottom preservation
`h ⊥ = ⊥`, and the actual commuting equation, all-ideal fusion is:

```lean
h (Observations.foldr f e I) = Observations.foldr g (h e) I
```

The target seed is **`h e`**. The continuous-algebra variant is a specialization
through `.monotone`. `fusion_requires_strict` proves that all-ideal fusion
forces bottom preservation by choosing the bottom ideal; it needs neither
observer continuity nor an assumed commuting equation for this implication.

## Actual consumers and distinguishing cases

The retained client `truncate n` extends `principal ∘ cut n`. On the independent
stream ideal it is exactly the principal open prefix of length `n`. Applying
the existing guarded and paused observation equalities then proves the same
result for actual producers. The counting producer starting at four has
truncation `[4,5,6]` at budget three. `counting_truncations_and_costs` retains
the corresponding actual `Delivers` witnesses for arbitrary starts and
lengths: `n` guarded transitions and `2*n` paused transitions. In the concrete
case both reach seven, after three and six transitions respectively.

The Prop-valued consumer `first p` has tail-ignoring step `fun a _ => p a` and
seed `False`. It obtains `p 4` from either counting realization, `p a` from the
actual emit-once producer, and `False` from an always-silent producer. An
identity tail step with seed `True` separately distinguishes known nil from
the emit-once ideal's unknown tail.

The observer `fun P => P ∧ Q` is Scott continuous and strict for arbitrary
`Q`. `first_fusion` applies the public semantic fusion theorem, preserving
the transformed seed `False ∧ Q`. The guarded and paused combined consumers
then return `p (c s).1 ∧ Q` through that theorem and the actual producer
observation API.

Constant `True` supplies the adversarial observer. It is continuous and
commutes with the constant-True step, but does not preserve bottom. Fusion
fails at the bottom ideal, while the total finite embedding retains its weaker
fusion theorem. Neither successful finite fusion nor observer continuity is
used as a substitute for strictness.

Finally, `allCuts` extends `s ↦ fun n => principal (cut n s)` once into the
function-space CPO. Its function-valued `allCuts_isLUB` and
`allCuts_continuous` exercise the full Pi construction. `allCuts_apply` agrees
with every separately extended truncation, and its stream, guarded and paused
laws supply every prefix together. The checked zero and three budget cases
distinguish bottom from the known `[4,5,6]` prefix.

## Source correspondence and remaining work

The companion `adwh-directed-limits-provenance.tsv` maps exactly the approved
56 source declarations once each, including original statements and their
qualifications. Standard-owner and inline-hypothesis dispositions avoid
duplicating the source's basic order definitions. The distribution is:

| Canonical checkpoint-335 file | Rows adapted here | SHA-256 |
|---|---:|---|
| `LazyListDomain.lean` | 18 | `11c925f78d8814621e33e7cd1c82de4dee6df59c2b4cab674b8843da5e54fb46` |
| `InfiniteLists.lean` | 20 | `5d5853b8f4ac296ef87babe57f8b7748775b605900248bc765aeb55495cf07ba` |
| `InfiniteListFusion.lean` | 6 | `5361a0bafad1f966393222bb0ec0ee7d1aee15de123541c4899e14c467d3a4da` |
| `LazyListEvaluation.lean` | 12 | `4f6308bd80e6b10c58d2eb97dbccf40abb8e3b625e2f93b1d5288c6e277ad01c` |

The supplied archive SHA-256 is
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
Standard owners refer to the pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The operator developments build on these limits: [append](adwh-partial-append.md),
[concat](adwh-partial-concat.md), [scans](adwh-seeded-scans.md),
[left folds](adwh-partial-left-fold.md), [map](adwh-partial-map.md),
[takeWhile](adwh-partial-takewhile.md), [filter](adwh-partial-filter.md),
and [zip](adwh-partial-zip.md). Their separate source ledgers record coverage.
This is not a claim of whole-book completion or fresh textbook-page inspection.

Observation-ideal equality forgets timing and transition counts. These
noncomputable directed suprema do not establish native runtime, sharing,
physical memory, whole-language evaluation, recursive fixed-point semantics,
contextual equivalence, compiler adequacy or joint label refinement. An
exhausted finite search budget still does not establish divergence.
