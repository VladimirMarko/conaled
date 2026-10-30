# Transporting reachable left-fold fusion

Research for [#248](https://github.com/VladimirMarko/conaled/issues/248),
Implementation follow-up: [#252 is implemented](recursive-fusion-implementation.md)
with checked types and nonconstant-presheaf applications. The assessment below
records the original design and its scope.

2026-10-30. Audited repository revision
`b564720cac0033a7beea65828c7a616f2f0f4407`; Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean 4.35.0.

The next experiment should derive reachable left-fold fusion from an initial
list algebra and exponential objects, then specialize the **same categorical
proof** to types and a nonconstant presheaf. This is a proposed mathematical
construction, not a checked implementation. It needs no unrestricted fixed
point and no general recursive proof language. The construction below gives a
bounded implementation specification; #109 retains compiler recursion scope.

## The selected argument and its current clients

The exact test is [ListFusion.foldl_reachable](../../SquareKit/ListFusion.lean):

```text
P e
∀ r a, P r → P (f r a)
∀ r a, P r → h (f r a) = g (h r) a
────────────────────────────────────────────────────
h (foldl f e xs) = foldl g (h e) xs
```

Here `A`, `R`, `S` are arbitrary types, `f : R → A → R`, `g : S → A → S`,
`h : R → S`, and `P : R → Prop`. No monoid, injectivity, decidable predicate,
commutativity or inverse to `h` is required. The existing proof inducts on `xs`
while generalizing `e`; the induction hypothesis is applied to `f e a`, with
its validity supplied by closure. Generalizing the accumulator is essential.

[OrderedSummary.batch_summary](../../Applications/Sequences/OrderedSummary.lean)
uses `h r = summary measure (decode r)` and
`g m a = m * measure a`. Representation validity is `P`; push closure and
`decode (push r a) = decode r ++ [a]` discharge the local square using
`summary_append` and `summary_singleton`. `batch_decode` uses the same fusion
with full sequence observation, then a separate append-fold identity.
[List and DList clients](../../Examples/OrderedSummary.lean) use these ordinary
interfaces. The proposed experiment recovers `batch_summary`; it does not
quietly include transport of `batch_decode`'s second induction or all cache laws.

Cache validity in that module has a dependent premise:
`Inv r ∧ cached = summary measure (decode r)`. `append_valid` preserves it
using local monoid/observation laws. That theorem itself is not the selected
recursive argument. A valid-state subtype can contain this invariant without
requiring a canonical witness beyond the supplied proof. Full sequence meaning
and equality of its lossy summary remain separate.

[#185's presheaf example](../../Examples/OrderedSummaryPresheaf.lean) transports
existential reassociation; its list induction stays outside the interpreted
argument. [#218's compiler](../../SquareKit/ListFoldCompiler.lean) already has
finite fold/post syntax, target operations, soundness, and compiled fusion.
Its `Sound.fold` equation denotes into host `List`, and `fold_fusion` calls the
selected host theorem. This is useful compiler reuse, but not yet reuse of a
recursive argument inside the presheaf category. The
[implementation record](recursive-compilation.md) explicitly keeps partial
recursion and richer indexed traversal open.

## Three routes and their obligations

| Route | Reusable argument | Caller and model obligations | Assessment for this test |
|---|---|---|---|
| Existing List/FreeMonoid APIs | Host `foldl_reachable`; monoid homomorphism extension | Supply `P`, closure and the local square; ordinary monoid laws for summaries | Keep as the concrete interface. Changing types or monoids alone does not meet the cross-setting test. |
| Operation-and-law adapter over Type | Package state, observation, push and closure; invoke existing fusion | The same local laws, possibly hidden by an adapter | Useful specialization. Merely adding a model parameter around host lists does not reinterpret recursion or equality. |
| Initial list algebra in a category, with exponentials | Derive fusion once by algebra homomorphisms and initiality | Construct list initiality, needed exponentials, valid-state object and commuting arrows | Recommended bounded experiment. Model construction is explicit, and the complete fusion conclusion is never a primitive. |

Mathlib supplies [endofunctor algebras and their morphisms][algebra], including
`CategoryTheory.Endofunctor.Algebra`, and `Limits.IsInitial` supplies uniqueness
of outgoing algebra morphisms. [FreeMonoid.lift][free] already supplies ordered
monoid extension and `comp_lift`; replacing that API would add no capability.
Mathlib also constructs [closed functor categories][closed] through enriched
homs under suitable limits. These are source-verified ingredients, not a claim
that their instances already elaborate together into the proposed list theorem.

Ghani, Johann and Fumex's [*Generic Fibrational Induction*][gfi], Definition 4.7
and Theorem 4.11, identify a larger route: a comprehension category with unit,
an initial algebra and a truth-preserving lifting yield sound induction.
Section 4.3 adds hypotheses for constructing such liftings. This addresses the
real obligation of interpreting predicates and dependent induction; changing a
functor parameter alone does not supply those hypotheses. For this equality
fusion test, iteration uniqueness and a valid-state object suffice, so building
the general fibrational framework first would add unneeded obligations. Revisit
it when a consumer needs dependent proof data or a different predicate category.
This recommendation is based on the selected claim, not a judgment about an
author's programme.

## Candidate theorem and the recursive argument

Let `C` be a category with finite products, binary coproducts, and the
exponentials used below. For an object `A`, require an initial algebra `L A`
for `F_A X = 1 + A × X`, with `nil` and `cons`. Cartesian closure is a convenient
initial implementation interface; only the specified exponentials are used.
Keep that distinction visible if a later target lacks general closure.

Represent the invariant by a mono `i : I → R`. Supply
`fI : I × A → I` factoring the original step `f : R × A → R`:
`i ∘ fI = f ∘ (i × id_A)`. Set `hI = h ∘ i`, and require

```text
hI ∘ fI = g ∘ (hI × id_A).
```

A seed is a map `e : 1 → I`; the theorem also holds for arbitrary generalized
seeds because it is an equality of arrows on `L A × I`. For the mathematical
fusion core one can supply `I`, `fI`, and `hI` directly; the mono and factorization
are needed to recover the original reachable-state statement without asserting
the square on invalid `R` states.

Construct a left-fold action `run_f : L A × I → I` from the initial list
algebra into the exponential `I^I`. Its algebra has empty value `id_I` and
cons operation `a,k ↦ k ∘ f_a`, where `f_a(s) = fI(s,a)`. This is internal
lambda notation for arrows built from evaluation, currying and composition,
not an assumption that global elements determine all arrows. Uncurrying its
unique fold gives `run_f`. Similarly construct `run_g : L A × S → S`.
The candidate conclusion is

```text
hI ∘ run_f = run_g ∘ (id_(L A) × hI).
```

Here is the proof to implement once for `C`:

1. Give `S^I` the list algebra with empty value `hI` and cons action
   `a,k ↦ k ∘ f_a`.
2. Postcomposition with `hI` is an algebra morphism `I^I → S^I`.
   The cons square is associativity of composition.
3. Precomposition with `hI` is an algebra morphism `S^S → S^I`.
   Its cons square is `k ∘ g_a ∘ hI = k ∘ hI ∘ f_a`, using the local square.
4. Both composites from the initial list algebra into `S^I` are algebra
   morphisms. Initiality makes them equal. Uncurry that equality to obtain
   the conclusion; specialize the seed and then forget `I` to recover the
   ordinary theorem. Apply this same categorical theorem to `i` and its step
   factorization to establish that forgetting the valid-state run equals the
   original `R` run; this bridge is a derived specialization, not a new premise.

This uses the universal property of recursion to derive the recursive result.
It does not assume fusion as a law of a model. For ordinary lists, the
corresponding induction expands to the existing generalized-accumulator proof.
The shared proof can be written directly with categorical arrows in Lean;
adding syntax for induction is unnecessary for this experiment. An eventual
internal-language presentation may hide those arrows without changing the
mathematical requirement.

## Two models, and what must be proved locally

**Types.** Take `I = {r // P r}`, lift the step using closure, and use ordinary
function spaces. Construct list initiality by structural recursion and prove
uniqueness by list induction. Show that the derived action is `List.foldl`,
then recover the existing theorem and `batch_summary` under their original
hypotheses. Equality is Lean equality of functions, used extensionally;
validity proofs are propositions. No choice of data from an existential proof
is needed. The valid accumulator and its image remain explicit values.

**Nonconstant presheaves.** Use the existing two-stage category, with a
restriction from fine sections to coarse sections. Let `A` have fine sections
`Nat × Bool`, coarse sections `Nat`, and restriction `Prod.fst`. Let `R` be
ordered sequences with an optional diagnostic cache, `I` its valid-cache
subfunctor, and `S` diagnostic summaries: fine `(length, ordered Bool word)`,
coarse `length`. Restriction forgets labels. Push appends one element and
updates the cache in order; `hI` observes the summary. The existing
`summaryMap`, `cacheMap`, stable cached relation and forgetting-label laws
supply examples of the required naturality, but the new single-element step,
its restriction law and factorization still need checking.

The list object has sections `List (A.obj j)` and restriction `List.map`.
For any natural list algebra, define its fold sectionwise. Prove its
naturality by list induction using the algebra's naturality; prove uniqueness
sectionwise. These establish initiality in the **functor category**, rather
than merely proving fusion separately at two stages. Apply the one categorical
fusion theorem there. Stagewise evaluation of the resulting arrow equality
recovers the concrete clients. Those model-construction proofs may use host
induction; the application fusion proof must not be duplicated in the model.

Exponentials are not pointwise function spaces. For diagrams `X_f → X_c`
and `Y_f → Y_c`, `(Y^X)_c` consists of functions `X_c → Y_c`, whereas
`(Y^X)_f` consists of pairs of functions `u_f`, `u_c` satisfying
`restrict_Y ∘ u_f = u_c ∘ restrict_X`. Restriction selects `u_c`.
This explicit walking-arrow description can discharge the model's exponential
obligations if the general Mathlib construction creates disproportionate
integration work. It is a specialization of the same universal property.

Predicates here are stable subfunctors. The cache invariant therefore needs
preservation along restriction; an arbitrary pair of stage predicates will not
do. Equality of natural transformations is componentwise extensional equality,
and all restrictions preserve it. Neither equality nor cache validity is
reflected through the lossy restriction. This experiment has no higher-identity
witness claim and no existential witness extraction interface.

Evaluation functors preserve the pointwise list object and its recursive
constructor structure, but must **not** be assumed to preserve exponentials:
the displayed fine-stage exponential already contradicts that shortcut.
Instantiate the categorical theorem in each setting, prove the actions'
component equations, and compare their ordinary outputs directly. A later
general functorial transport theorem would need specified list-initiality,
product and exponential comparison hypotheses; it is outside this experiment.

## Cases that discriminate the proposal

These are specified implementation cases, not newly checked Lean results.
Existing good/bad-cache and nonreflection cases are already checked in
[OrderedSummaryPresheaf](../../Examples/OrderedSummaryPresheaf.lean).

- Empty input returns the supplied valid seed in both models. A nonempty valid
  seed ensures the proof covers arbitrary accumulators, rather than only empty
  construction.
- Starting empty, `[(3,true),(3,true),(5,false)]` yields length three and word
  `[true,true,false]`; restriction yields `[3,3,5]` and length three. The
  repeated input retains multiplicity. Swapping the final two elements changes
  the fine word but leaves the coarse length unchanged.
- A fine cache for `[(3,true)]` storing word `[false]` is invalid although its
  coarse cache is valid. Existing `bad_fine` and `no_validity_reflection`
  prevent turning preservation into reflection.
- Keep sequence push as append but update the fine cached word by **prepending**
  the next label. From seed word `[true]`, appending `false` violates the local
  square: `[false,true] ≠ [true,false]`. Coarse length still agrees. Checking
  only the coarse model would miss the required fine preservation premise.
- Define a candidate observation whose fine value is sequence length but whose
  coarse value is constantly zero, with identity restriction on `Nat`.
  A singleton disproves naturality. Separate Set proofs at both stages do not
  make this a presheaf morphism; the shared theorem must reject that input.

## Lean feasibility, termination and ownership

The categorical proof above is a mathematical feasibility argument. The source
audit found the underlying algebra and closure constructions; no attempted
Lean encoding has established either an elaborator obstruction or its absence.
Likely integration obligations are universe alignment, selected products versus
pointwise products, exponential comparisons and subtype/subfunctor coercions.
Record actual diagnostics if they arise. Their presence alone would not show
that the mathematics is impossible or that a current worker's difficulty is
permanent. Follow the [agreed assessment criteria](../language-direction.md#elegance-author-capability-and-language-constraints).

Keep ordinary `batch_summary` clients syntax-free. A small helper can construct
the valid-state object and its step from `P` and closure, then export the same
fusion statement. Model authors supply initiality and exponential evidence;
ordinary authors supply the local observation laws they already know. Compare
those obligations and wrapper costs, not just proof line counts. #235 owns any
unresolved interface mismatch or future generalization; #249 owns recorded
author trials. This research itself is not an author-effectiveness trial.

Structural list recursion terminates because the input is finite. The existing
compiler terminates by recursion over its finite source syntax, independently
of runtime list length. Termination of target evaluation additionally depends
on executable primitive interpretations and their operational contract; a
categorical arrow or semantic equality does not establish runtime cost or
termination of an external backend. Elliott's [*Compiling to Categories*,
§12][ctc] identifies recursive inlining as a compiler nontermination concern
and proposes investigating a fixed-point interface. The finite initial-algebra
experiment does not solve that broader question.

The implementation follow-up should deliver the single theorem, the two model
instances, recovery of the ordinary summary client, and the listed positive
and missing-premise cases. It must show which proof is shared and which model
obligations remain, use checked examples and statement review, and pass the
applicable full build/proof audit plus independent Standards and Spec review.
Do not extend the compiler syntax, add general dependent induction, claim
arbitrary fixed points, or change existing clients' assumptions to make the
example fit. Publish the bounded follow-up under #109, coordinated with #174,
#200, #36 and #235; closing this research leaves that implementation outstanding.

[algebra]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Endofunctor/Algebra.lean
[free]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/FreeMonoid/Basic.lean
[closed]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Monoidal/Closed/FunctorCategory/Basic.lean
[gfi]: https://cs.appstate.edu/johannp/gfi.pdf
[ctc]: https://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf
