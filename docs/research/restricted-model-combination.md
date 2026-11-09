# Constructing models from compatible components

For [#431](https://github.com/VladimirMarko/conaled/issues/431), **investigate a
bounded implementation of signature-union amalgamation**. Two independently
supplied algebraic models can be combined when their signatures overlap only
in a declared common signature and their common reducts come with an
isomorphism. The construction below retains both components and interprets
mixed terms. It does not discover the overlap isomorphism or establish new
interaction axioms between the components.

This is a paper construction and research assessment, not a new Lean result.
Local source inspection is at `5d3f1f610fc9bf601deb321f1a6fa83be94e1348`, with
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Primary sources were inspected on 2026-11-09. No performance or author-effort
measurement, universal synthesizer, implementation commitment, or required
adapter to the current architecture follows from this report.

## Primary-source approaches

**Signature amalgamation.** Schröder, Mossakowski, Tarlecki, Klin and Hoffman,
[*Amalgamation in the Semantics of CASL*](https://www.cs.ox.ac.uk/people/bartek.klin/papers/tcs05.pdf),
§2, pp. 7–8 of the author-hosted PDF, defines the required property: the
contravariant model functor sends a signature pushout to a pullback of model
categories. Models whose reducts are literally equal have a unique amalgam;
compatible model morphisms amalgamate too. This is an additional property,
not a consequence of the institution satisfaction law. The introduction names
many-sorted equational and first-order logic as positive cases. Section 5,
Example 4, explains failure for CASL subsorts: implicitly imposed equalities
between composed injections can conflict after union. Thus this report excludes
implicit coercions and unnamed sharing. The property concerns combination
across signatures, not embedding two models of one theory into a larger model.

Diaconescu and Stefaneas,
[*Ultraproducts and possible worlds semantics in institutions*](https://www.imar.ro/~diacon/PDF/ks_tcs.pdf),
§2.3 Example 1 and §2.5 Definition 5/Example 5, provides another explicit
first-order formulation. Sorts, finitary functions and predicates are named;
their FOL convention supplies a constant per sort to exclude empty carriers.
Signature maps preserve arities, reducts restrict interpretations, and signature
pushouts admit unique model amalgamation. We use the narrower total equational
fragment below and do not import their modal construction or ultraproducts.

**Sheaf gluing.** The Stacks Project,
[§6.33, Lemmas 6.33.2–6.33.4](https://stacks.math.columbia.edu/tag/00AK),
requires a topological space, a set-indexed open cover, local sheaves and
overlap isomorphisms satisfying the triple cocycle equation. Compatible tuples
of sections, restricted componentwise, construct the global sheaf. Restriction
is an equivalence of categories, giving recovery up to specified isomorphism.
Lemma 6.33.3 extends this to listed algebraic structures. Unlike signature
union, this assembles spatially local models. For the proposed application we
would fix a universe containing the space, cover and section sets, closed
under the required products and equalizers, raising the universe if needed.

## Restricted construction and exact hypotheses

The following derivation spells out the first approach for a class small
enough to formalize independently of a general institution library.

Let `Σ0 → ΣL` and `Σ0 → ΣR` be literal inclusions of finite many-sorted,
finitary, total-operation signatures. Every sort has a named constant.
The intersections of their sort and operation names are exactly `Σ0`, with
identical arities there. Private names are disjoint; there are no implicit
coercions, dependent sorts, partial operations or higher identity operations.
Let `T0`, `TL`, `TR` be sets of universally quantified equations in their
respective signatures, with both side theories containing `T0`. The combined
theory is precisely the union of the translated side axioms over
`Σ = ΣL ∪ ΣR`; it contains no additional mixed axioms. Infinite carriers are
allowed. Put signatures, axiom sets and carriers in a fixed set universe; the
collection of all such models may live in a larger universe.

Inputs are actual models `L ⊨ TL`, `R ⊨ TR` and an actual isomorphism
`e : L|Σ0 ≅ R|Σ0`: an invertible function `e_s` for every common sort,
preserving each common operation, including constants. The inverse functions
and their inverse equations are supplied data. No solver, existence oracle,
or equality of the two carrier types is an input.

Construct a normalized right model `Rᵉ` as follows. On common sorts use L's
carriers; on private right sorts use R's. Let `j_s` from these carriers to R's
be `e_s` on common sorts and identity on private sorts. For every right
operation `f : s₁ … sₙ → t`, define

```text
fᵉ(x₁,…,xₙ) = j_t⁻¹(fᴿ(j_s₁(x₁),…,j_sₙ(xₙ))).
```

For common operations this equals L's interpretation by the supplied
isomorphism law. An induction on right terms proves
`j_t(eval_Rᵉ(t,ρ)) = eval_R(t,jρ)`. Every right equation therefore holds in
`Rᵉ`, using injectivity of its result-sort `j_t`. This is a derivation from
component laws, not a hypothesis saying that the desired amalgam already
exists. The induction includes open terms and arbitrary well-sorted valuations.

Now define C on each left sort and operation by L, and on each private right
sort and operation by `Rᵉ`. Common declarations coincide, so this defines every
operation unambiguously. Left terms evaluate exactly as in L, and right terms
as in `Rᵉ`; hence `C ⊨ TL ∪ TR`. Every mixed term also has a total recursive
evaluation because every operation has an interpretation, although its value
need not satisfy any new mixed equation.

The left reduct is literally L in this chosen presentation; the right reduct
is isomorphic to R through j. Once the carriers, e and these identifications
are fixed, all operations of C are forced. A second such presentation has a
unique isomorphism commuting with the specified component identifications.
This is uniqueness **over the supplied data**. It asserts neither equality of
arbitrary record encodings nor uniqueness when the overlap isomorphism is
forgotten. If both reducts already coincide, no normalization is needed and
the union has strict uniqueness of operation interpretations.

Compatible component homomorphisms also combine: their common-sort maps must
satisfy `e' ∘ hL = hR ∘ e`; use hL on left sorts and hR on private right
sorts. Substitution into the displayed conjugation formula proves preservation
of right operations. Identity and composition follow componentwise. This
paper argument covers total equational homomorphisms, not preservation of
arbitrary first-order formulas by forward maps.

## Positive example: action plus observation

Take `T0` to have one sort X and a selected point `x0`. The left extension
adds a sort M, monoid operations and unit, and an action `act : M × X → X`
with precisely these action laws:

```text
act(1,x) = x
act(m*n,x) = act(m,act(n,x)).
```

The right extension adds a sort D, a selected element `d0`, and an arbitrary
observation `o : X → D`. There are no observation axioms. D's constant makes
the nonempty-sort convention explicit; it need not equal `o(x0)`.

Supply the left model `(M,X,x0,act)` independently of the right model
`(Y,y0,D,d0,o)`. The overlap input is a pointed bijection
`e : X ≃ Y`, with `e(x0)=y0`. The result retains M, X, x0 and act, retains
D and d0, and **derives** `out(x)=o(e(x))`. Its right reduct recovers the
supplied observer via e. A newly available mixed expression is
`out(act(m,x))`. From the action law and function congruence we derive

```text
out(act(m*n,x)) = out(act(m,act(n,x))).
```

The action law is proved once in the left component; each new observer needs
only its pointed overlap identification. No action-law proof is repeated for
the combined model or its observer. This is a bounded proof-obligation saving,
not an empirical productivity claim. Direct function composition obtains the
same saving for this particular example; a general amalgamation lemma would
extend it to independently presented operations and their equations.

For a concrete inhabited case, let M and X be Booleans, multiplication and
action be XOR, and the unit and x0 be false. Let Y be `Fin 2`, y0 be 0,
D be Booleans, d0 be false, and `o(0)=false`, `o(1)=true`. Supply the explicit
bijection `e(false)=0`, `e(true)=1`, with its inverse. The constructed output
after acting by true on x0 is true; acting by true twice yields false. These
are paper calculations of the defined functions, not Lean checks or runtime
measurements. XOR's associativity and unit laws supply the left obligations.

Equality here is set equality, and the selected observation is the exact
Boolean output. Distinct representations X and Y are permitted. Nothing
requires storing proof objects of the action laws or retaining every possible
observation. If a different client specifies a quotient observation or
non-set identity, it needs its own preservation contract; this construction
does not impose host equality on that client or establish its combination.

## Rejecting cases and logical boundaries

**Incompatible overlap.** Keep the same two signatures. Supply a left model
with singleton X, its sole point and any trivial monoid action, and a right
model with two-element Y and any observer. Both models satisfy their side
theories, but there is no bijection X ≃ Y. If C recovered both reducts up to
isomorphism, composing their carrier isomorphisms would give such a bijection,
a contradiction. Pairing carriers or forgetting one state changes the recovery
contract. Independent satisfiability of the two theories is insufficient for
combining these supplied models.

**Missing interaction law.** The positive Boolean/`Fin 2` example has a valid
overlap and an actual combined model. It refutes the extra mixed axiom
`∀m x, out(act(m,x)) = out(x)`: use `m=true`, `x=false`. Thus no combined model
recovering these components and this overlap can also satisfy that axiom.
This control prevents treating signature union as automatic synthesis of
invariant observations, ordered monoids, compatible smooth structures or cost
laws. An invariant-observer variant would require exactly the extra invariance
proof; it cannot be obtained by renaming the same inputs.

**Semantic versus syntactic claims.** The construction is conditional on
supplied compatible models. It is not an all-model expansion theorem for
arbitrary side theories: one side may impose a new equation on common
operations that the other model violates. Semantic conservativity needs an
expansion for every old model, as the existing extension work explicitly
proves. Syntactic conservativity additionally concerns a specified calculus
and its proof relation; no completeness bridge is supplied here. Interpreting
a source derivation in C is another step requiring a sound interpretation of
its fragment. Constructing C alone does not translate proof objects, recover
chosen witnesses from existential truth, or automate requirement discovery.

## Construction, choice and existence

| Input and output | What this report establishes |
|---|---|
| Explicit component operations, e and inverse | The formulas construct C directly. For effective finite signatures and computable operations/maps, evaluation remains computable. No search for a model or representative is used. |
| Arbitrary set-valued operations | A mathematical function defines C; computability of its inputs is not inferred. A prospective Lean definition can be noncomputable when supplied operations are. |
| Only `∃ e, compatible e` in a proposition | One can prove existence of C without selecting an executable e. Extracting a chosen e using classical choice gives a noncomputable construction in Lean, unless stronger effective data are provided. |
| Sheaf gluing inputs | The explicit tuple construction need not be executable for arbitrary infinite section sets; it does not select a local chart. |

For the finite example, both directions of e and all operations are explicit.
Neither the existence of a bijection nor a generic theorem asserting an amalgam
is used as a substitute for the construction.

## Delta from current repository capabilities

| Existing route | Inspected evidence | What the proposed construction adds or does differently |
|---|---|---|
| All-model representation extension | [`Models.lean`](../../SquareKit/RepresentationExtension/Models.lean), `expand`, `liftHom`, `comparison`; [implementation record](all-model-representation-extensions.md) | Existing code constructs product and quotient sorts for every admitted old model and compares presentations. Here the additional operations are independent input data, generally not determined by the reduct. Union preserves them rather than selecting canonical products or quotients. |
| Dependent descent | [`Descent.lean`](../../SquareKit/RepresentationExtension/Descent.lean), `DescentData`, `fiberEquiv`, `section_descends_iff` | Existing code constructs a family over a set quotient from coherent fiber equivalences, with selected-section equivariance as a separate obligation. Signature union neither quotients the shared carrier nor supplies that coherence. Sheaf gluing changes the base-overlap geometry; it is not a replacement for this checked thin-relation result. |
| Institutions and compatible squares | [`Capabilities.lean`](../../SquareKit/Institutions/Capabilities.lean), `Setting`, `Connection`, `Compatible` | These checked interfaces take model types and reduct functions as inputs; `Compatible` combines proof and realization maps for an existing connection. They do not compute a joint model from two reducts. A signature-indexed category and amalgamation property would be additional structure. |
| Synchronized realizations | [`Combinators.lean`](../../SquareKit/Combinators.lean), `synchronized`, `synchronize` | This already constructs pairs agreeing under decoders and preserves their agreement. It is an actual construction, but its pullback is of representation values over a common meaning, not models of a union signature. It need not recover each entire representation by an isomorphism. |
| Theory networks | [#294 comparison](theory-network-comparison.md), especially model reducts and total views | That paper work composes interpretations of a supplied target model and retains a selected solution. The present proposal constructs the target model from two compatible inputs first. A network could publish the union and its inclusions, but view composition alone does not prove amalgamation. |
| Direct native interface | Monoid action plus `out := o ∘ e` | The same construction needs no theory syntax or institution adapter. Reuse existing `Monoid`/action interfaces in a future Lean case. A signature-level version earns its cost only by absorbing repeated transport and axiom-preservation proofs across additional components. |

The local claims above are source-inspected existing declarations, not freshly
rebuilt results. The proposal does not replace these interfaces or conflict
with ADRs [0001](../adr/0001-modules-and-proof-dependencies.md),
[0002](../adr/0002-relations-and-synchronization.md) or
[0010](../adr/0010-composition-and-proof-audit.md).

## Assessment and bounded next step

**Investigate** a native action/observation formalization before a generic
signature library. Its acceptance target would construct the combined model,
prove both reduct recovery equations, derive the mixed action observation law,
and reject the singleton/two-element overlap and false invariance axiom through
the same public contract. Keep e and its inverse as explicit data; retain the
different carrier representations. Then test a second independent operation
component before deciding whether generic signatures reduce repeated work.
No first-order parser, proof frontend, mandatory certificate layer or universal
model framework is part of that target.

**Defer** choosing native records versus a signature-indexed implementation
until those two uses expose their actual obligations. An institution adapter
may document integration later, but is not an admission requirement. This
assessment adopts the bounded mathematical possibility, not a repository-wide
architecture. #288 owns the proposed construction follow-up; #290 owns any
theory-publication route; #235 coordinates interface decisions and review.
Those owners are existing umbrellas, not newly scheduled implementation work.

**Preserve sheaf gluing as an alternative that changes the question.** Its
target is a global model from spatially local models with transition maps,
rather than independent operation packages on a common carrier. Investigate
it when a concrete geometric client supplies a cover, local models and cocycle
data whose global reconstruction is not already handled by existing descent.
#288 and #36 should scope that client, coordinated with #32 for geometry.
It is deferred here because the positive example has no spatial locality,
not because it lacks an adapter to the current interfaces.

**Reject** unconditional combination of arbitrary supplied models or automatic
generation of mixed laws. The controls above refute those guarantees. Preserve
overlap discovery as a distinct research question: revisit it when a restricted
class provides an effective matching procedure, or when a client explicitly
accepts weaker relational recovery instead of isomorphic reduct recovery.
#235/#288 should discuss that changed contract before its adoption; independent
research into it need not wait for an incumbent consumer.

Statement review of the paper argument checked the quantifier order (given
L, R and e, construct C), the open-term induction, nonempty positive inputs,
uniqueness relative to supplied identifications, and the recovery contract in
both rejecting cases. No Lean declarations or tooling changed. Validation is
documentation-level link, fence and whitespace checking; no full build is
required. Independent Standards and Spec review remains with the coordinating
implementation workflow.
