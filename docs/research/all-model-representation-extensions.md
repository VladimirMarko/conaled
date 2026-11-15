# Checked all-model representation extensions

Adopt the bounded set-model construction for
[#291](https://github.com/VladimirMarko/conaled/issues/291). Product and quotient
sorts now expand every model in the [frozen contract](all-model-representation-fixture.md),
including infinite carriers. The implementation lifts every admitted forward
homomorphism, compares arbitrary presentations over their old models, reflects
old semantic consequence, and descends coherent dependent fibers and compatible
selected sections. These are Lean results. No syntactic-conservativity or
higher-groupoid strictification result is claimed.

The fixture was committed as `9465e45` before the reusable interface. The
selected consumer is the exact bounded parser decision family, with its existing
native trie denotation. Review clarified its nonemptiness obligation: a supplied
parser is needed, not just pointwise inhabitation of the language. The retained
instance uses the existing compiled `left` parser. This clarifies the adapter;
the arbitrary old model class and the exact witness contract are unchanged.

## Sources and inspected revisions

The local baseline was `2525b12052e4c85c57f9050dbf18f7a36ba2ef19`.
The [#287 comparison](representation-extension-comparison.md) and its
[fixture](representation-extension-comparison/fixture.md) supply the intended
mathematics, including the dependent and failure cases. That document was a
paper derivation; the declarations linked below provide the checked claims.

Barrett–Halvorson's [*Morita Equivalence*, arXiv:1506.04675v1,
§§2, 4.1–4.2](https://arxiv.org/html/1506.04675) assumes nonempty sorts. Its
Theorem 4.1 gives expansion unique up to isomorphism for a Morita extension;
Theorem 4.2 derives old semantic conservativity. Admissibility obligations
belong to the defining-sort axioms. Theorem 4.3 translates formulas using codes
for new-sort variables; those codes do not select representatives. The proof's
map discussion uses elementary embeddings and isomorphisms. Our forward
homomorphism lifting is proved separately for this fixture's atomic R and P.
We do not claim the paper's general formula-translation theorem in Lean.

Mathlib is pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679`, release
`v4.35.0`. Inspected primary implementation sources are
[`ModelTheory/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Basic.lean),
[`Syntax.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Syntax.lean), and
[`Semantics.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Semantics.lean).
Its language is single-sorted. The adapter therefore interprets the old language
on A ⊕ B with sort predicates; guarded quantifiers range over A or B. It reuses
Mathlib's formula syntax, satisfaction and isomorphism theorem. Quotients reuse
Lean/Mathlib `Setoid`, `Quotient.lift`, `Quotient.map`, `Quotient.sound` and
`Quotient.exact`, and the repository's
[`ObservationExtension`](../../SquareKit/ObservationExtension.lean) eliminator.

## Model construction and reusable certificates

[`Models.lean`](../../SquareKit/RepresentationExtension/Models.lean) fixes
`Model`: nonempty A and B, `Setoid A`, and unrestricted `A → Prop`.
`Hom` requires only forward preservation of R and P. There is no finiteness,
decidability, representative selection, or P-inhabitation assumption.

`ProductSort M` is the certificate for one presentation: a carrier and two
projections satisfying the unique-pair axiom. `QuotientSort M` is its quotient
counterpart: a carrier, q, the exact kernel equation, and surjectivity.
`ProductSort.canonical` and `QuotientSort.canonical` construct these certificates
for every M, using A × B and `Quotient M.relation`. Nonemptiness of both new
sorts follows from the old nonemptiness assumptions. These records do not ask
a caller to assume expansion, comparison, functoriality, or conservativity.
The module proves those results from the defining axioms.

`expandProduct` retains M as its reduct. `expandQuotient` accepts any
`ProductModel`, including a noncanonical C, and retains that entire stage.
`expand` composes them. `expandProductHom` and `expandQuotientHom` perform the
same stages on maps; the second retains the supplied product map.
`expandHom_id`, `expandHom_comp`, `liftHom_id` and `liftHom_comp` establish
the action laws. `ExtendedHom.ext` proves that the old map determines both
new components; `liftHom` supplies that extension for every admitted old map.

`comparison` fixes A and B and maps an arbitrary final presentation to the
canonical expansion of its reduct. `comparison_bijective` proves both new
components bijective. `comparisonInverse` and both inverse equations establish
an actual isomorphism over the old model. `comparison_natural` proves its
naturality for the admitted maps. Uniqueness follows from `ExtendedHom.ext`.
The reversed-coordinate product and singleton quotient in `alternate` exercise
a presentation that is not definitionally the canonical one.

The comparison and fiber inverses use `Equiv.ofBijective`, hence classical
choice in their Lean implementation. Forward quotient elimination and selected
section descent use `Quotient.lift`. No construction exposes an arbitrary
representative selector A/R → A, and no claim of choice-free Lean dependencies
is made.

## Old formulas and consequence

[`Logic.lean`](../../SquareKit/RepresentationExtension/Logic.lean) interprets
the tagged relational language with equality using Mathlib. `realize_allA`
and `realize_allB` check that the guards give precisely the original two
quantifier domains. `typedAssignment` retains the sort of each free variable.
The adapter permits more tagged formulas than the well-sorted source fragment;
all old well-sorted atomic formulas, Boolean combinations and guarded
quantifiers lie within this language. It does not restrict observations to
recognition, atomic formulas, or a selected finite list.

`consequence_iff` quantifies over every formula, premise set, old model and
assignment, and over every extended model satisfying the two sort certificates.
`typed_consequence_iff` gives the same result with fixed free-variable sorts.
Reflection instantiates the extended hypothesis at `expand M` for arbitrary M;
preservation takes the reduct of an arbitrary extended model. Old satisfaction
uses the unchanged old carrier and structure, so its recovery equation is
definitional. The existence of an expansion for every M is the nontrivial
premise supplied by the constructions. `countermodel_expands` retains the
actual falsifying assignment.

`realize_oldEquiv` uses Mathlib's full formula-invariance theorem, with predicate
and relation reflection supplied by the old isomorphism. The
`forward_not_preserved` example admits a forward map from empty P to universal P
and shows that an old negated formula changes truth. No full-formula preservation
is inferred for such maps. `bad_implies_existsP` and
`existsP_not_old_consequence` show why adding c with P(c) fails the all-model
condition. No calculus, completeness bridge or selected proof-tree inverse is
implemented or inferred.

## Dependent descent and selected values

[`Descent.lean`](../../SquareKit/RepresentationExtension/Descent.lean) constructs
the quotient of dependent pairs `(a,e)` by coherent transport. `DescentData`
supplies fiber equivalences for related pairs, their identity law and their
composition law. Proof irrelevance makes the transport independent of the proof
of R; this is a thin equivalence-relation groupoid, not a higher identity type.
Fibers may be empty.

`totalSetoid` proves the induced relation on dependent pairs is an equivalence.
`base` maps its quotient to A/R. `fiberEquiv` proves each original E(a)
equivalent to the fiber of `base` over [a], using proved injectivity and
surjectivity. `fiberEquiv_transport` checks compatibility of these comparisons.
`descend` constructs a quotient section from an equivariant chosen section;
`recover` returns its original selected value through the fiber equivalence.
`section_descends_iff` proves necessity as well as sufficiency, with explicit
pullback equations. Its conclusion is exact recovery relative to the supplied
transport, not existence of some unrelated section.

The checked three-point instance has classes {0,1} and {2}. Its fiber over a
consists of indices in `Fin 2`, restricted to index zero when a = 2. Transport
preserves the index. `two_values` and `singleton_fiber` expose the different
fiber sizes. `zero_recovered` uses the general recovery theorem to retain the
selected zero index. The universal Bool relation with identity transport
rejects the section `a ↦ a`; `no_selected_descent` derives the obstruction
through `section_descends_iff`. The separate symmetry test rejects an
equivariant representative selector while `noncanonical_section` constructs
a section choosing false.

## Direct construction versus certificate use

Both routes have the same all-model contract. Direct parameterization over M
already gives an all-model result; a certificate does not strengthen that
quantifier. The concrete recipes are shared rather than duplicated.

| Obligation | Direct parameterized route | Certificate client |
| --- | --- | --- |
| Model admission | Supply nonempty A and B, equivalence R, and P. | Supply the same `Model`. |
| Canonical sort construction | Use A × B and A/R and prove their defining equations. | Reuse the proved `canonical` recipes. |
| Alternate presentation | Prove the product unique-pair or quotient kernel/surjectivity axioms, then construct comparison maps. | Supply those same defining axioms once; reuse comparisons, inverse laws and naturality. |
| Forward maps | Prove R/P preservation, coordinate squares, quotient well-definedness and composition. | Supply the same old `Hom`; reuse `liftHom` and its laws. |
| Exact observer | Prove that related inputs have equal output. | Supply the same compatibility proof to `QuotientSort.observe`; recover through `observe_q`. |
| Dependent chosen section | Supply coherent fiber equivalences and selected-value equivariance. | Supply exactly the same data to `DescentData.descend`; the sort certificate cannot remove it. |

[`Examples/RepresentationExtension.lean`](../../Examples/RepresentationExtension.lean)
instantiates A as the existing ambiguous parser type, B as `PUnit`, R as exact
bounded decision agreement, and P as true. The supplied `left` parser proves
A nonempty. `Parsing.recovered` works for any quotient presentation;
`Parsing.direct_agrees` equates it to the direct parameterized eliminator on
identical inputs. `recovered_trie` connects that public result to native
`WitnessTrie.unfold` and `lookup`, using the existing `lookup_unfold` theorem.
The left and right epsilon decisions remain different, including their selected
sum witnesses. Their quotient images are proved distinct. The existing
recognition-only no-factor theorem is retained as the rejection case.

This exact observation setoid is an adapter defined here from the existing
bounded decision contract. The prior parser module supplies native parser/trie
semantics, not a ready-made two-sorted first-order structure. B, P, inhabitation
and the setoid are explicit remaining client adapters. The parser does not
exercise the general varying-fiber construction; the separate dependent case
does. No frontend conversion or AST migration is required for this client.

## Example-driven development and statement review

The frozen expectations preceded the interface: opposite selected epsilon
witnesses must remain distinct; the empty-P model must fail the bad extension;
zero-index dependent selection must recover; representative-sensitive selection
must fail. Initial gaps were missing connections from the native exact parser
contract to an all-model quotient result and from coherent fibers to an actual
quotient family. The work added those constructions and then used their public
theorems in the retained cases. Elaboration corrections during implementation
were not mathematical counterexamples.

Statement review checked the new definitions and theorem families against the
fixture. Product existence and uniqueness and quotient kernel and surjectivity
are defining axioms, not assumed all-model conclusions. Map quantifiers admit
noninjective maps and only forward R/P preservation. Semantic consequence
quantifies over arbitrary old and extended models, including assignments and
all formulas; typed free assignments are preserved. Dependent descent uses
identity and composition and recovers the specified section through its fiber
comparison. No fiber inhabitation is assumed globally. The negative controls
are inhabited models, so their failures are not vacuous. Helpers inherit these
cases; comparison is also exercised by `alternate`, composition by the infinite
natural-number model (3 becomes 8 after increment then doubling), and both
old-sort quantifiers by `bothSorts_valid`.

## Decision, costs and remaining work

Adopt these bounded certificates and their public observer/descent results for
set-model representation extensions. Keep direct native parser callers: they
pay no new syntax cost. Investigate general defining formulas only when a
consumer needs them, because forward homomorphisms may not preserve their
truth. Defer a reusable many-sorted frontend, general Morita library, new-sort
formula-code translation, and calculus bridge to #235/#288 if a concrete task
requires them. Reject unconditional natural representative selection and
unconditional selected-section descent: the retained controls refute both.

The implementation costs are a tagged-carrier first-order adapter, a pair of
small defining-sort certificates, proved map/comparison machinery and the
separate dependent quotient construction. A noncanonical presentation still
must prove its defining axioms. Repeated observer clients provide compatibility;
repeated dependent clients provide coherence and equivariance. These obligations
are mathematically necessary. This experiment measures no human or agent
author-effort improvement and makes no productivity claim.

#235 owns future certificate/general-formula integration, #288 the extension
programme, and #262 any bridge to the existing type-interpretation APIs.
Dependent higher-identity work remains with #107/#292 and must retain its own
identity contract. None of that work is resumed or claimed complete here.
The source-paper dependent coherence alternatives remain applicability questions
as recorded in #287; this thin set descent theorem does not discharge their
hypotheses.

Validation uses the README's focused module build followed by committed-candidate
`./check.sh --candidate HEAD` and `./check.sh --verify-candidate HEAD`, including
public-entrypoint coverage and exhaustive proof audit. The exact candidate and
results are recorded in the review handoff; independent Standards and Spec
review belongs to the coordinating implementation loop.
