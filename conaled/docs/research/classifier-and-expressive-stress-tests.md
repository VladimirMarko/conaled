# Relative classifiers and expressive stress tests

Research note, 2026-10-25. This responds to the owner's request to establish the
full classifier contract and exercise richer mathematics early. The proposed
theorems and tests below are specifications, not new Lean results. They extend
the [composition contracts](composable-setting-contracts.md) and the checked
[presheaf representation](presheaf-setting.md).

## The next classifier theorem

The completed representation theorem classifies models over objects of one
presheaf category. The next theorem must quantify over geometric morphisms
from other toposes. It should retain the same finite presentation so that the
new difficulty is the categorical meaning of classification.

Fix a Grothendieck topos E, X in E and U ↪ X. Put B = E/X, write u ↪ 1B for
U as a subterminal of B, and put a = u ⊔ 1B. The underlying object of a in E
is A = U ⊔ X. Let π:B/a → B be the slice geometric morphism. The finite
geometric theory T(u) has propositional generators p,q and axioms

```text
⊤ ⊢ p ∨ q       p ∧ q ⊢ ⊥       p ⊢ u.
```

For every Grothendieck topos F and geometric morphism h:F→B, prove an
equivalence of categories

```text
Geom_B((F,h), (B/a,π)) ≃ Mod_F(T(h* u)).
```

The left side is a hom-category in the pseudo-slice: its objects include a
geometric morphism k:F→B/a and an invertible comparison πk ≅ h. Its arrows
are geometric transformations compatible with that comparison. Fix a
convention for the direction of inverse-image transformations throughout.
Deleting the comparison to h weakens the statement incorrectly.

A model on the right consists of complementary subterminals P,Q in F,
with P ≤ h*u. A model homomorphism preserves both designated predicates.
In this particular propositional theory these homomorphisms force equality:
P≤P′ and Q≤Q′, together with complementarity, imply P=P′ and Q=Q′.
Thus the model category is equivalent to a discrete category. Prove this
fact; do not use it to discard model morphisms for other theories.

The proof has two reusable parts. First show that these partitions correspond
to sections s:1F→h*a. Finite coproduct disjointness and stability give the
forward and reverse constructions without deciding membership in u. Then
prove the slice-topos universal property, including transformations. Given s,
the inverse image of the classified geometric morphism is

```text
B/a  --h* on slices-->  F/(h*a)  --pullback along s-->  F.
```

Construct its right adjoint and prove the adjunction and finite-limit
preservation. In a topos, the pullback functor along s has a dependent-product
right adjoint. Merely defining the displayed functor does not yet construct a
geometric morphism. Conversely, apply k* to the generic section and use the
comparison over B. Establish both inverse equivalences and their action on
transformations.

Slices are toposes, and their geometric inverse images are pullback functors;
these constructions are described in the Stacks Project's
[localization of topoi](https://stacks.math.columbia.edu/tag/04GY).
The equivalence above and its partition argument are our explicit proposed
specialization. They are not established by citing that section alone.

The generic section in B/a is the diagonal a→a×a over a. Pulling back the
two summand inclusions gives the actual generic predicates. The equivalence
must be identified with pullback of this generic model, not an independently
chosen model with the same cardinalities.

This is a full classifier theorem for T(u), with arbitrary source topoi in
the stated universe bounds. It is not a construction of the classifier of
every geometric theory. The abstract slice argument may admit elementary
toposes too; state that stronger result only after checking all adjunction
and size assumptions, rather than making Grothendieck hypotheses disappear
informally.

## Change of ambient base and iteration

For f:B′→B, form a′=f*u⊔1B′. Prove that

```text
B′/a′  →  B/a
  ↓         ↓
 B′    →    B
```

is a pseudopullback of geometric morphisms. Its comparison uses the canonical
coproduct isomorphism f*a ≅ a′. Track the generic model through that
comparison. Also prove pseudonaturality of the classifier equivalence under
precomposition F′→F, including geometric transformations, identity and
composition. Parameter substitution Y→X and ambient base change must agree
on their common mixed square.

These are the missing contracts behind the fixed-slice experiments. Vickers's
[*Arithmetic universes and classifying toposes*, Theorems 30–31](https://sjvickers.github.io/AUClTop.pdf)
proves classifier stability under pseudopullback for its context extensions
and packages it through local representability. Its base elementary toposes
have natural numbers objects. This is evidence for the required form of the
contract, not a checked implementation dependency.

Vickers's [*Generalized point-free spaces, pointwise*, §8.1](https://arxiv.org/pdf/2206.01113)
turns presentation data into parameters and adjoins a model of the resulting
relative theory. Sections 8.2–8.3 extend the account to sites and bipullbacks.
These constructions justify studying iterated internal formation, subject to
their geometric presentation and size conditions. They do not provide a
classifier for arbitrary dependent or higher type theories.

## Literature-backed test with nonidentity model morphisms

Use the theory of one unconstrained proposition, equivalently one subterminal
object. Johnstone's *Topos Theory* (1977), §4.3, p. 117, identifies the
Sierpiński topos over a base with the classifier for open objects, his term
here for subterminals. The calculation uses the walking-arrow category and
identifies its flat diagrams with the poset of subterminals.
See the [primary text, p. 117](https://pages.jh.edu/rrynasi1/NewFoundations4Math/Literature/Toposes/Johnstone1977ToposTheory.pdf).
This supplies a small established example with noninvertible model maps.

Our proposed acceptance theorem, for a Grothendieck base B and every
Grothendieck topos h:F→B within the stated size bounds, is

```text
Geom_B((F,h), (S_B,π)) ≃ Sub_F(1F).
```

Here S_B is the relative Sierpiński topos, presented by the arrow category
of B; its generic subterminal is the arrow (0B→1B), included in the
terminal arrow (1B→1B). The right side is a category whose arrows are
inclusions, not a discrete collection of subobjects. The equivalence must
send k to k* of that generic subterminal and act on every transformation.

Adopt the convention that a geometric transformation α:k⇒l has
inverse-image component α*:k*⇒l*. It then induces k*G→l*G, in the same
direction as a model homomorphism. Under the opposite convention for
geometric transformations, the hom-category in the displayed theorem must
be replaced by its opposite. Vickers's
[*Arithmetic universes and classifying toposes*, §5.2](https://sjvickers.github.io/AUClTop.pdf)
explicitly reconstructs a unique 2-cell from a model homomorphism, including
noninvertible homomorphisms; this is the required fullness and faithfulness
obligation. Reindexing reverses source geometric morphisms while preserving
the direction of their inverse-image transformations. Do not conflate these
two variance choices.

The first checked specialization should take B=F=Set. The two models
0↪1 and 1↪1 admit a noninvertible map from the former to the latter and
no map back. Construct the corresponding two points of S_Set and the
noninvertible geometric transformation between them; prove that the
classifier equivalence preserves its direction. This distinguishes the
intended category from both its discrete category and its maximal groupoid.
Also prove source pseudonaturality, identity/composition coherence and the
ambient-base pseudopullback comparison for S_B. These are proposed checks,
not existing Lean results.

This example still has thin hom-categories. If later interfaces depend on
that special property, follow it with the theory of one unconstrained sort,
whose models and homomorphisms are objects and arbitrary maps. Johnstone's
next example on p. 117 constructs the object classifier from finite sets.
That follow-up would test parallel maps; the Sierpiński example already
tests the immediate requirement of nonidentity, noninvertible maps. A small
internal site with nontrivial coverage is a separate test of site presentation.

## Existing richer semantics must be carried across the new routes

The narrowness of #118–#127 does not describe the whole repository.
[`GroupoidIdentity`](../../SquareKit/Internal/PathTransport/GroupoidIdentity.lean)
already represents identity by arrows, with endpoint conjugation and
substitution. [`Examples.GroupoidTransport`](../../Examples/GroupoidTransport.lean)
uses the one-object groupoid C₄: loop labels remain distinct under both a
faithful action and an ineffective action. Its module documentation points to
`Examples.AgdaTransferModels` for the complete transferred source argument.

These results should become fixtures for new interpretation and compilation
routes. A new C₂ example alone would repeat a distinction already checked.
What remains unestablished is that the new routes retain these distinctions,
and that the abstractions support the additional dependent and universe
structure proposed below. Nothing here selects or prepares #108's reserved
independent authoring test.

The [Hofmann–Streicher groupoid model](https://people.csail.mit.edu/jgross/personal-website/papers/academic-papers-local/agroupoidinterpretationoftypetheroy.pdf)
shows why nontrivial identity and transport must be retained: it refutes
universal uniqueness of identity proofs. An ordinary groupoid model still
does not test nontrivial identities between identity witnesses. Higher tests
need a richer semantic target.

## Small mathematics that can force design changes

The following are proposed acceptance examples. Each should have independently
stated expected observations, a checked source argument and comparisons through
at least two supported routes. Preserve a negative test for the information
that an intentionally forgetting route loses.

| Test | Observable contract | Failure would expose |
|---|---|---|
| Ambiguous parse of a fixed short word in a grammar with two derivations | A dependent pair retains the parse tree and its yield certificate. The two trees remain distinguishable after translation even though both prove the same membership proposition. Reuse the project's distinction between recognition and parse witnesses. | An existential/`Prop` intermediate representation erases computational evidence. The compilation-facing representation or semantic relation must change. |
| C₄ loop transport through the new routes | Retain the existing distinct loop labels and faithful action results; an ineffective action must not identify the base arrows. A quotient-to-components route must declare its loss of information. | Identity has been replaced by host equality or inferred from a chosen action that is not faithful. |
| A dependent family with nonconstant fibres | Use vectors indexed by length, dependent lookup, and reindexing under a noninjective map of contexts. Prove substitution for dependent sums, projections and a dependent eliminator, including a two-step comparison. | Telescopes support only constant fibres, or chosen pullbacks create coherence obligations that callers must solve repeatedly. |
| A dependent family over a groupoid | A two-element fibre over the walking automorphism with its nontrivial loop swapping the elements; compare transport and dependent pairs, then retain the distinction through a route. Combine this with the existing loop tests rather than counting action semantics alone as a new result. | Set-valued dependent families work only over discrete contexts, or context extension forgets how arrows act on fibres. |
| Nontrivial second identity | A small explicitly specified 2-groupoid with one object, one 1-arrow, and C₂ as the group of 2-automorphisms. Define the required identity fragment and its interpretation; prove the two 2-cells remain distinguishable. | A supposedly general identity interface has already imposed 1-truncation. This is a 2-dimensional test, not full HoTT or an automatic intensional type-theory model. |
| A universe of small dependent data | Codes for a bounded family of finite types, a decoding family, dependent-sum codes and substitution; then a second level containing the first code object. Prove decoding/substitution comparisons and state the level of every object. | An externally supplied Lean `Type` parameter was mistaken for an internal universe, closure fails under dependence, or the design requires `Type : Type`. |

For the vector test, include a context with n=0 and n=1, so the fibre
variation is checked rather than asserted. For the universe test, distinguish
codes from decoded objects and from the ambient collection of all models.
A finite-code universe demonstrates only its specified closure operations.
An internal universe intended to classify a broader class of small maps needs
its own generic-family and pullback theorem. Univalence is a separate demand;
it does not follow from having codes and decoding.

A useful first universe fixture is the groupoid Ufin whose objects are natural
numbers and whose arrows n→m are equivalences `Fin n ≃ Fin m`. Decode n as
`Fin n` and an arrow as its underlying bijection. The transposition at code 2
then changes a decoded element while leaving its code object fixed. A discrete
universe with codes n alone would miss this test. The decoding family is a
functor to sets; its category of elements supplies a generic family in this
bounded sense. Ufin is a groupoid described in the ambient metatheory, not an
element of its own decoding family.

For a finite base n and finite family b:`Fin n→Nat`, dependent sum and product
codes can be `Σ i, b i` and `∏ i, b i` as natural-number cardinalities.
The required decoding comparisons are bijections to the actual dependent
sum and product of the sets `Fin (b i)`. State and prove their naturality under
base and fibre bijections; cardinality equations alone discard the action
being tested. The empty base checks the empty sum and singleton product.
Chosen enumerations introduce coherence work, which is part of the fixture.
This tests finite dependent data and first identity structure together without
claiming a general universe of all types. A second code level containing Ufin
cannot itself decode only finite sets: Ufin has infinitely many objects and
nontrivial arrows. That required enlargement should be explicit, rather than
silently reusing the finite decoding family.

The source distinction between dependent pairs, propositional existence,
identity types and universes is documented in the primary
[*Homotopy Type Theory* book, Chapters 1–3](https://homotopytypetheory.org/book/).
The proposed fixtures above are project design tests, not claims extracted
from that book or already formalized here.

Dependent substitution requires deliberate coherence choices.
[Clairambault–Dybjer, §§3–6](https://arxiv.org/pdf/1112.3456)
explains the problem with arbitrary pullback choices and develops the
biequivalence using structured categories with families and pseudomorphisms.
Its extensional identity result must not be used as evidence for the higher
identity fixture. Prefer a small common substitution contract only where the
checked examples demonstrate it; keep the semantic assumptions of the
different routes visible.

## Decisions these experiments should inform

The full finite classifier and the richer tests can proceed independently.
Neither should wait for an existing application workstream to need them.
Their purpose is to expose representation constraints while interfaces can
still change.

The first design decisions are which judgments each route preserves, where
computational witnesses remain inspectable, how context extension and
substitution are represented, and whether a route intentionally truncates
identity data. A backend emitting ordinary Lean propositions may still host
an explicit model of richer identities; that does not turn them into Lean's
native equality. State which of those meanings the compilation theorem uses.

For the classifier, accept the finite result only when it covers arbitrary
source geometric morphisms, the actual generic model, model morphisms and
base-change coherence. For expressive tests, accept success only when their
distinguishing observations survive the route under study. Merely adding
syntax constructors, or proving a theorem after erasing the distinguishing
data, would miss the intended architectural test.

Validation for this note: inspected the cited local interfaces and primary
sources. No Lean definitions changed and no Lean build was run.

## Checked witness and vector fixture (#140)

[`Examples.ExpressiveWitnesses`](../../Examples/ExpressiveWitnesses.lean)
implements the first bounded witness and nonconstant-family tests. Its source
constructions are ordinary Lean data and sections of `DependentSquares`, not
new syntax for a general dependent compiler.

The grammar `(ε + true)(ε + true)` has two parses of `[true]`: the token is
consumed by the left or right operand. A `ParsedWord` dependent pair retains
the selected `Concat` tree, including its concatenation/yield certificate.
The direct route observes whether the left word is nonempty. The second route
uses `derivativeConcatIso` and observes the derivative's sum tag. The
`observation_preserved` theorem compares those independently defined
observations for every tree; `selected_roundtrip` recovers the entire selected
pair. Both concrete trees reduce to their expected distinct tags. The
`observation_does_not_factor` theorem proves that forgetting to `Nonempty`
prevents recovery of that distinction. This is transport of a selected parse,
not enumeration of every parse by the parser's decision procedure.

The vector source family is `Fin n → Bool`. The direct split-family route and
a length-certified list route interpret the same section, whose entry at
index `i` is true exactly when `i` is even. `compileSection` works for any
section of this family: `decode_encode` discharges the local semantic law,
then `TermCert.reindex`, `SubCert.compose`, `sectionCert`, `pCert` and `qCert`
supply transport and context extension. The fixture checks dependent sums,
both projections, dependent lookup/elimination, substitution along `n ↦ n/2`,
and composition with `n ↦ n+2`. Its output lists at lengths 0 and 1 are `[]`
and `[true]`; the two-step route at 0 also produces `[true]`. The empty fibre
has one vector and the singleton-index fibre has distinct true/false vectors;
`fibres_not_equivalent` rules out identifying those fibres.

Callers supply a family, a section, representation meaning functions and
commuting substitution certificates. List lookup requires `i : Fin n`; no
lookup at length 0 is available. The sum and extension rules come from the
existing split-family model. Its chosen reindexing computes strictly, while
`TermCert.reindex` handles the general equality transport. No sheaf route,
intensional identity rule, internal universe, arbitrary source elaboration,
or codata rule is established by this fixture. All displayed data routes are
computable; reduction examples are kernel proofs, not native-evaluation
axioms. The fixture introduces no foreign execution boundary.

The negative vector theorem concerns the particular constant `Unit` carrier
that erases every entry. It does not rule out constant encodings containing
tags or length data. To retain the tested contract a route must preserve
indexed lookup; for parses it must preserve the selected tree observation.
A full inverse, as in the parse isomorphism, is sufficient but stronger than
observation preservation. A proposition-only route remains useful for
membership, with that weaker contract stated explicitly. Neither fixture
changes #107's authoring regression or supplies #108's reserved theorem.

## Checked groupoid route fixture (#141)

[`Examples.GroupoidRoutes`](../../Examples/GroupoidRoutes.lean) reuses C₄ and
the existing generated source transport term. Its family has fibre `ZMod 2`;
a label acts by addition of its parity. Label 1 exchanges 0 and 1, while
label 2 acts trivially. The base labels remain distinct. `not_constant`
proves that this family is not naturally isomorphic to the constant
two-element family, and `swapPair` is an arrow between dependent pairs
retaining the base label that moves their fibre values.

[`GroupoidTransportRoutes`](../../SquareKit/GroupoidTransportRoutes.lean)
packages a base functor and a natural map of fibres. The route's transport
comparison follows from naturality. Identity, composition and reindexing use
Mathlib functors and natural transformations; their laws and arrow/fibre
comparisons are checked. This small contract needs categories, with independent
object universes, rather than a groupoid or a universal intermediate language.
The groupoid source interpreter is used separately in the fixture.

Each coordinate route negates the C₄ base label and adds 1 to the fibre
coordinate. The routes compose: after two stages both the label and the fibre
coordinate are restored. `source_route` and `composed_source_route` compare
the same generated source transport term, rather than unrelated calculations.
The source comparison reduces through the existing all-rule interpreter;
`two_transports` also consumes the existing interpreted concatenation proof.
`double_source_label` preserves every source label even when instantiated
with the ineffective family from `Examples.GroupoidTransport`.

Substitution has two checked meanings here. Precomposition with the
nonidentity label-negation functor changes the ambient family;
`substitution_source`, `substituted_label`, and `substitution_composition`
compare transport, base arrows, and composed routes under that substitution.
`SourceSubstitution.weakened_transport` separately specializes the existing
source reindexing rule to a context extended by one unused base point. It
substitutes both the path and fibre element before selecting a model.
No new source rule or authoring API is introduced.

The forgetting route lands in a discrete one-object base with a singleton
fibre. `orbit_exact` identifies equality of its fibre outputs with the
source's same-orbit relation. Its transport square commutes, but neither
individual fibre values nor C₄ labels can be recovered: the two impossibility
theorems quantify over every proposed decoder. In particular label 2 is lost
even though its ineffective action alone could not have detected that loss.
Faithfulness on base arrows and preservation of the chosen fibre observation
are additional requirements for a route claiming the stronger contract.

Callers supply a functor on base objects and arrows and a natural fibre map;
they need no syntax wrapper for the ordinary route laws. These routes preserve
only their specified set-valued transport contract, not arbitrary source
judgments or reflection. The fixture establishes first-level groupoid
behaviour, not second identities, univalence, or a general higher-type model.
It changes neither #107's authoring implementation nor #108's independent test.

## Checked second-identity fixture (#142)

[`DoubleDelooping`](../../SquareKit/DoubleDelooping.lean) constructs a Mathlib
strict bicategory from a commutative group. It has one object, one 1-arrow,
and group elements as 2-arrows. Its hom-category is the existing `SingleObj`
groupoid. Whiskering, unitors, associator, pentagon, triangle and exchange
are checked in the `Bicategory` instance; `Bicategory.Strict` checks strictness.
Every 1-arrow has a strict inverse. Vertical and horizontal 2-composition both
reduce to the group's multiplication, with Mathlib's composition order.
Commutativity proves interchange, and group inversion supplies 2-inverses.
The C₂ specialization in
[`Examples.SecondIdentity`](../../Examples/SecondIdentity.lean) checks the
cardinalities: one object, one 1-arrow, two 2-arrows.

The primary motivation is the distinction in the HoTT book's
[§2.1, including the Eckmann–Hilton argument](https://github.com/HoTT/book/blob/578b85cc8d586b1677ec4335148adeb443057d24/basics.tex)
between paths and paths between paths. Commutativity of second-loop
composition explains the abelian hypothesis here. Hofmann–Streicher's
[§5.1 groupoid example](https://people.csail.mit.edu/jgross/personal-website/papers/academic-papers-local/agroupoidinterpretationoftypetheroy.pdf)
retains distinct first-identity objects but interprets their identity families
discretely. Those references motivate the test; the strict finite structure
and route comparisons above are separate Lean results.

[`Internal.TwoLoop`](../../SquareKit/Internal/TwoLoop.lean) is an opt-in source
for algebraic 2-loops at that fixed object and fixed 1-arrow. It contains
variables, identity, vertical and horizontal composition, and inverse. Its
explicit equation judgment has congruence, both unit laws, associativity,
both inverse laws and interchange; `sound` proves every derivation valid in
every double delooping supplied here. `Expr.eval_subst` checks substitution.
No dependent types, identity eliminator, universes, arbitrary higher type
theory or third-identity witnesses are part of this source. The equations
are strict laws in the host logic; the interpreted 2-arrows themselves are
data in `Type` and are not native Lean equality proofs.

The same source pasting diagram is interpreted in C₂ labels (`ZMod 2`) and
in Boolean XOR. The independent observations are the label's natural-number
representative and the Boolean's 0/1 value. `encode` is a proved group
equivalence; the shared `map_vertical` and `map_horizontal` results preserve
both compositions. `interpretationSquare` uses the existing `Squares.Square`
contract to compare all source expressions under a group homomorphism.
`routes_agree`, `observations_agree` and `route_roundtrip` specialize that
comparison. The selected diagram combines horizontal composition, inverse,
vertical composition and identity; it yields the nonidentity cell in both
routes. The source interchange proof has checked interpretations in both.
Replacing its generator by a double yields identity, using the shared
substitution theorem. Ordinary clients can apply interchange and cancellation
without using source syntax.

The forgetting target is a terminal groupoid promoted through Mathlib's
`LocallyDiscrete` construction. Truncation preserves both compositions but
identifies the selected diagram with identity. `no_groupoid_observation`
proves the obstruction for any ordinary category promoted this way: each
fixed-boundary 2-hom is a subsingleton, so no observer can recover both labels.
`no_native_identity_observation` states the corresponding obstruction for a
native Lean equality proof. This concerns dimension-preserving identity
interpretations. It does not say that an arbitrary set cannot store labels
as ordinary data, or that moving a label to a different dimension preserves
the original contract.

Future higher routes must retain the appropriate cell data and preserve
both compositions and their interaction; preserving objects and 1-arrows
alone is insufficient. The required common interface here is a commutative
group and its homomorphisms, realized through Mathlib's bicategory and the
existing representation squares. General multi-object or weak higher
interpretations need additional interfaces and coherence proofs. This
fixture supplies none of the dependent-elimination rules needed for a full
HoTT interpretation and does not change #107/#108's authoring boundary.

## Checked finite universe (#143)

`SquareKit/FiniteUniverse.lean` implements Ufin with a wrapper around Nat as
objects and `Fin n ≃ Fin m` as arrows. Its `decode` functor acts by the actual
bijection. `Examples/FiniteUniverse.lean` checks the transposition at 2: it
fixes the code and exchanges the two decoded points. `discrete_loss` proves
that an action on decoded points cannot factor through the functor to
`Discrete Nat`, because that functor identifies swap with identity.

`Enumeration A` keeps a code and a decoding equivalence to A. Its `map`
conjugates an arbitrary bijection by the two enumerations. Naturality,
identity, composition and change-of-enumeration coherence are proved once.
`sumCode` and `productCode` enumerate actual dependent pairs and sections;
`sumEquiv` and `productEquiv` move both base indices and fibre values.
Their element-level naturality and composition laws feed the same enumeration
contract. The checked examples include unequal fibre sizes 1 and 2, simultaneous
base/fibre swaps, the empty sum and the singleton empty product. Enumeration
uses `Fintype.equivFin`, hence classical choice; no executable canonical ordering
is claimed. The computation examples concern decoded data, independently of
which enumeration was chosen.

The two routes are realization into the groupoid of finite sets with chosen
Fintype structures and classification back into Ufin. They use the existing
`GroupoidTransport.Route` interface. `construction_roundtrip` compares the
same enumerated input and bijection through the composed route; sum and product
clients recover the independently calculated pair and section. Route
composition and context reindexing reuse the existing naturality laws.

The bounded generic-family result is `familyEquiv`: for any functor from a
small category into the finite-set groupoid, the total set of the classified
decoding family is equivalent to the original total set over the same base.
`family_projection` preserves the projection and `family_transport` compares
every base arrow. This is a chosen objectwise pullback comparison with transport,
not a claim to classify all small maps in an arbitrary category. It does not
supply a categorical universal property for arbitrary fibrations or univalence.
The need to retain substitution comparisons is consistent with
[Clairambault–Dybjer, §3.1, Definition 7 and Proposition 4](https://arxiv.org/pdf/1112.3456),
which formulate preservation using coherent comparison isomorphisms.

A small second-level construction is also checked: `LargerCode` has finite
codes and a `universe` tag. Its decoding lands in `Grpd.{0,0}`; finite tags
decode to discrete finite groupoids, and the universe tag decodes to the whole
Ufin groupoid. `larger_swap` retains its nonidentity arrow. `no_finite_self`
proves that no finite set can even enumerate Ufin's objects. Both code types
live in Lean `Type 0`, but the second decoding has the larger codomain
`Grpd.{0,0} : Type 1`, not the finite-set decoding family. This respects the
separation of universes discussed in the
[HoTT book, §1.3](https://github.com/HoTT/book/blob/578b85cc8d586b1677ec4335148adeb443057d24/preliminaries.tex).

The remaining nesting theorem would require a second code groupoid with
appropriate equivalences as code arrows, a coherent groupoid-valued decoding,
and closure/comparison maps for dependent sums and products of its supported
groupoid families, including families over Ufin. The tagged function alone
establishes none of those closure or genericity claims. No Type:Type,
identification of host equality with bijections, general small-map classifier,
or new identity eliminator is used. The #107/#108 boundary is unchanged.
