# Coherent comparisons of ordinary groupoid presentations

Issue [#325](https://github.com/VladimirMarko/conaled/issues/325) extends the
native Type comparison experiment to ordinary groupoids. The implementation is
in `SquareKit/Internal/DependentJudgments/CoherentGroupoidMaps.lean`; the checked
clients are in `Examples/CoherentGroupoidPresentations.lean`.

## Objects and allowed maps

An object consists of an ordinary groupoid context Γ and a functor
`A : Γ ⥤ Grpd`. Its terms are the existing `Section A`, including their action
on arrows. Comprehension is the existing Grothendieck construction `Extend A`.

`DisplayMap A B` contains a context equivalence, a functor between the total
groupoids, and a natural isomorphism comparing its projection with the context
functor. The total functor need not be an equivalence. This is a class of maps
between displayed families, rather than an assertion that every map is an
equivalence of presentations. `changeBase` uses a context equivalence;
`ofNatural` embeds strict natural family transformations. The examples use
invertible changes of carrier, including C₄ versus `ULift C₄`.

Projection compatibility is specified data. It need not be an equality and
does not assert strict preservation of the chosen horizontal lifts. The
existing shear is an admitted map, and its failure to preserve a horizontal
lift remains a checked negative example. This does not identify all commuting
squares with the strictly cleavage-preserving maps.

## Term transport and substitution

For a source section, first compose its total functor with the display map and
the inverse context equivalence. Its projection is naturally isomorphic to
the identity by the supplied projection comparison and the context counit.
Existing `ContextualElimination.normalize` and `Section.ofOver` produce a
target section. `termComparison` retains the natural isomorphism from this
section to that unnormalized image. Neither existence of an unspecified term
nor proof irrelevance replaces these arrows.

`normalize_substitution` proves that normalization after an arbitrary target
substitution equals reindexing the normalized section. `termSubstitution`
retains the corresponding isomorphism; `termSubstitution_twice` checks its
behavior under another substitution. For strict natural family maps,
`reindex_term` additionally compares transport through the pulled-back family
map with reindexing transport, by equality of sections.

These are two distinct statements. The general display-map API compares
normalization and substitution of the image functor. It does not construct an
independent pullback operation on all display-map records. The strict family
fragment has that operation and its term equation. No universal pseudo
morphism of all source theories is claimed.

`term_identity` is equality of sections. `termCompose` compares successive
transport with transport through a composite display map. Its triangle law
relates it to the original normalization comparisons, and
`termCompose_substitution` preserves that triangle under substitution.
`mapComparison` transports natural isomorphisms of section functors and
preserves identity and composition. `termAssociator` compares the two
parenthesizations of a composite through their common raw image;
`termCompose_assoc` proves that the two orders of composing three selected
term comparisons agree. `termIdentity` is the identity map's retained
normalization isomorphism. `termCompose_leftUnit` and
`termCompose_rightUnit` compare insertion and removal of identity maps with
that selected unitor. These unit equations concern natural isomorphisms; an
additional equality of `termIdentity` with `eqToIso term_identity` is not
claimed. The proofs use Mathlib's natural isomorphism composition and
whiskering. They do not introduce a new bicategory of models or claim a
separate pentagon theorem for such a bicategory.

## Chosen contextual J

The existing normalized path equivalence and its telescope extensions specify
chosen contextual elimination. For two such roots, `eliminationComparison`
requires a comparison of the root square and a comparison of the chosen
branches after the display map. It derives a natural isomorphism between the
completed eliminations. The proof uses the existing strict beta equations and
extends the branch comparison along the target root equivalence using its
counit. The final J-preservation statement is not a field or a premise.

`naturalEliminationComparison` constructs the branch comparison for any
strict natural family transformation and any normalized root. It therefore
applies to normalized dependent telescope roots as well as the empty tail.
The worked example uses an actual based-path context, a C₄-valued motive,
and its `ULift C₄` presentation. `chosenJComparison` comes from this generic
construction. `chosenJ_arrow` proves its naturality for every arrow of the
path context. `chosenJ_selected_loop` observes the selected integer residue
on the reflexive branch, using the public substitution and beta equations.

The required root and branch comparisons delimit the admitted J fragment.
An arbitrary display functor alone is not asserted to preserve every chosen
identity family or J operation. The construction supplies a way to derive
that preservation once the primitive motive, root, and branch comparisons
have been supplied. The separate higher-family construction remains #322.

## Selected observations and negative cases

The first client is the existing C₄ binary monodromy example. Independently,
the generator adds one modulo two, while the label two acts trivially on the
binary value. `generatorTransport_zero` checks that the nontrivial comparison
between two substitutions changes zero to one. The comparison is provably
different from reflexivity. `wrapped_zero` checks the coordinate-changing
equivalence `b ↦ ULift (b + 1)` between unequal fiber carriers.
`source_transport` connects it to the existing interpreted source J transport
through naturality. The ineffective label two remains different from zero
even when their actions on the selected binary value coincide.

The second client has genuine groupoid fibers. Its diagonal section sends a
base loop to the same fiber loop. `coherentWrap` changes the fiber carrier and
supplies the central base loop one as its projection isomorphism.
`projection_nontrivial` rejects replacing that comparison by the identity.
`selected_loop` retains every label; `selected_source_loop` connects this to
the existing interpreted source label. In particular labels two and zero
remain distinguishable. `different_context_loop` changes both the context
and fiber carriers and retains the same label. `sequentialComparison` and the
substituted composition triangle exercise the public composition machinery.
The three-map specialization composes the nontrivial `coherentWrap` with a
context change and its inverse presentation change. It checks the selected
associativity equation; both unit equations are also specialized to
`coherentWrap` and its diagonal section.

The shear case rejects an over-strong restriction on the allowed maps. The
binary and groupoid cases reject erasure of the selected comparison or path
data. Ordinary groupoids do not establish preservation of a nontrivial
second identity; no such conclusion follows from these examples.

## Reuse, alternatives, and statement review

The construction reuses `Section`, Grothendieck comprehension, normalization,
normalized root equivalences, strict beta, and Mathlib equivalences and natural
isomorphisms. The pinned Mathlib also has a Grothendieck construction for
pseudofunctors. A bridge to that API would need to connect its total category
to these existing split sections and chosen eliminations. This task uses the
total functor and projection isomorphism directly; it does not duplicate the
pseudofunctor hierarchy or claim that bridge has been established.

Relative to the native Type experiment, section comparison now retains
ordinary fiber arrows and nontrivial projection isomorphisms. The strict
natural-transformation specialization remains available. No existing strict
model-map contract was weakened and no consumer was migrated to a weaker
contract. Model-specific assumptions are ordinary groupoids, an equivalence
of contexts, and normalized equivalences for the chosen J roots. Normalization,
whiskering, comparison transport, and the branch-to-elimination argument are
reusable within those hypotheses.

Statement review distinguishes host equality of sections and functors from
natural isomorphism of their total functors. Source judgmental equality is
not redefined. The concrete source observations reuse existing sound
interpretations; the new API is not a translation of every source judgment.
The examples instantiate the primitive comparison data rather than assuming
the desired observations. Constant C₄ motives exercise non-discrete arrows;
the binary monodromy separately exercises nonconstant action. Neither alone
is described as an unrestricted dependent model equivalence.

Remaining generalization belongs to #235/#289: pullback of arbitrary
display-map records, an all-model pseudo-morphism interface, and its complete
bicategorical coherence. #322 owns higher-family/J preservation. These are
boundaries of this ordinary-groupoid comparison experiment, not a replacement
for its checked substitution, composition, and chosen-J results.
