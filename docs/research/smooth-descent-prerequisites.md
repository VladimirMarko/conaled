# Descent prerequisites for the smooth source interpretation

This is a partial #433 checkpoint. The reusable comparison model and the
closure of generated source interpretations remain separate work. These
lemmas do not establish descent for every family in an ambient groupoid model.

## Constructed comparisons

`SheafActionQuotientDescentCategory` turns the existing quotient cocycles into
a category whose morphisms are the existing compatible local maps. Its
`descentFunctor` uses the existing constructed objects and descended arrows.
The existing arrow equivalence proves full faithfulness; canonical recovery
proves essential surjectivity. `quotientDescentEquivalence` obtains the inverse
and coherence from Mathlib's equivalence construction. The selected local
recovery arrow remains available separately, and `Map.comparison_naturality`
proves that it commutes with every compatible local arrow. The category laws
do not require a cover hypothesis; effectiveness and its groupoid consequence
do require the stated locally surjective cover.

`SheafActionQuotientDescentDisplay` proves that a locally surjective parameter
map has a locally surjective split display, using `SplitSheaf.ofDisplay` and
its actual display isomorphism. Quotient objects over the original parameter
and its split presentation are equivalent, including their arrows. The datum
accepted by `displayDescentEquivalence` is still a cocycle on that split
presentation. A separate general Čech-datum encoding on an arbitrary cover has
not been introduced or silently identified with it.

`GrothendieckEquivalence` uses Mathlib's Grothendieck construction. Fullness,
faithfulness and essential surjectivity of component functors produce the
corresponding total comparison, and hence an equivalence. Combining this with
a base equivalence yields `extendEquivalence`; its projection square is an
actual functor equality. Components need only be equivalences, not strict
isomorphisms or bijections on object representations. Actual hom equivalences
supply the identity comparison, including conjugation by the endpoint recovery
isomorphisms.

`SmoothQuotientDeformationDescentMaps` proves preservation and reflection of
local deformation compatibility along the selected quotient arrows. Its
`CocycleDatum.Fiber` contains a local deformation and its matching equations;
there is no supplied global deformation. `fiberEquivalence` constructs the
global deformation and both inverse laws from the existing cocycle gluing
and uniqueness theorems. `fiberFamily` makes these local fibers a functor on
the quotient cocycle category. Its action is proved equal to transport along
`Map.localArrow`, and `fiberComparison` is a natural isomorphism with the
descended global deformation family.

`SmoothQuotientDescentExtension` applies the generic extension theorem to
these comparisons. It gives an equivalence between a quotient cocycle extended
by its compatible deformation and a global quotient object extended by its
deformation. Its base is exactly the existing constructed descended object.
This is one actual primitive context-extension instance of the closure lemma;
it is not the induction over every generated source context.

## Fixed-cover sections

`SectionDescent` reconstructs a complete section from a base equivalence and
natural fiber comparisons whose components are equivalences. It pulls the
supplied section's lift through the total equivalence, then uses the existing
section normalization to make its projection strictly the identity. No
reconstructed section is an input. Recovery is a natural isomorphism of the
whole section functors. Its components project to identity arrows in the
compared base, so it is vertical. `sectionVerticalEquiv` gives an equivalence
of the sets of selected vertical natural transformations between sections;
its inverse laws retain the transformations themselves.

`SmoothQuotientDescentSections` applies this construction to the actual
local-to-descended deformation fiber comparison over the full quotient cocycle
groupoid. The input assigns a matching local deformation to every cocycle and
acts naturally on every compatible local arrow. The output constructs a section of descended deformation fibers, with
vertical recovery through the actual gluing comparison.
The base of this specialization is still the cocycle groupoid. Transport onward
to the global quotient context and compatibility as parameters and covers vary
remain obligations for generated interpretation descent.

## Checked cases and statement review

`Examples.DescentClosure` changes a two-representative contractible groupoid to
one representative in each fiber over a two-object discrete base. It checks
the resulting extension equivalence even though the fiber functor is not
injective on objects. This tests that the hypotheses admit equivalence rather
than requiring identical presentations.

The rejecting case forgets integer-labelled loops to the terminal groupoid.
All endpoints and observed images agree, but the functor is not faithful.
The accepted identity comparison retains the distinct zero and one loops.
Thus discreteness of an identity family must not be confused with discarding
its arrow-valued objects.

`Examples.SmoothDescentMaps` accepts arbitrary local cocycles and compatible
maps, checks preservation and reflection, and checks that the extension
comparison returns the constructed descended deformation. It specializes
recovery and the actual hom comparison to the existing doubled-origin torsor
with ineffective action, without a global trivialization. Its loop statement
retains any pair of distinct selected arrows; the independent integer-loop
example supplies a concrete rejection of forgetting those distinctions.

`Examples.SectionDescent` supplies two sections of a constant integer-loop
family with equal object assignments but different arrow actions. It also
constructs a nonidentity vertical loop transformation of the stationary
section and proves that inverse transport distinguishes it from the identity.
This rejects an object-only section contract and checks that the accepted
comparison preserves selected transformations. Another specialization transports
a loop-valued section across the base equivalence that collapses the two
contractible context representatives.

The section theorem quantifies over all source and target base categories and
all groupoid-valued families in the stated universes. Its input is one complete
section with functorial arrow data, not unrelated objects at each context.
The component-equivalence hypothesis is explicit; it is proved from the
existing deformation gluing equivalence in the smooth specialization. Recovery
is a vertical natural isomorphism, not equality of section representations.

The general extension statement quantifies over arbitrary categories and
functor-valued families, with independent base and fiber universe parameters.
The identity comparison quantifies over arbitrary endpoints and actual arrows.
The quotient descent category retains all original torsors, local maps and
cocycle compatibility, without assuming a trivialization or effective action.
Its equivalence is constructed from existing gluing theorems, rather than
stored as an assumed conclusion in local descent data.

## Remaining work

The generic extension lemma is not yet instantiated as an equivalence between
local *generated-context* cocycles and their Grothendieck decomposition. That
requires relative-family closure beyond the primitive deformation family, generated parameter comparisons and their
coherence. Identity, substitution, conversion, path contexts and arbitrary
finite dependent tails must then be covered together. The unchanged source
transport-composition derivation must be connected through those constructions;
a direct proof of its target equality is insufficient.

Section descent has two useful layers. A section supplied over the full
context-descent groupoid includes its action on all compatible arrows; a fixed
cover transport theorem now reconstructs it with vertical-isomorphism recovery.
Arbitrary locally supplied sections require additional compatibility over
sheaf parameters and covers pulled back to those parameters. A section over
one parameter alone does not provide that contract. The fixed-cover result above proves the first layer from the extension
equivalence and normalization. The second layer remains unproved; the current
result does not supply arbitrary local-section gluing.

The boundary-fiber equivalence and classical chart comparison remain existing
consumer interfaces. Their compatibility with generated descent must be
proved when that descent is constructed. An objectwise equivalence does not
supply such compatibility automatically.

## Validation boundary

Development uses focused Lean checks with the pinned environment and unchanged
trust, heartbeat and toolchain settings. Candidate-wide fresh validation,
exhaustive audit and independent review belong to the enclosing orchestration.
The review handoff records exact commands and revisions; focused checks alone
do not close #433.
