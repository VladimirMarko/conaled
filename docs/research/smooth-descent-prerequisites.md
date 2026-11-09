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
requires relative-family descent, generated parameter comparisons and their
coherence. Identity, substitution, conversion, path contexts and arbitrary
finite dependent tails must then be covered together. The unchanged source
transport-composition derivation must be connected through those constructions;
a direct proof of its target equality is insufficient.

Section descent has two useful layers. A section supplied over the full
context-descent groupoid includes its action on all compatible arrows; a fixed
cover transport theorem can reconstruct it with vertical-isomorphism recovery.
Arbitrary locally supplied sections require additional compatibility over
sheaf parameters and covers pulled back to those parameters. A section over
one parameter alone does not provide that contract. Neither layer is proved
by the extension equivalence alone, and this checkpoint does not claim either
section-gluing result.

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
