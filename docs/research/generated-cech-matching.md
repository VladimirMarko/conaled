# Generated Čech matching input

This is an intermediate construction for [#445](https://github.com/VladimirMarko/conaled/issues/445).
It defines independent matching data and the actual global-to-local functor.
It does not yet prove effective descent for generated contexts or families.

`Internal.PathTransport.CechMatching.Diagram` records local, double-overlap and
triple-overlap groupoids, their restriction functors and selected endpoint
comparisons. Its `Datum` supplies a local object, an actual overlap isomorphism,
and diagonal and triple-overlap laws. Morphisms retain their complete local
arrows and their overlap squares. Inverting those arrows gives a groupoid;
the forgetful local functor is faithful. No global object, effective descent
hypothesis or prescribed gluing comparison occurs in this definition.

`StrictDiagram` supplies these endpoint comparisons from strict functor
identities. Its `equalFunctor` constructs canonical matching when a functor's
two overlap restrictions are equal. The equality-transport proof is generic;
its smooth specialization does not unfold the generated semantic model during
that proof.

`SmoothQuotientGeneratedMatching` instantiates this construction using the
existing direct interpretation and its generated parameter restriction laws.
It uses one `CtxDeriv` and its semantic code at all parameter objects. The
resulting `restrictionFunctor` restricts both objects and arrows along the
actual split display. Its overlap is the canonical equality-induced
isomorphism. This uniform construction applies to telescope and branch
contexts as well as ordinary extensions. It does not establish the induction
identifying these data with an interpretation over primitive quotient cocycles.

`CechMatching.StrictMap` maps the local, double and triple groupoids with
six strict restriction squares. Its induced matching functor preserves actual
local arrows; the diagonal and cocycle proofs follow from those squares.
Identity and composition are functor equalities. Strict inverse diagrams give
an equivalence of matching categories, with no assumed matching equivalence.
This supports cover-presentation isomorphisms whose restriction laws are strict;
it does not assert the same construction for arbitrary weak diagram maps.

`SmoothQuotientGeneratedMatchingSubstitution` instantiates all six squares
using generated substitution preservation. It supplies matching substitution
functors, including the comprehension projection, with their exact local
object and arrow action. Relative-family identification and effective descent
still require further work.

## Statement review and checked cases

The matching input permits arbitrary local objects with arbitrary overlap
isomorphisms satisfying the equations. Canonical matching for restrictions is
a separate constructor, not a requirement on the input. Neither local
surjectivity nor faithfulness of parameter restriction is used. The equations
compare actual arrows after selected endpoint identifications; they do not
replace groupoid fibers with sets.

`CechMatchingConstant.constantEquivalence` recovers an arbitrary groupoid from
its identity-display matching category. It preserves its entire hom-sets.
`Examples.GeneratedCechMatching` specializes this result to integer-labelled
loops: the selected one loop remains distinct from the identity arrow, but
using it as an identity-display overlap violates the diagonal equation. The
same example module checks the actual smooth object and arrow restriction
formulas and accepts any finite telescope derivation.

`Examples.GeneratedMatchingMaps` swaps the two objects of a discrete groupoid
at all three diagram levels. Its matching functor moves the false representative
to the true representative, and the proved strict inverse constructs the
matching equivalence.

These cases test the matching input and canonical restriction. They do not
exercise generated effective descent on a nontrivial torsor. The primitive
nontrivial torsor and ineffective-action cases remain in
`Examples.CechDeformationDescent` and `Examples.CechOverlapRejection`.

## Relative matching fibers

`GroupoidFiberDecomposition` constructs a natural groupoid-valued fiber family
for any groupoid functor. A fiber object contains a domain object and a selected
base arrow. Fiber morphisms satisfy the corresponding square. Its total category
is equivalent to the domain, with a natural comparison of base projections.
`SmoothQuotientGeneratedMatchingFibers` applies this construction to the actual
matching projection of a generated comprehension. No cover hypothesis is needed.

This is a homotopy-fiber decomposition of independent local matching data. It
does not identify those fibers with generated type semantics and therefore does
not prove effective descent. `CechMatchingSetFamily` separately specifies local
values satisfying an equation along the supplied overlap arrow and proves their
naturality under all matching-context arrows. Neither construction assumes that
local data extend globally.

Statement review: the fiber projection comparison retains the supplied base
isomorphism; the full and faithful total forgetful functor retains every domain
arrow. `Examples.GeneratedMatchingFibers` checks the construction on an integer
loop groupoid and the set-family matching equation on identity displays. These
checks supplement, but do not replace, the dependent-tail effectiveness cases
still required below.

## Work remaining for #445

- Identify matching data for a generated comprehension with a base datum and
  its independently specified matching fiber, retaining its projection and
  all local-arrow actions.
- Construct identity-family matching with selected endpoint arrows, and prove
  family naturality and substitution compatibility.
- Prove the full induction through finite dependent tails, including pulled-back
  and path-reindexed tails. The existing uniform definition is not this proof.
- Combine that identification with the existing generated equivalences to
  construct effective descent and selected recovery through actual restriction.
- Reconstruct complete sections from supplied local data, with vertical
  isomorphisms and uniqueness, and connect the effective/ineffective torsor
  consumers and failed matching cases.

Focused checks use the pinned shell and unchanged trust and heartbeat settings.
Independent review, the parent fresh build and exhaustive audit remain part of
candidate acceptance. This checkpoint does not close #445 or #433.
