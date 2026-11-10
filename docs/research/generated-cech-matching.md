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

These cases test the matching input and canonical restriction. They do not
exercise generated effective descent on a nontrivial torsor. The primitive
nontrivial torsor and ineffective-action cases remain in
`Examples.CechDeformationDescent` and `Examples.CechOverlapRejection`.

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
