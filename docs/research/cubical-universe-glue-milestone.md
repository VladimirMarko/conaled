# Internal universes and Glue: a construction milestone

Research for [#403](https://github.com/VladimirMarko/conaled/issues/403).
Local audit revision: `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
Recommendation: construct and test a universe of selected small cubical
families before claiming univalence or importing the retained integer cover.
The first deliverable must settle size and substitution, including a failed
candidate if the current filler representation cannot fit the intended universe.
This is a proposal, not a new construction result.

## What the existing classifiers do

[#321's fragment](cubical-model-construction.md) constructs filling, constructor
closure, contextual marked identity and higher cocycle witnesses.
[`LawfulFamily`](../../SquareKit/Internal/Cubical/FamilyData.lean) is external
semantic data over a context. It is not an internal universe whose terms classify
those families. Its filler quantifies over arbitrary contexts at the specified
Lean universe level, which matters for the size of a proposed code object.

[#143's finite codes](../../SquareKit/FiniteUniverse.lean) retain finite-set
bijections and classify functors into the finite-set groupoid, with dependent
sum/product coherence. The [arbitrary-source classifier](../../SquareKit/ArbitrarySourceClassifier.lean)
classifies the finite complementary-predicate theory using geometric morphisms.
Its stronger source generality does not turn it into a classifier of all small
fibrant cubical maps. No cardinality code can by itself supply the higher path
space and Glue rules required here. `LocalUniverses.lean` addresses a coherence
construction; its name does not establish a univalent cubical universe.

## Exact reference and construction obligations

The semantic target is [CCHM, arXiv:1611.02108v1, Definition 18 and
§8.3](https://arxiv.org/html/1611.02108v1). Codes at a cube are small fibrant
families over its representable. Code/decode are inverse and commute with
restriction. The Russell interpretation uses nested Grothendieck universes.
These set-theoretic assumptions must be replaced by explicit Lean universe
bounds, not added as host axioms.

Proposed implementation graph, with acceptance at each edge:

1. **Size and representables.** Define small fibers in `Type u`, with code
   presheaf in a sufficiently higher universe. Compare cube-local composition
   data with the current context-quantified `Filling`; construct conversions
   and their laws or record the precise obstruction. Do not assert `U : U`.
2. **Classification and decoding.** Construct `El` and `code` over arbitrary
   admitted contexts. Prove reindexing, `El(code A)` and `code(El a)` comparisons,
   stating whether equalities are strict or specified isomorphisms. If only
   isomorphisms are obtained, prove the coherence needed by the chosen source
   rules before advertising a strict source interpretation.
3. **Small constructor closure.** Lift the existing Pi, Sigma, Path and discrete
   providers to codes and prove decoding compatibility, including dependent
   substitution. Keep marked identity separate from Path.
4. **Glue family.** Given a face `φ`, small lawful `A`, small lawful `T` on `φ`,
   and a fiberwise equivalence `e : T ≃ A|φ`, construct the glued family, its
   restriction, introduction and elimination. Prove the full-face identification
   with `T`, unglue/glue and eta equations, and substitution for all these data.
   A natural isomorphism alone is too restrictive as the general equivalence
   input; include the homotopical fiber-contractibility data actually used.
5. **Glue filling and universe filling.** Derive lawful filling rather than
   accepting it as a new unproved provider. Check that the full-face equation
   preserves the selected structure, not just its underlying carrier. Use Glue
   to construct the universe's own filling.
6. **Univalence and source use.** Construct `ua`, prove its equivalence theorem
   and transport comparison. Then interpret the specific source universe/Glue
   judgments used by the retained cover. A CCHM semantic theorem alone does
   not cover Agda's split transport/composition or indexed identity conversion.

Steps 1–3 form an achievable bounded continuation: a checked size/classification
bridge with constructor codes and no promise yet of full univalence. Steps 4–6
are owned residual work of #36, with acceptance tied to the same source consumer.
The graph is a dependency proposal, not a committed schedule or a theorem that
these encodings will succeed. If Step 1 fails, compare a cube-local presentation
and an external native equivalence route before revising shared interfaces.

## Consumers and controls

The positive smallness client is a dependent code `B : El a → U` with
`El (sigmaCode a B)` compared to `Σ x : El a, El (B x)`, and the analogous
Pi comparison after two substitutions. A constant finite code does not exercise
this requirement. A second client constructs the Boolean-negation universe
path and its [separate observations](computational-univalence-transport.md).
The substantive consumer remains the unchanged integer-cover definition and
nested transport in `Monodromy.agda`, tracked in the [HIT plan](computational-higher-inductive-consumers.md).

Reject a glue constructor with mismatched face data, a non-equivalence map in
place of `e`, a decoded family lacking lawful filling, and a code large enough
to violate the declared size bound. Reject an attempted identification of every
universe loop with reflexivity: its Boolean action must detect the transposition.
Retain the integer-cover orientation test because negation is its own inverse.
These are proposed checked controls, not claims of new test execution.

A small finite-only universe can be useful, but it cannot close this milestone
for an integer cover without extending its decoded objects and closure.
Likewise, constructing one path between two codes is weaker than proving
univalence for the selected universe.

## Alternatives and boundary of the recommendation

De Morgan semantics offers local reuse and matches the retained source's
connection operations. This does not establish that it minimizes total effort.
[Cartesian cubical semantics](cubical-judgment-compatibility.md) changes the
primitive rules and needs a translation; axiomatic HoTT leaves the selected
execution observation unsupported unless given another realization. Compare
these routes on the unchanged cover, including source admission and repair,
rather than selecting by theorem counts. Smooth/cohesive compatibility stays
with #36/#100; neither classifier closure nor Glue filling establishes it.

No Lean or Agda build was rerun for this documentation-only investigation.
The [fibrancy inventory](fibrancy-capability-assessment.md) identifies reusable
providers and their exact hypotheses. All new formal work must pass the normal
statement review, examples and proof audit with no new axiom exceptions.
