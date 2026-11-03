# Recursive fusion through initiality

Implementation of [#252](https://github.com/VladimirMarko/conaled/issues/252),
following the [construction assessed in #248](recursive-argument-transport.md).

The recursive argument is now proved once in
[the categorical fusion module](../../SquareKit/ListInitial/Fusion.lean).
The types and presheaf clients apply that proof. They do not assume fusion as a
model law or prove it independently by induction at each presheaf stage.

## Shared argument and assumptions

`signature A` is the endofunctor `1 + A × -`. `actionAlgebra f h` gives the
exponential `S^I` its empty observation `h` and cons operation
`(a,k) ↦ (i ↦ k(f(i,a)))`. Postcomposition and precomposition become algebra
morphisms; the latter uses the local commuting square. Uniqueness of morphisms
from the initial list algebra equates the two folds. Uncurrying gives `fusion`.

The public equation uses argument order `I × L A`, matching Mathlib's
left-tensor exponential adjunction. Swapping the arguments gives the
`L A × I` equation in the research specification. Both equations range over
arbitrary generalized seeds, not only global elements. The `applyHom` helpers
express generalized application, and exponential extensionality follows from
the adjunction. There is no well-pointedness assumption.

The implementation requests chosen Cartesian products, binary coproducts and
Cartesian closure. The proof uses `I^I`, `S^S` and `S^I`, together with list
initiality for the particular input object. These are sufficient assumptions
for this construction, not universal requirements for data structures or
compilation targets. Initiality and algebra morphisms are Mathlib's existing
interfaces. The algebra operations and morphism laws are separate declarations.

## Model construction and ordinary use

[Types](../../SquareKit/ListInitial/Types.lean) supplies the list algebra,
its recursive fold and uniqueness. `run_eq` identifies the constructed action
with ordinary `List.foldl`. `reachable` builds the subtype of valid states and
uses the same fusion theorem twice: once for observation, once to forget the
subtype. `foldl_reachable` retains the original theorem's independent universe
levels using `ULift`; its representation-comparison lemma uses host induction.
No injectivity, monoid structure or decidability of the invariant is required.

The summary recovery in
[RecursiveFusion](../../Examples/RecursiveFusion.lean) has the original
`OrderedSummary.batch_summary` hypotheses. A concrete ordered diagnostic batch
uses that recovery. Existing ordinary sequence modules and their imports stay
unchanged: callers can continue supplying direct operations and local laws
without categorical syntax.

[Presheaves](../../SquareKit/ListInitial/Presheaves.lean) constructs pointwise
lists for a small category with small hom types. The list fold is natural by
induction using the algebra's naturality; uniqueness is equality of natural
transformations. These are proofs of the model's initiality. Its `run_eq`
proves the component computation equation, using the exponential beta law.
`foldl_fusion` then applies the shared categorical `fusion`, with no induction
in that application proof.

Exponentials come from Mathlib's `FunctorToTypes` closed adjunction. Their
sections are compatible families along arrows, rather than pointwise function
spaces. In the walking-arrow example, `sectionToNatural`, `naturalToSection`
and their round trips identify a fine exponential section with a natural
transformation: its fine and coarse functions commute with restriction.
`exponential_restriction` shows restriction selects the coarse function.
No claim that evaluation preserves exponentials is used.

## Checked application and statement review

The example's inputs restrict `(Nat,Bool) → Nat`. Sequences restrict by mapping
that projection. Summaries restrict `(length,ordered Boolean word) → length`.
Cache validity is a stable subfunctor; its inclusion is monic. Push, summary and
observation are natural transformations. `closed` proves cache preservation,
`factorization` relates valid-state push to ordinary cache push, and `square`
proves the local observation law. `cached_fusion` and `forget_run` invoke the
shared recursive result.

Retained cases cover an empty input with a nonempty valid seed, a nonempty input
with that seed, the repeated ordered word `[true,true,false]`, swapped labels,
and the coarse result after restriction. The negative cases retain an invalid
fine cache that becomes valid after restriction, a prepending update whose
length is correct but whose ordered word violates the local square, and a
singleton that rules out naturality for fine length paired with coarse zero.
`no_bad_observation` states that last obstruction for any purported natural
transformation with those component formulas.

Statement review checked the following distinctions:

- Initiality supplies uniqueness of algebra morphisms, not an assumed fusion
  conclusion. The two requisite morphisms are constructed from the stated
  operations and the local square.
- Validity only restricts the local square. Forgetting the subtype is derived,
  and arbitrary valid seeds remain explicit. No witness is extracted from an
  existential proposition.
- Model initiality and computation comparisons use host recursion. The fusion
  argument itself is reused categorically. The result does not transport
  arbitrary induction, compiler syntax, dependent proof data or fixed points.
- The ordered word and sequence values remain available. Restriction preserves
  equality and validity but reflects neither in this example. No higher
  identity or runtime-performance claim is made.

## Encoding evidence and #235 handoff

The mathematical construction required no stronger local observation law than
the research specified. Lean's elaboration did require care around chosen
coproduct instances hidden behind algebra-carrier definitions, concrete
morphism coercions and association of categorical compositions. Local backward
transparency options and generalized-application helper lemmas resolved these
obligations. An attempted expansion of the functor exponential's implementation
was replaced by its existing beta law; that proof is shorter and depends on
the public adjunction contract.

This records one author's implementation experience, not a controlled usability
trial or a limitation inherent in Lean. The ordinary specialization remains
small; model authors still construct initiality and interpret operations.
[#235](https://github.com/VladimirMarko/conaled/issues/235) retains the interface
questions: a smaller selected-exponential capability interface, reusable
invariant-subobject adapters beyond this example, and transport along functors
with explicit product/list/exponential comparisons. None is required by the
present client. General dependent induction and compiler recursion remain with
their existing owners, including #109.
