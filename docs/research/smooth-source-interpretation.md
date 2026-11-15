# Smooth source interpretation and generated descent

This report supersedes the earlier partial #433 construction checkpoint.
The unchanged first-path transport-composition derivation is interpreted in
`SmoothQuotientSource.model a X` for every sheaf parameter X. Its external base
is the entire quotient torsor groupoid and its external fiber is the constructed
deformation family. The generated context, family, substitution and full-section
descent obligations are implemented by #445, their selected comparison coherence
by #446, and original-cover transfer by #447. The bounded integration was
accepted at `3c064b11a5812e38c317601473e6897f65ce2a32`; see
[Acceptance and validation](#acceptance-and-validation) below. The scope limits
in this report remain unchanged.

## The retained source proof

No source rule or proof was changed. The source-consuming route is:

1. `SmoothQuotientDeformations.source_composition` invokes the public
   `GroupoidTransport.transport_concat` wrapper.
2. That abbreviation names `GroupoidModel.UniversalTransfer.transport_concat_universes`.
   It uses the existing universe-lift model and calls `transport_concat`.
3. The latter calls `TransferConsumer.consume` with
   `Typed.Authoring.UniversalTransfer.proof` and its actual generated inputs.
4. `consume` interprets that generated term, extracts equality in the discrete
   fiber, and identifies source transport and concatenation by the existing
   `SourceSemantics` and `ConcatSemantics` results.

This is the unchanged #104/#105 first-path proof selected in #102. The
`transport_comp` lemma needed to construct the semantic family is recorded as
model setup. It is not the body of the source-consuming theorem. The classical
consumer applies the interpreted source result before using the previously
proved coefficient/derivative comparisons.

The exact source requirements are already available: empty and extended typed
contexts, simultaneous substitution and comprehension pairing, the externally
assigned base and its fiber family, identities and reflexivity, conversion, and
J with the dependent `z,q,b` tail. The quotient is supplied as the external base;
its tangent family is supplied as the external fiber. This construction does not
require a source term presenting `BG`, general dependent sums, universes,
univalence, cohesion, or crisp judgments. No #107 operation or favorable #108
result is used as a prerequisite.

## Family on arbitrary quotient torsors

For a sheaf parameter `X`, let `P : SheafActionQuotient.Object a X`. A
`SmoothQuotientDeformations.Deformation P` is an equivariant sheaf morphism

    D × Total(P) → M

whose value at zero is `P.totalMap`. The total sheaf is the actual torsor total
space. The definition requires no global section or trivialization of `P`.
Naturality in the presentation stages belongs to the sheaf morphism; it is not
an additional pointwise continuity assertion.

A quotient arrow acts by precomposition with its inverse torsor map. This gives
the set-valued functor `family a X` on the entire quotient groupoid. The constant
deformation witnesses nonemptiness even for a nontrivial torsor. Quotient objects
live in `Type 1`, while their arrows and deformation sets use the existing small
sheaf-section universe. The source wrapper's explicit universe lifts accommodate
these sizes without resizing.

Restriction along every map `Y → X` pulls back the entire deformation map.
`restrict_id`, `restrict_comp`, and `transport_restrict` prove its laws. These
particular equalities reduce to the chosen split pullback implementation. They
do not identify distinct quotient arrows, including arrows acting ineffectively.

## Boundary and chart comparisons

In the `SmoothQuotientDeformationFiber` module,
`SmoothQuotientDeformations.Fiber P`: the structured-arrow category of quotient
arcs with an actual boundary arrow from `P` to their zero restriction.

A deformation produces such a quotient arc on the pullback of `P`'s torsor.
Conversely, fullness of torsor restriction along zero lifts the given boundary
torsor arrow. This constructs `fromFiber`; `recovery` retains the coherent
boundary isomorphism. Faithfulness of zero restriction proves full faithfulness
of the comparison. `equivalence` therefore applies to every quotient object,
including objects that admit no global chart lift.

`transportComparison` compares deformation transport with forward boundary
transport. It is an isomorphism with a boundary triangle, not an equality of
quotient objects. `fiberRestriction` and `comparison_restrict` retain the boundary
under every sheaf-parameter map.

On a chart lift, `chartEquiv` evaluates at the identity of the regular torsor;
its inverse extends an arc equivariantly. `toArc_transport` identifies the result
with `SmoothQuotientTransport.forwardArcTransport`. The quotient convention is
still `m = g·n`, so forward transport uses the inverse label. The action arrow for
an ordinary element `g` has label `g⁻¹`, hence acts forward by `g`.

`source_arc_composition` transports the result of the unchanged source proof
through this equivalence. `SmoothQuotientSource.origin_classical_composition`
then uses `origin_forward_classical` to obtain the composition of the actual
classical manifold derivatives. The comparison with those derivatives uses the
existing coordinate and fixed-lift theorems; it is not definitional equality.

## Primitive family descent

For any locally surjective sheaf map `f : Y → X` and fixed arbitrary quotient
object `P`, `DescentDatum P f` contains a deformation on `P|Y` and the matching
condition on the induced cover of `D × Total(P)`. It assumes no global deformation
or effectiveness witness.

`DescentDatum.descend` uses effective descent of sheaf maps to construct the
global map. Its zero equation follows by cancellation of the total-space cover.
Its equivariance follows by cancellation after adjoining the group parameter.
`descend_restrict` and `descend_unique` establish effectiveness and uniqueness.
`CocycleDatum` combines this with quotient-object cocycle descent. Its inputs
are a local quotient object, torsor cocycle, compatible local value map, and
local deformation invariant under that cocycle. The descended quotient object
is constructed by the existing quotient descent theorem. `CocycleDatum.descend`
then constructs its deformation; `recover` recovers the local deformation via
the quotient comparison arrow, and `unique` proves uniqueness on that descended
object. No global quotient object is an input.

## Generated contexts, families and complete sections

`SmoothQuotientGeneratedMatching.descentEquivalence` has the actual canonical
restriction functor as its forward map. Its only covering hypothesis is local
surjectivity. `SmoothQuotientCechLocal.familyEvaluation_isEquivalence` proves
all typed-family constructors, including identities and arbitrary substitution;
`matchingEvaluation_isEquivalence` proves every typed context. Telescope and
context normalization retain the original raw context and semantic code and
cover finite dependent tails, pulled tails and path-reindexed tails. These are
constructor proofs, not an assumed matching equivalence or a list of closed
examples.

The independent relative matching family stores local fiber objects, actual
overlap arrows, diagonal and triple laws, and their prescribed base projections.
Its comprehension equivalence reconstructs the matching groupoid of the extended
context. Thus nonidentity vertical arrows survive even when a primitive
deformation family is discrete. `SmoothQuotientGeneratedMatching.sectionDescent`
reconstructs complete sections, gives a natural recovery isomorphism with its
selected base component, and gives a bijection on all vertical transformations.
The inputs do not require local objects to extend globally.

For an original locally surjective sheaf map f, the corresponding public APIs
are `SmoothQuotientCoverMatching.descentEquivalence`, `relativeMatchingFamily`
and `sectionDescent`. Their Čech diagram uses f's actual categorical double and
triple pullbacks. `restriction_toSplit` identifies canonical restriction with
the split presentation; `matchingEquivalence` recovers all local objects,
overlaps and arrows in both directions. The presentation section comparison
uses an equivalence of total dependent matching categories and its explicit
base projection comparison, rather than equality of arbitrary groupoid objects.

`sourceSection_totalRestriction` and `universalTransfer_restriction` connect
the exact interpreted source section to the original-cover total matching
restriction on objects and arrows. `Examples.OriginalCoverGeneratedSections`
specializes this to the disk action and the dependent-tail J caller.
`restriction_substitution` is a whole-functor equation for every generated
substitution. `SmoothQuotientCechLocal.familyEvaluation_transport`
retains the selected natural fiber comparison and its identity/composition
laws. The #446 context/family comparisons have identity, composition and both
whiskering laws; section coherence includes the generated dependent-J case.
`SmoothQuotientGeneratedBaseChange.universalTransfer_square` applies that
selected square to the exact `Typed.Authoring.UniversalTransfer.proof`, with
its original context and type. `Examples.SmoothSelectedComparison` specializes
it to the same disk action used by `origin_classical_composition`, the ineffective
action, and an independent dependent-tail J caller. These comparisons retain
actual arrows; uniqueness of a final discrete equality is not their premise.

## Scope

The result supplies this source interpretation and its stated generated descent
fragment. It does not establish all of Myers's modal foundations, general
microlinearity, Weil–Kock–Lawvere theory, transverse pullbacks, proper étale
presentations, univalence, cohesion, crisp judgments or new source syntax.
The external properness theorem and the separate internal properness obstruction
retain their own statements. The construction is not completion of the broader
#36 programme. These known-theorem consumers do not measure independent author
productivity; that remains a separate investigation.

## Checked cases and statement review

`Examples.SmoothSourceTransport` retains an ordinary caller with arbitrary
quotient objects, arrows, and deformation. It also checks:

- the doubled-origin quotient torsor with no global chart lift, a source consumer
  over that torsor, and recovery of an arbitrary boundary datum over it;
- the four origin automorphisms and trivial isotropy at nonzero disk points;
- distinct ineffective loops and source-derived identity transport for their
  composition;
- effective deformation descent over arbitrary locally surjective parameters;
- recovery of local deformations from quotient torsor cocycles without a supplied
  global quotient object.

Statement review checked quantifier order, zero boundaries, inverse-arrow
orientation, and the distinction between equality of deformation maps and
isomorphism of boundary objects. The nontrivial-torsor case rules out an implicit
global-trivialization premise. The ineffective case checks that transport on a
set-valued tangent fiber does not erase base isotropy. These are known theorem
consumers, not an independent author-productivity trial.

Model-specific work consists of the deformation family, boundary equivalence,
chart comparison, parameter maps, and descent. Reused proof work is the existing
source term, interpreter, and transport/concatenation evaluations. The original
Typed first proof, old Contextual proof and existing ordinary clients remain
unchanged. No #108 preparation or broader modal/properness comparison is included.

## Acceptance and validation

The [#433 acceptance record][acceptance] dated 10 November 2026 reports
successful fresh validation and independent Standards/Spec review of the exact
candidate `3c064b11a5812e38c317601473e6897f65ce2a32`. It records:

- `./check.sh --candidate HEAD --fresh --jobs 4`: all 2,729 project modules
  plus the exhaustive audit passed (2,730 checked modules total).
- `./check.sh --verify-candidate HEAD`: the exact candidate matched the fresh
  receipt immediately before acceptance.
- The transitive axiom union was `propext`, `Classical.choice`, and `Quot.sound`.

These are the validation results for that candidate, not a claim of a new run
for subsequent documentation changes. The earlier entrypoint failure produced
no acceptance receipt; the corrected candidate passed a repeated complete fresh
run. Focused development checks and earlier checkpoint results did not replace
that gate. The result remains the bounded source interpretation and generated
descent fragment described above, not a full Myers modal model or a new
properness comparison.

[acceptance]: https://github.com/VladimirMarko/conaled/issues/433#issuecomment-6781234863

[#433]: https://github.com/VladimirMarko/conaled/issues/433
