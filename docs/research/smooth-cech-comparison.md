# Smooth Čech data and nontrivial torsors

This is the implementation record for [#567](https://github.com/VladimirMarko/conaled/issues/567).
The comparison extends #566's smooth action charts to ordinary local maps and
transition labels on a supplied represented atlas. The implementation includes
selected recovery, refinement and base-change comparisons, with the concrete
clients below. Candidate acceptance is tracked separately from focused checks.

## Mathematical contract

An `Atlas X I` supplies actual maps from ordinary principal-open domains into a
parameter sheaf `X`, a covering-sieve proof, and represented pair and triple
intersections with categorical pullback witnesses. The parameter sheaf need
not itself be a manifold. The construction does not assert that arbitrary
sheaf covers have represented refinements.

The acted-on space has the same scope as #566: a Type-sized, finite-dimensional
real manifold without boundary, with a smooth action of a discrete group.
The generic constructions do not require compactness or effectiveness, and do
not require finiteness where only the group laws and discrete topology suffice.
Finite groups remain admitted clients.

`SmoothCech.Datum` supplies ordinary smooth local maps and locally constant
forward labels before descent is performed. If `uᵢⱼ` carries the local value on
chart `i` to the value on chart `j`, its cocycle is
`uᵢₖ = uⱼₖ * uᵢⱼ`. Diagonal identity is required after restriction along the
actual diagonal. Requiring the entire self-intersection label to be one would
exclude non-monomorphic chart maps without mathematical justification.

A `Hom p q` retains all local forward labels, their endpoint equations and the
compatibility equation `vᵢⱼ * gᵢ = gⱼ * uᵢⱼ`. It retains ineffective stabilizer
arrows. The associated smooth families include both the label and the source
coordinate, with their certificates.

The internal regular-torsor convention is unchanged: an internal quotient
label `k` gives external forward label `k⁻¹`. External labels `g` followed by
`h` compose as `h * g`. The implementation keeps this distinction through
interpretation, extraction and gauges.

## Construction and recovery

`SheafCoproductLocal` supplies local decomposition and equality for the actual
sheaf coproduct, including empty covering sieves. It does not choose a global
summand. `SmoothRepresentedCover` uses it to compare represented pairs and
triples with the actual pullbacks of the coproduct cover.

`SmoothCechDescent` assembles local value maps, interprets inverse transition
labels on the actual overlap, proves the diagonal and cocycle laws, and uses
the existing effective quotient descent. No descended object or desired
comparison is a field of the external datum.

`SmoothCechComparison` constructs the equivalence between complete external
arrow families and arrows between the descended objects. Its intermediate
`LabelMap` retains an actual sheaf label, the endpoint relation and the
compatibility equation. Both inverse equations retain the full records.

For an original quotient object `P`, `TrivializedOn A smoothAction P` supplies
equivariant trivializations of its actual restricted torsors on the given
represented charts. This is the precise additional geometric hypothesis.
Local triviality in the general torsor contract alone does not supply such a
represented atlas. The supplied trivializations give a section on the
coproduct cover, a regularized descent datum and an explicit recovery arrow.
`SmoothCechExtraction` reconstructs ordinary local maps and transitions from
that datum. `extractedDatum_cech` and `extractedDatum_descent` retain the chosen
whole records. `extractedRecovery` returns its interpretation to `P`, including
the manifold-valued map.

`arrowEquiv`, `arrow_roundtrip`, `external_arrow_roundtrip` and
`recovery_naturality` compare the complete external families with the original
quotient arrows and their chosen recovery maps. Identity and composition are
preserved.

## Selected refinement and base-change comparisons

`AtlasMap` retains the base map, chart-index map, actual chart maps and their
commuting equations. Its identity and composition laws retain pair and total
maps. `Datum.restrict_ident` and `restrict_comp` are equalities of complete
external data, including transition labels.

`Datum.restrictComparison` compares reindexing the interpreted object with
interpreting the restricted datum. It is constructed from the actual local
comparison through the atlas total map and existing descent. Its `recover`
law retains that local comparison; uniqueness is proved through recovery.
`Hom.restrictComparison_naturality` retains the complete arrows. Identity and
composition laws use the selected comparisons and explicit equality transport
of the full restricted datum. They do not identify independently chosen
descent objects by literal equality.

`Datum.commonComparison` compares two restrictions into the same actual
common atlas. Its identity, composition and arrow naturality laws retain the
two supplied atlas maps. The clutching client exercises two genuine principal
refinements and their common product refinement. `common_route_coherence`
compares the actual alternate routes to that common atlas. The restricted
interpreted objects still have no global section, by transport through the
selected comparison to the original quarter-turn object.

## Changes of trivialization

A supplied gauge `aᵢ` transforms transitions by
`aⱼ * uᵢⱼ * aᵢ⁻¹`. `gauge_twice` proves equality of the complete resulting datum
with the ordered composite gauge. The identity law is also a whole-datum law.

For two independently supplied trivializations `t` and `u` of the same
original object, `changeOfTrivialization` extracts the original identity
arrow through the established complete-arrow equivalence. Its labels are
therefore constructed, not assumed. `changed_datum` proves that these labels
transform the entire first extracted datum into the second.
`change_recovery` compares the actual chosen recovery arrows; identity and
composite changes retain complete arrows.

## The nontrivial client and actual geometry

The client is the existing clutching torsor over the doubled-origin line
sheaf, with group `C4` and quarter-turn transition on the positive component
of the punctured overlap. The negative component has identity transition.
The target manifold is a real line with the trivial action and constant zero
map. This admits ineffective stabilizers and places no compactness hypothesis
on the charts.

`SmoothClutchingAtlas` proves that the two represented charts and their pair
and triple intersections form an admitted atlas. It builds equivariant local
trivializations from the actual clutching chart sections.
`Examples.SmoothCechDescent.Clutching.interpreted_no_section` transfers a
hypothetical global section through the selected recovery and contradicts the
existing no-section theorem for the actual torsor. Nontriviality is not inferred
merely from a nonconstant cocycle.

The extracted overlap is identified with the original clutching transition as
an equality of sheaf maps at every site stage. `extracted_transition` then
identifies its ordinary forward label with the inverse underlying label. For
`C4`, the negative point has label one and the positive point has inverse
quarter turn. `quarterTurn_transition_varies` proves the two extracted labels
differ. This calculation uses the actual supplied trivializations and pushout
identification, independently of the no-section argument.

`SmoothClutchingRefinement` constructs principal intersections by transporting
the existing all-stage localization pullback through explicit coordinate
isomorphisms. Mixed-origin intersections paste these with the actual clutching
pullback. Iteration gives represented triples. Covering follows by pulling
back the principal covering sieve at arbitrary site stages and composing it
with the original atlas cover.

The two refinements remove `+1` and `-1`, or `+2` and `-2`, separately on each
origin chart. Their common refinement uses pairwise products of those defining
functions. Both maps to the two atlases, and their composite coordinate maps
to the original atlas, are supplied. Omitted-point theorems distinguish these
from identity refinements.

`SmoothClutchingScaling` constructs base scaling maps and explicit inverses
for every nonzero multiplier. It proves nonidentity when the multiplier differs
from one and the composition of scaling by two followed by three is scaling
by six. A principal function `f` pulls back to `x ↦ f(r*x)`.
`principalScalingIso`, `scaling_pullback` and `scaled_chart_pullback` retain the
actual maps and categorical pullback evidence. Scaling does not preserve the
fixed puncture positions. The half-point control distinguishes the domain
excluding `1` from its inverse image under scaling by two. The client supplies
the actual scaling-by-two atlas map and the subsequent scaling-by-three map
on the already pulled-back domains. `scaling_complete_datum` retains all data
under their composite. `scaling_comparison_coherence` specializes the selected
interpretation comparison composition law to those maps through
`ComparisonComposition`, which names the full equation and its explicit
equality transport. The observations
`scaling_domain_six` and `scaling_base_six` identify the resulting domains and
base map with scaling by six.

## Identity-cover reduction

`OneChart.extracted_eq` identifies the whole extracted datum of an original
chart with the independent identity datum, including its transition labels.
`OneChart.recovery` transports the selected recovery along this equality.
`labelsEquiv` and `familiesEquiv` identify identity-cover arrows with the
original labels and complete smooth families. `native_family_agreement`
proves that the chosen local chart arrow gives exactly #566's smooth family.
`TrivializedOn.canonicalDescentMap` constructs a map to canonical descent
from the actual local regularization. Its descended map followed by the chosen
`canonicalRecovery` equals `extractedRecovery`. `canonicalArrowMap` composes
these local maps with the external arrow's descent map; its image under the
existing `canonicalArrowEquiv` equals the recovered external arrow.

`canonical_arrow_agreement` specializes this to extraction of every original
chart arrow. `canonical_family_agreement` retains the complete #566 family,
and `canonical_family_cover_comparison` retains it after the existing selected
comparison to another canonical descent cover.

`independent_family_agreement` starts with an arbitrary arrow between the
independently defined identity data. After transporting the complete datum
along `extracted_eq`, its globally recovered arrow gives exactly the supplied
#566 family. `independent_arrow_agreement` identifies the complete native
arrow. This uses the actual all-stage split regularization coordinates and
`arrowEquiv_split_apply`, rather than assuming that the arrow was produced
by extraction. `independent_canonical_arrow_agreement` retains the actual
canonical descent map and chosen recovery; the corresponding family comparison
also commutes with a change to any admitted canonical descent cover.

## Controls and acceptance

Checked controls include noncommuting `S3` label order, a nonidentity `C4`
gauge, incompatible endpoint rejection, bad diagonal rejection and complete
arrow recovery on an empty domain. A further malformed-cocycle control keeps
all displayed diagonals equal to one and rejects the off-diagonal cocycle.

`SquareApplications` imports the checked consumer module. The implementation
and its statement review are ready for integration; final acceptance requires
the integrated candidate build, exhaustive axiom audit, independent Standards
and Spec reviews, and final verification. Focused author checks do not replace
that acceptance evidence. The final author check built
`Examples.SmoothCechDescent` and its dependencies successfully (3,762 jobs),
its log is `/tmp/conaled-wave-20261115/567/evidence/final-consumers-04.log`.
That author checkpoint retained a section-wide `maxHeartbeats 800000` setting
in `SmoothCechRefinement`; its original description as using default limits
was inaccurate. Independent review reproduced the entire refinement module
without that override, and the override was removed. The corrected integration
candidate `fd1df6cf` passed the full 3,434-module build and exhaustive axiom
audit at default heartbeat limits. The transparency option for that section
remains explicit. This correction preserves the historical checks rather than
reclassifying them as default-limit runs.

Representable refinement of arbitrary torsor covers remains a separate
mathematical question. This delivery supplies the precise represented-cover
hypothesis and proves it for the nontrivial client; it does not claim coverage
of every quotient object. Higher/cohesive semantics, arbitrary
`ModelWithCorners`, Agda conversion and proper-étale finite-bisection
constructions retain their separate scope.

The work does not identify external `IsProperMap`, internal `DPProper` or
`Compact.ProperData`. It adds no properness claim for the chart inclusions,
no general manifold pullback assumption and no claim that the doubled-origin
parameter sheaf is a Hausdorff manifold.
