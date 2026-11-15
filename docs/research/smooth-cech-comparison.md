# Smooth Čech data and nontrivial torsors

This is the implementation record for [#567](https://github.com/VladimirMarko/conaled/issues/567).
The comparison extends #566's smooth action charts to ordinary local maps and
transition labels on a supplied represented atlas. Work is in progress; the
final comparison laws and candidate acceptance are recorded below when checked.

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
excluding `1` from its inverse image under scaling by two.

## Identity-cover reduction

`OneChart.extracted_eq` identifies the whole extracted datum of an original
chart with the independent identity datum, including its transition labels.
`OneChart.recovery` transports the selected recovery along this equality.
`labelsEquiv` and `familiesEquiv` identify identity-cover arrows with the
original labels and complete smooth families. `native_family_agreement`
proves that the chosen local chart arrow gives exactly #566's smooth family.
Agreement after global extraction and the canonical recovery comparison still
requires the chartwise recovery specialization described below.

## Controls and unfinished acceptance

Checked controls include noncommuting `S3` label order, a nonidentity `C4`
gauge, incompatible endpoint rejection, bad diagonal rejection and complete
arrow recovery on an empty domain. A further malformed-cocycle control keeps
all displayed diagonals equal to one and rejects the off-diagonal cocycle.

Remaining work includes the selected interpreted refinement/base-change
comparisons, the global one-chart comparison with #566's chosen recovery maps,
additional concrete coordinate observations, complete public integration,
statement review, candidate audit and both independent review axes. Intermediate
focused checks are not final acceptance.

The work does not identify external `IsProperMap`, internal `DPProper` or
`Compact.ProperData`. It adds no properness claim for the chart inclusions,
no general manifold pullback assumption and no claim that the doubled-origin
parameter sheaf is a Hausdorff manifold.
