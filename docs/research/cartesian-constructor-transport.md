# Native Cartesian constructor transport

[Issue #631](https://github.com/VladimirMarko/conaled/issues/631) supplies dependent
pair and function transport along the Cartesian model's own universe paths.
Import `SquareKit.Internal.Cubical.CartesianConstructorTransportSubstitution`
and open `SquareKit.Cubical.Cartesian.SmallUniverse.LargeConstructors`.

## Inputs and selected sections

`pairAlongPath p b z` and `functionAlongPath p b z` accept an actual native path
`p : paths a₀ a₁`, a dependent code `b` over the entire decoded display of
`codeOfPath p`, and a source section `z`. The source and target codes remain in
the types. In particular, `p` can be the independently chosen Cartesian
`NativeUnivalence.ua a₀ a₁ f E`, retaining its supplied equivalence witness `E`.
No restriction of a De Morgan univalence path is involved.

The underlying algorithms also accept arbitrary source and target interval
terms. `pairFirst` fills the carrier. `pairSecond` fills the dependent field
along that very carrier section, and `pairSection` retains both components.
`pairFirst_path` identifies its endpoint with native universe transport,
including both endpoint code conversions.

`functionArgument`, `functionBody`, and `functionSection` expose the native
function-filling recipe. A target argument is extended backwards from its
variable target cap before the source function is applied. The dependent
result is then filled forwards along that argument section. The resulting Pi
term retains values at every restriction-indexed argument. The `_source`
theorems identify the whole source section, and `functionSection_apply`
identifies the whole dependent body.

## Comparison with universe transport

For any admitted result `R`, `R.codePath` is its actual constructor code path.
`R.codePath_transport` identifies its native path map with the canonical
decoder's chosen transport. `R.transportInFamily` expresses that transport
through the two endpoint decoder isomorphisms.
`R.roundTripComparison` gives a native path recovering the entire source field
after forward and reverse transport, including its dependent witnesses.

`R.transportFromSection` derives a comparison from a whole section and its
source-cap equation. The construction uses
`IntervalTransport.prescribedLineComparison`: native relative lifting for
evaluation compares the canonically selected transport line with the supplied
section. It does not accept the final transport-preservation assertion as an
input. `pairTransportFormula` and `functionTransportFormula` supply their
algorithmically constructed sections and cap proofs to this comparison.

These results are native homogeneous paths, with selected bodies retained.
They do not assert equality of arbitrary transport endpoints. The helper
`homogeneousPath_observe` yields equality only after a specified observation
into a constant family. `piObservation` applies such an observation to a
dependent function at a specified argument.

## Substitution and rebuilding

`pairSection_reindex` and `functionSection_reindex` give exact whole-section
equations. The function equation includes the full `piReindexIso` adapter.
`FunctionFilling.fill_input_reindex` also covers arbitrary tubes and variable
caps, rather than just the empty boxes used for transport.

Restriction of a fixed result preserves the exact selected comparison body:
`Result.transportComparison_body_reindex` and
`Result.comparisonInFamily_body_reindex`. Their proof uses uniformity of the
actual evaluation lifting and its family-input reindexing equation. The
endpoint cast in `prescribedLineComparison` is exposed by its `_body` theorem;
endpoint agreement alone would not establish the body equation.

An independently rebuilt constructor is a distinct result.
`pairRecomputedComparison` and `functionRecomputedComparison` retain both
chosen comparisons and connect their transport endpoints by native
concatenation and reversal. They use the exact section equations and the
decoded-family adapters from
[#606](https://github.com/VladimirMarko/conaled/issues/606).
They do not assert equality of the independently selected comparison bodies.
The stronger fixed-constructor equation was completed by
[#671](https://github.com/VladimirMarko/conaled/issues/671), using
the [canonical decoder recovery](canonical-decoder-filling-recovery.md)
completed by [#607](https://github.com/VladimirMarko/conaled/issues/607).
The public `pair_comparison_body_recomputed` and
`function_comparison_body_recomputed` derive exact equality with arbitrary
source and target caps; see [the body contract](constructor-recomputation.md).
The algorithms here derive their paths without assuming a
canonical-versus-returned filler equality.

## Consumers and statement review

`Examples.CartesianConstructorTransport` uses native univalence for permutations
of `Fin 3`. Native Glue's target coordinate admits a dependent fiber
`Fin(q+1)` over the whole line through the public small-presentation interface.
Fibers at coordinates zero and one are proved nonisomorphic. The function
codomain retains this witness together with a `Fin 3` label; those output
fibers are also nonisomorphic.

The examples consume the new pair and function sections and their comparisons.
They check noncommuting successive swaps, inverse recovery, and a three-cycle
whose transported identity-labelled function evaluates using the inverse
argument. That value differs from both the original argument and its forward
transport. Variable source caps, a proper face, two nonidentity substitutions,
and their composite exercise the whole-section and comparison APIs.
`Substitution.PairCase` and `Substitution.FunctionCase` retain the full section
equations, fixed-result and independently rebuilt body equations, and native
paths comparing the two transport endpoints. The function case also retains
its whole proper-face filling equation. Their concrete instances reuse these checked interfaces;
they do not normalize the admitted code's implementation in every assertion.

[#625](https://github.com/VladimirMarko/conaled/issues/625)'s structure-identity
clients can use these algorithms for carrier-dependent fields and functions.
They must retain the supplied carrier equivalence witness, the dependent
codomain line, endpoint decoders, whole transported fields, and comparison
paths. Converting those paths to exact equality requires an appropriate
observation or a separate discreteness theorem. Exact compatibility with
independently rebuilt comparisons uses the completed #671 body theorem.
The [total structure-identity theorem](cubical-structure-identity.md)
is a separate construction.

Statement review checks the dependent display in the input type, both endpoint
adapters, the backwards argument direction, and whether each conclusion is a
whole-section equality, a body equality, a native path, or an observed equality.
The implementation introduces no host axioms or proof-audit exceptions.

`pairSection_reindex` retains a declaration-local `maxHeartbeats 400000`
allowance. Its development check exhausted the default 200000 heartbeats; the
substitution module subsequently built in 12 seconds and its final worker
check took 13 seconds. These are whole-module times. No declaration-specific
passing profile or final-base default-only probe was retained. The allowance
does not change the selected filling algorithm or the theorem's statement.
