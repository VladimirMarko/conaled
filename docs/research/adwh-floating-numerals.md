# Floating numeral traces and accepted interval consumption

## Operations and observation have different requirements

`Numerals.Floating.Operations` contains only the source operations: zero,
natural-number conversion, addition and division by ten. `fraction` executes the
literal right fold over those operations. `fraction64` and `fraction32` use the
actual operations of their respective pinned logical models. Binary32 does not
pass through binary64. The model bridges retain the same conversions, association
and division at each step.

The decoder is a separate `α → Option Rat` argument. Concrete observations reuse
`Floating.Observation.decode64` and `decode32`. Both signed zeros decode to zero;
finite subnormals are included; NaN and either infinity are rejected. The source
natural conversions are exact on proper decimal digits by the existing digit
theorems. Arbitrary natural conversion is allowed to round or overflow.

`run` computes the tail and binds the actual conversion, sum and quotient before
asking for their rational observations. It returns the actual result even if the
certificate is `none`. `run_value` proves agreement with the independent pure
executor for every decoder, without a decoder law.

The empty observer result is `(ops.zero, some ⟨0, []⟩)`. The certificate starts at
rational zero without executing a seed observation. Consequently, `run_trace`
and trace-only error, digit and length theorems need no zero-decoding assumption.
`run_sound` and `run_observations`, which identify observations with the actual
result and actual tails, separately require `read ops.zero = some 0`. The concrete
formats discharge that requirement using the existing zero theorems. A checked
synthetic seed-seven case exhibits why the distinction matters.

No commutative-ring or associativity structure is imposed on Float. Standard
rational algebra is used only after the rounded results have been observed.

## Exact residual meaning

A `Numerals.FloatingError.Step` records the natural digit and rational tail,
converted, added and output values. Its residuals are:

\[
e_c=q_c-d,\qquad e_a=q_a-(q_c+q_t),\qquad e_d=q_o-q_a/10.
\]

The local error is `(e_c+e_a)/10+e_d`. The separate-operation bound is
`(|e_c|+|e_a|)/10+|e_d|`. The division residual is outside the division by ten.
The word `operationBound` denotes an absolute numerical residual bound, not an
execution-work measure or relative error.

`Trace` links rational tail and output values, with one step per input digit.
Steps stay in input order even though the right fold executes the tail first.
`Observes` separately relates every stored value to the actual conversion,
addition, division and independently defined executor tail. Rational trace
validity alone does not authenticate arbitrary externally supplied step data.

For every valid rational trace the exact identity is

\[
q-\texttt{Numerals.Decimal.fractionRat}(digits)
  =\sum_{i=0}^{n-1}\frac{e_i}{10^i}.
\]

Both the propagated absolute local-error bound and the more explicit propagated
operation bound enclose this error. The proofs reuse standard Mathlib absolute
values, ordered-field facts, list sums and geometric sums. They do not import the
standalone source's private rational foundation. List multiplicity is retained;
repeated steps are not converted to a deduplicated finset.

The conditional local-epsilon results retain both the coarse factor `10/9` and
the finite factor `(10/9)*(1-1/10^n)`. Their premises are explicit bounds on the
actual recorded local errors. Geometric-series algebra does not discharge the
later IEEE rounding and range argument for arbitrary proper-digit lists.

## Stage completeness, checking and release

`StagesFinite` tests the conversion, sum and quotient of every independently
defined source step. `FiniteRun` specializes it to decoder success. The empty
case is `True`, matching the observer's empty certificate rather than silently
adding a seed check. Exact `run_finite_iff` and rejection theorems characterize
this domain. Concrete format specializations use the 1012 decoder-domain laws.

This condition is stronger than final decodability for general operation data.
A retained synthetic case rejects an intermediate natural value eleven, then
computes a final zero that does decode. The observer still rejects that trace.

`certify` runs the observer and accepts exactly when its propagated operation
bound is at most the requested tolerance. `releaseCertificate` performs the same
check and returns the actual certificate only on acceptance. The public release
equivalence retains both successful production and the bound inequality.
Actual-output soundness uses the separate seed law.

The check is conservative: cancellation can make the true error smaller than
the bound. A rational trace on digits `[2,5]` has residuals `-1/1000` and `1/100`,
zero final signed error, and operation bound `1/500`. It is a mathematical trace
example, not an assertion that these are the actual IEEE steps. Rejection by the
bound check does not prove that the true error exceeds the tolerance.

## A real interval consumer of the intended decimal

For a released certificate with decoded value `q` and operation bound `B`,
`Examples.FloatingNumerals.enclosure` constructs `[q-B,q+B]`. The error theorem
proves that this rational interval contains the intended exact decimal value
`Numerals.Decimal.fractionRat digits`.

`consume` then invokes a supplied existing interval `RelSquare`. Its existing
preservation law encloses the consumer's specification applied to that exact
decimal. The successful-release theorem recovers the produced certificate,
accepted bound and actual executor decoding as well as the final containment.
The exact success/rejection equations remain available.

The concrete `decimalSquare64` and `decimalSquare32` use the existing
`Floating.Intervals.squareConsumer`, built from interval multiplication and
ordinary relational composition. An exact eighth produces the singleton `1/64`.
An accepted inexact tenth encloses `1/100`. Zero-tolerance tenth and overflow
inputs retain `none` throughout the pipeline.

The 1012 singleton adapter encloses a function of the decoded binary value. It
does not by itself account for numeral error. This development supplies that
missing interval before applying the existing consumer. It asserts no
unconditional square from every digit list to successful outputs and never lets
`none` represent an arbitrary rational value. The result is rational interval
enclosure, not rounded floating multiplication or outward-rounded Float endpoints.

## Retained source evidence and scope

The ordinary import closure includes the source value/bit/error cases, all ten
single-digit certificates, and the listed longer source certificates. Empty and
all-zero folds, exact eighths, inexact tenths, the six-digit example, proper nines
rounding to one, repeated-rounding differences, arbitrary-natural conversion
overflow, and positive-exact binary32 underflow retain their source qualifications.
Closed value fixtures and bounded certificate fixtures occupy separate modules
from the structural observer proofs.

All these claims concern the pinned logical Float/Float32 definitions. They do
not establish hardware/native/GHC correspondence, NaN payload preservation,
opaque cross-format conversions, lazy/partial/infinite execution, or physical
costs. The [packing](adwh-floating-packing.md), [rounding](adwh-floating-rounding.md)
and [uniform precision](adwh-floating-uniform.md) developments supply those
separate contracts. Chapter 1 and the whole-book effort
remain open, and the entire queens-16 numerical proof remains excluded.

Focused elaboration and statement/selected-axiom inspection are development
evidence. Acceptance still requires the integrated immutable full build,
exhaustive proof audit, public-entrypoint coverage, final candidate verification
and independent Standards and Spec review.
