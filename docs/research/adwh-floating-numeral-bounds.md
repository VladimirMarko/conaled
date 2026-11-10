# Constructing numeral certificates from local step laws

This development adapts all fourteen explicit named declarations in the supplied
successor source `ADWH/Chapter01/FloatingNumeralBounds.lean`, SHA-256
`4f84998420acb384427b71bc4da06369b032f65ffb8cac7bf6991cf6f0091bf3`.
The source has no anonymous cases. The companion provenance map records every
destination. No fresh original-book or PDF verification is claimed.

The prerequisites and execution/observation boundary are described in
[Floating numeral traces and accepted interval consumption](adwh-floating-numerals.md).
The new construction supplies successful certificates from local arithmetic
laws, allowing the existing observer, error bounds, checker and interval consumer
to be applied to every proper input under those laws.

## Local laws and constructive success

`Numerals.Floating.StepLaws` is a proposition over the existing `Operations α`,
an independent decoder `α → Option Rat`, and separate addition/division error
parameters. It requires both parameters to be nonnegative and provides:

- Exact conversion of each natural digit below ten.
- Successful addition of a proper digit to an actually decoded tail in `[0,1]`,
  producing a decoded sum in `[0,10]` with the stated addition residual bound.
- Successful division by ten of an actually decoded value in `[0,10]`, producing
  a decoded value in `[0,1]` with the stated division residual bound.

The zero-decoding law is a separate hypothesis of `proper_run`. It identifies
the initial execution seed with rational zero, allowing the actual-tail range
induction to start. `Operations` and `StepLaws` do not store that law. Existing
law-free value erasure, rational trace construction and stage-completeness
theorems retain their original interfaces.

For a proper digit list, `proper_run` constructs a certificate returned by the
existing `run`, an observation of the actual `fraction` result, its closed `[0,1]`
range, and bounds for every recorded step. Success and whole-stage finiteness
are conclusions. At each cons step the proof constructs the actual addition
and division observations from the local laws, then uses `run_value` to identify
the independently defined executor tail.

`StepBounds` records the proper digit, exact conversion, all three closed ranges,
and separate addition/division residual bounds. Its conversion residual is zero,
so its operation bound is at most

\[
\varepsilon = \frac{\varepsilon_{\mathrm{add}}}{10}
              +\varepsilon_{\mathrm{div}}.
\]

The division residual remains outside division by ten. These are absolute
numerical errors, not relative errors or measures of execution work. Closed
endpoints are retained because later formatted executions may reach zero or one.

## Shared finite and coarse propagation

The general propagation results live in the existing
`Numerals.FloatingError` owner. `propagate_uniform_length` uses its monotonicity,
constant-weight calculation and Mathlib geometric sum to prove

\[
\operatorname{propagate}(w,ss)
\le \frac{10}{9}\varepsilon
     \left(1-\frac{1}{10^{|ss|}}\right)
\]

from the pointwise premise `w s ≤ epsilon` on the recorded list. Epsilon and the
weights may be negative. The source list order and multiplicity remain intact.

The coarser `propagate_uniform` bound `(10/9)*epsilon` requires nonnegative
epsilon. Two constant weights of `-1` propagate to `-11/10`, which equals their
finite envelope; the coarse comparison with `-10/9` is false. The retained
`negative_weight_boundary` application exercises both facts through the public
finite theorem and exact rational arithmetic.

Existing `errorBound_uniform` and `errorBound_uniform_length` keep their public
contracts as specializations of these general results. The adaptation adds no
second absolute-value or geometric-series foundation.

## Derived certificate and checker guarantees

`proper_finite_run` derives the existing whole-stage predicate. For any returned
certificate, `proper_certificate` identifies it with the constructed witness and
supplies the range and step facts. Combining the per-step bound with the shared
propagation theorem and `run_length` gives

\[
B \le \frac{10}{9}
       \left(\frac{\varepsilon_{\mathrm{add}}}{10}
                      +\varepsilon_{\mathrm{div}}\right)
       \left(1-\frac{1}{10^n}\right).
\]

The corresponding absolute-error theorem targets
`Numerals.Decimal.fractionRat digits`. Coarse operation and absolute-error bounds
are also retained. `proper_certify` constructs observation success and proves
acceptance by the existing Boolean checker at the coarse derived tolerance.

`Examples.FloatingNumeralBounds.proper_consume` composes that acceptance with the
existing `consume_isSome` and `consume_release` contracts. It constructs a
successful interval result, retains decoding of the actual executor value, and
proves containment of the consumer specification applied to the exact decimal.
The supplied step laws and zero law remain explicit hypotheses of this claim.

## Exact rational specialization and interval square

`rationalOperations` uses ordinary rational zero, natural conversion, addition
and division by ten, with decoder `some`. `rational_step_laws` establishes the
interface with both epsilons zero. Proper digits satisfy `d ≤ 9`, so adding a
tail in `[0,1]` stays in `[0,10]`; division by positive ten stays in `[0,1]`.

The public proper-run construction yields `rational_certificate` for every
proper input. The public error bounds establish the exact decimal certificate
value and zero operation radius. `rational_release` then releases that produced
certificate at zero tolerance.

`rationalSquare` invokes the existing `Floating.Intervals.squareConsumer` through
the generic numeral interval consumer. The zero-radius enclosure is a singleton,
and `squareConsumer_singleton` proves that the actual result is the singleton of
the exact decimal square. Successful containment is also derived through the
general consumer theorem. Input `[1,2,5]` specializes this result to singleton
`1/64`.

The small underflow specialization states explicitly that the exact fraction of
`replicate 45 0 ++ [1]` is `1/10^46`. The constructed rational certificate has
that value and zero radius. The same theorem reuses the existing checked Float32
observation of zero, making the different arithmetic meanings explicit without
repeating the formatted computation.

## Scope

The rational instance demonstrates a satisfiable local-law interface and its
connection to interval consumption. [Bounded floating operations](adwh-floating-operations.md)
derive the Float/Float32 step laws from rounding, packing and range theorems;
[uniform numeral guarantees](adwh-floating-uniform.md) apply those laws to
arbitrary proper-digit lists. These logical model results do not establish
native hardware correspondence or whole-book completion. The concrete
queens-16 numerical proof remains excluded.
