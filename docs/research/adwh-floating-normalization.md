# Exact carry normalization and rounding-unit bounds

This development adapts all 26 named declarations and two source cases from
checkpoint 335's `FloatingNormalize` and `FloatingMagnitude`. The exact source
hashes, coordinates and dispositions are recorded in
`adwh-floating-normalization-provenance.tsv`. Three elementary binary-power
order declarations are supplied directly by Mathlib; the remaining contracts
belong to the existing floating rounding domain.

## Existing operations and separate hypotheses

The pinned logical model owns `Format`, target shifts, residual-bit records,
nearest-even rounding, `roundWithAccuracy` and `round`. This development proves
properties of those operations. `Floating.Observation` retains exact dyadic
meaning; the common `Floating.Rounding.AccuracyRep` relates operation data to an
independent rational; `Floating.Packing.Canonical` owns the existing format
predicate. There is no replacement floating executor or dyadic theory.

`Aligned format m e` states that either the input exponent is at or below the
subnormal floor, or its natural mantissa has at least the required significant
bits. This is the same disjunction already supplied by the actual division
core's precision theorem. It explains why a normalization operation that only
increases exponents has enough incoming precision.

The theorem families deliberately have different hypotheses:

| Claim | Required semantic or shape premise |
|---|---|
| First shifted mantissa is strictly below `2^p`; exponent is at or above the floor | None |
| Normal lower mantissa bound above the floor | Alignment |
| `roundWithAccuracy` produces a canonical result, for either sign | Alignment |
| Positive `roundWithAccuracy` has the stated finite rational observation | None |
| Its error relative to the independent original value | `AccuracyRep` |
| Full `round` produces a canonical result | Positive incoming natural mantissa |
| Positive full `round` value and error laws | No extra alignment or positivity premise |

Here `p` is the format's complete mantissa width, including the implicit bit.
The latter numerical laws describe raw unpacked-model values. They do not assert
that later packing cannot overflow.

## Why the second shift adds no error

The first target shift has mantissa less than `2^p`. Nearest-even rounding then
produces a natural mantissa at most `2^p`. The actual core performs a second
target shift on that exact rounded natural:

- Below `2^p`, the existing width and floor conditions make this a no-shift case.
- At exactly `2^p`, the carry becomes `2^(p-1)` and the exponent increases by one.

`carry_shift_value` proves equality of the exact dyadic values in both cases.
The second shift therefore contributes no extra rounding-error allowance.
The final positive observation is the first rounded dyadic value, and its error
is bounded by half the binary unit selected by the first shift.

The width, floor and normal-lower laws also establish canonicality after that
carry adjustment. Full `round` first decreases the input exponent if necessary;
`decreaseExponent_aligned` connects that execution to the same normalization laws.

## Magnitude determines the first unit

`dyadic_lower_power` transports a natural mantissa lower bound through the
existing dyadic observation. For a positive mantissa, an inclusive bound
`dyadicValue m e ≤ 2^k` gives `totalExponent m e ≤ k+1`.

`shift_exponent_bound` combines the represented-value bound with alignment and
the subnormal floor to bound the actual first shifted exponent by
`max (k+1-p) minExponent`. The bound on the result exponent is a conclusion,
not an assumed input. The inclusive upper endpoint explains the extra bit;
the later strict-magnitude argument has a different bound.

Integer-power monotonicity and order reflection reuse Mathlib's
`zpow_le_zpow_right₀`, `zpow_lt_zpow_right₀` and
`zpow_le_zpow_iff_right₀`. Rational absolute value remains the standard one.

## Consuming an enclosure of the original value

`Examples.FloatingNormalization.interval` decodes the actual positive
`roundWithAccuracy` result and returns the rational interval centered at that
observation with radius half the first-shift binary unit. The public
positive-value theorem proves Option success for raw normalization. Given
`AccuracyRep m a x`, the error theorem proves that this interval contains the
original value `x * 2^e`.

`consume` passes that interval to an existing `Relational.RelSquare` on the
rational interval representation. Its generic soundness theorem uses the
consumer's preservation law. The concrete square operation reuses the existing
four-corner interval multiplication through `Floating.Intervals.squareConsumer`.
Its result encloses the square of the original value.

The retained binary32 cases exercise the two critical boundaries:

| Case | Original represented value | Actual rounded observation | Error radius |
|---|---|---|---|
| Mantissa `2^24-1`, exponent `-23`, upper-inexact accuracy, represented mantissa `m+3/4` | `2-2^-25` | `2` | `2^-24` |
| Mantissa `1`, exponent `-150`, exact accuracy | `2^-150` | `0` | `2^-150` |

Both source constructor equalities are connected to the public target-shift
laws. Separate representation premises and the general error/enclosure laws
connect the displayed original values to interval consumption. In the underflow
case the input interval is `[-2^-150, 2^-150]`; ordinary interval squaring gives
`[-2^-300, 2^-300]`. Its negative lower endpoint is the existing interval
backend's dependency loss, and the interval still contains the original square.

An additional full-round case starts with mantissa one and exponent zero. The
public full-round canonicality and value theorems establish a canonical result
observing one, exercising the initial exponent-decrease path.

## Verification and continuing scope

Statement review covers natural versus integer width arithmetic, the single
alignment proposition, sign scope, zero/carry branches, canonicality versus raw
finite observation, the actual first rounding unit, and original versus rounded
values in the consumer. Small computations remain kernel checked; no generated
exhaustive proof graph, native-evaluation substitute, or resource-limit override
is introduced.
