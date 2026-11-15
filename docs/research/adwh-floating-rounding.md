# Actual floating rounding and arithmetic cores

This development adapts the 44 named declarations and ten anonymous cases in
checkpoint 335's `FloatingRounding`, `FloatingShiftRound` and
`FloatingArithmetic`. The exact source identities, hashes and dispositions are
in `adwh-floating-rounding-provenance.tsv`. This is a primitive rounding and
arithmetic-core contract. Packing, subsequent normalization, formatted operation
range bounds and uniform numeral bounds remain separate obligations.

## Shared meaning of existing operation data

The pinned Lean model owns `Accuracy`, `ExtendedMantissa`, nearest-even rounding,
quotient classification and shifts. The adaptation uses those operations directly.
`Floating.Rounding.AccuracyRep m a x` relates the actual accuracy tag to an
independent rational value in the current mantissa units:

| Accuracy | Meaning |
|---|---|
| Exact | `x = m` |
| Inexact, below the midpoint | `m < x < m + 1/2` |
| Midpoint | `x = m + 1/2` |
| Inexact, above the midpoint | `m + 1/2 < x < m + 1` |

`ExtendedRep` applies the same relation to the existing mantissa, round bit and
sticky bit record. It does not require that the record name a unique rational.
The operation data remain separate from the represented value and its laws.

The common nearest-even theorem encloses every represented rational between the
actual rounded mantissa minus and plus one half. The rounded natural is adjacent
to the truncated mantissa, and midpoint rounding returns an even natural.
Integer lower and upper bounds are preserved. Scaling by any nonnegative
rational unit uses Mathlib's absolute value and ordered-field laws; it does not
introduce another absolute-value theory or assume a format-specific epsilon.

## Quotients and exponent changes

`quotientMantissa` names the existing quotient/remainder classification followed
by nearest-even rounding. A positive denominator gives the correct accuracy
relation to the exact rational quotient. This one representation proof supplies
the half-unit error and its scaled form. The source's natural-number inequalities,
exact-division result and adjacency theorem are retained as well.

`Floating.Observation.dyadicValue` remains the exact dyadic interpretation.
Left-shifting a natural mantissa while lowering its exponent preserves that
value. `decreaseExponent` therefore preserves value both when it shifts and when
the requested target is above the current exponent and nothing changes.

The `divCore` bridges use the target exponent and shifted numerator chosen by
the actual model. Before rounding, the interpreted quotient equals the original
exact dyadic quotient. The initial rounded value differs by at most half its
selected binary unit. The accuracy relation also represents the original
quotient in those selected units. These statements require a positive divisor.
They do not silently assume that subsequent normalization or packing is exact.

The arithmetic-core module retains two further facts needed by later operation
proofs. Successful nonnegative unpacking is either a signed zero or a positive
finite value. Aligning two positive operands to the minimum exponent preserves
their exact sum. For positive operands, the actual division core either uses an
exponent at or below the subnormal floor, or supplies the required significant
mantissa bits. No second floating operation or canonical-format predicate is
introduced here.

## Residual-bit shifts

The actual `extended >>> n` represents `x / 2^n` whenever `extended` represents
`x`. The proof retains both the round bit and sticky bit. Its mantissa is exactly
the original natural mantissa divided by `2^n`.

Shifting to a target exponent produces exponent `max e target`. Combining the
shift representation with the shared nearest-even theorem gives error at most
half the resulting binary unit. The rescaling identity connects that result to
the original represented value. A target below the current exponent causes no
shift; it is included in the theorem rather than excluded by a premise.

## Composition with the existing interval library

`Examples.FloatingRounding` gives `ExtendedRep` the existing `Relational.RelRep`
interface. `shiftSquare` runs the real residual-bit shift and denotes division
by the corresponding power of two. `roundSquare` returns the rational interval
centered at the actual rounded mantissa, with radius one half. Its preservation
proof is the public common rounding theorem.

The existing interval-square consumer then consumes that enclosure by ordinary
relational composition. The universal result encloses `(x / 2^n)^2` for every
related input, without selecting a supposedly exact point from an interval.
All endpoints here are exact rationals, as in the existing interval library.

The concrete boundary case starts with exact mantissa five, shifts once, and
rounds the midpoint `5/2` to two. It returns `[3/2, 5/2]`; interval squaring
returns `[9/4, 25/4]` and contains the exact square `25/4`. The enclosure claims
use the public composition laws in addition to checking the closed outputs.

Other retained source cases distinguish the two even-tie directions (`5/2` to
two and `7/2` to four), rounding `7/3` and `8/3`, both exponent-decrease branches,
an exact and a sticky-bit shift, classification of `2 + 1/2`, and the aligned
sum `25/2`. An additional below-target case exercises the no-shift branch.

## Scope and verification

Statement inspection covers natural versus rational division, positive divisor
premises, integer exponents, the exact tag alternatives, nonnegative scaling,
the direction of target shifts, and represented versus rounded values. The
connected examples establish usable inputs and consume public preservation laws.
They use kernel-checked proofs and ordinary small computations; there is no
generated exhaustive proof graph or native-evaluation substitution.
