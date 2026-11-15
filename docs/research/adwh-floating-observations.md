# Floating observations and algebraic limits

This local 1012 adaptation selects twenty finite-observation declarations from
checkpoint 335's `ADWH.Chapter01.NumeralsFloating` and all twenty-six declarations
from `ADWH.Chapter01.FloatingAlgebraLimits`. The accompanying
`adwh-floating-observations-provenance.tsv` records all 46 exact source identities,
hashes and destinations. The remaining numeral executor, residual observer,
rounding and uniform-error developments are separate obligations. Neither this
slice nor its finite witnesses close Chapter 1.

## Existing owners and exact meaning

`Floating.Observation` interprets the actual pinned Lean logical `Float` and
`Float32` models. It uses the existing `toModel.unpack` operation. Core `Dyadic`
owns exact dyadic arithmetic: `dyadicValue m e` observes
`Dyadic.ofIntWithPrec (m : Int) (-e)` as a rational. The negative precision is
intentional. `dyadicValue_eq` proves the value is `m * 2^e`, and the positive and
negative exponent theorems recover both equations of the supplied source.
There is no second dyadic datatype, exponent theory, or floating algebra class.

The observation has the following exact domain:

| Unpacked model value | Rational observation |
|---|---|
| Either signed zero | `some 0` |
| Finite signed mantissa and exponent | `some` of the signed rational `m * 2^e` |
| Either signed infinity | `none` |
| NaN | `none` |

Finite observations include subnormal values. Interpreting an unpacked finite
constructor needs no extra canonical-format hypothesis; a packing or rounding
roundtrip would require its own proof. Success is exactly `isFinite`, and failure
is exactly `isNaN` or `isInf`, for each actual format. The proper-digit theorems
cover all natural digits below ten. They make no exactness claim about arbitrary
natural-to-floating conversion.

Both signed zeros denote the same rational and satisfy floating `==`, while
remaining distinct under Lean propositional equality. The decoder is therefore
not injective even on finite inputs. The pinned logical model canonicalizes
NaNs; these statements do not preserve arbitrary native NaN payloads or signs.

## Executed algebraic boundaries

`Examples.FloatingAlgebraLimits` retains the supplied small kernel-checked
witnesses, using standard `List.foldl` and `List.foldr`. The actual operation
results are decoded before explaining their numerical difference.

| Case | Binary64 | Binary32 |
|---|---|---|
| Exact input `B` | `2^53` | `2^24` |
| `(B + 1) + (-B)` | Decodes to 0 | Decodes to 0 |
| `B + (1 + (-B))` | Decodes to 1 | Decodes to 1 |
| Left and right sum folds on `[B, 1, -B]` | 0 and 1 | 0 and 1 |
| `(B + 2) - 1` and `B - 0` | Both decode to `B` | Both decode to `B` |
| `(B + 2) - B` and `1 - 0` | Decode to 2 and 1 | Decode to 2 and 1 |

All displayed inputs are finite exact integers. The decoded differences prove
failure of unrestricted associativity and equality of these folds, using
congruence through the public decoder. The subtraction example proves failure
of the unrestricted comparison rearrangement
`x-y ≤ x'-y' ↔ x-x' ≤ y-y'`. Over exact rationals the two sum folds both return
one for every rational `B`, and both corresponding difference comparisons are
false. Existing associative-fold laws remain valid under their hypotheses.

The NaN examples show that raw floating `≤` is not reflexive on every value.
The signed-zero examples show failure of antisymmetry with respect to
propositional equality. These claims do not assert nontransitivity and do not
rule out an existing algorithm whose chosen relation requires only transitivity.
There is no new blanket order instance.

## Actual partial composition with interval analysis

`Floating.Intervals.observed` is an existing `Relational.RelRep` whose relation
holds precisely when a decoder returns the represented rational. Its
`successful` result representation relates `some interval` to the rationals
enclosed by that interval. In particular, `none` represents no rational.

`adapt` accepts an existing `RelSquare` over `IntervalAnalysis.representation`.
It decodes the input, creates a singleton rational interval on success, and runs
that consumer. The proof uses `singleton_contains` and the consumer's existing
preservation law. Exact success and rejection theorems retain the decoder's
domain. The release theorem also recovers a decoded input and its enclosure
from any successful returned interval. No arbitrary interval or zero is
substituted after rejection.

The concrete `squareConsumer` pairs the existing identity realization and
composes it with the existing `IntervalAnalysis.mulSquare`. Both `square64` and
`square32` use this same consumer. Whenever an input decodes to `q`, the returned
interval is exactly the singleton at `q*q`, and hence contains that value.
`Examples.FloatingIntervals` connects the public generic laws to both formats:

- `-1.5` decodes to `-3/2` and yields the singleton at `9/4`.
- `0.125` decodes to `1/8` and yields the singleton at `1/64`.
- Binary32 bit pattern one decodes to the least positive subnormal, `2^(-149)`.
- Both signed zeros yield the singleton at zero.
- NaN and both infinities remain `none` through the whole composition.

These are functions of the represented binary rational. They do not assert
that rounded floating multiplication is exact, or enclose an intended decimal
input before its conversion error is accounted for. A later numeral certificate
can supply a rational interval around its decoded result and reuse the same
interval consumer.

## Statement review, trust and continuing work

The selected floating API operations have explicit logical model definitions.
The closed witnesses use `decide +kernel`; they do not replace proof with native
evaluation or generated exhaustive graphs. No global heartbeat increase is
needed for this development. Axiom cleanliness alone would not establish an
opaque external operation's intended behavior, so no opaque cross-format cast
or decomposition shortcut is used.

Statement inspection checks the actual model types, Boolean and propositional
domain formulations, natural proper-digit premise, source-compatible exponent
equations, standard fold argument order, equality distinctions, successful
result relation and composed rational specification. The examples separately
establish usable inputs and consume the public preservation results.
