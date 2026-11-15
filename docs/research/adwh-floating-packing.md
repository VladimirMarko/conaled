# Actual floating packing and numerical preservation

This development adapts the 23 named declarations and four source cases in checkpoint 335's
`FloatingPacking`. The exact identities, hashes and destinations are recorded in
`adwh-floating-packing-provenance.tsv`. Two source helpers reuse the stronger
1015 positivity and nonnegative-unpacking results, leaving 21 model-specific
declarations in the packing domain. Pinned core continues to own all operation
data and packing execution; `Floating.Observation` owns exact rational meaning.

## The representation hypotheses

`Canonical format value` and `NoOverflow format value` are distinct propositions
about the existing `UnpackedFloat`. They do not introduce a new floating type.

| Unpacked value | Canonical | No overflow |
|---|---|---|
| Either signed zero | True | True |
| Finite signed mantissa/exponent | Exponent equals the format's target exponent | Biased exponent lies below the reserved infinity/NaN pattern |
| Infinity or NaN | False | False |

The canonical exponent equation implies the lower exponent bound and the
mantissa-width bound. A mantissa shorter than the normal width must use the
subnormal floor. These facts justify the actual core packer's implicit-bit and
mantissa-truncation branches. The exponent-bias identity connects its zero biased
exponent to the floor. Existing bit-vector extraction theorems are reused.

`unpack_pack` proves equality of the entire signed unpacked representation under
both predicates. The normal, subnormal and zero proofs retain the existing
packer and unpacker. `pack_numeric` then composes that equality with the existing
partial rational observation. Bit-pattern validity alone is not a substitute
for this numerical preservation theorem.

The converse canonicality statement applies to a **finite result of unpacking a
bit pattern**. It does not assert that every arbitrary finite constructor is
canonical. This corrects an overly broad sentence in the supplied source's
introduction while retaining its actual formal claim.

## Actual-format numerical bridges

The generic signed preservation theorem is independent of the later numeral
range. For the numeral application, a successful observation in [0,10] is either
zero or a positive finite value. The existing 1015 theorem supplies those cases.
A positive natural mantissa with dyadic value at most ten has exponent at most
three; this proves the source no-overflow facts for binary64 and binary32.

The resulting model-specific theorems refer to the actual `Float.Model.pack`
and `Float32.Model.pack` and their unpackers. They retain the canonical input
premise and derive the overflow bound from the observed range. They neither
change rounded arithmetic nor establish later normalization invariants.

## Composition with interval analysis

`Examples.FloatingPacking.representation` relates an ordinary unpacked value to
an independent rational when canonicality, no overflow and successful rational
observation hold. `packingSquare` executes the actual bit-vector pack; its
codomain observes that bit pattern with the actual unpacker and existing decoder.

`consume` composes this square with the existing `Floating.Intervals.adapt` and
any existing rational interval consumer. The result preserves successful output
and encloses the consumer's function of the original represented rational. The
square specialization returns the exact singleton at `q*q`. No arbitrary
rational is selected after rejection and no approximation is hidden in an
equality claim.

The four source cases use the public roundtrip results:

- Negative signed zero retains its sign in the unpacked representation.
- Binary64's least positive subnormal is `(mantissa 1, exponent −1074)`.
- Binary32's least positive subnormal is `(mantissa 1, exponent −149)`.
- Negative normal minus one is `(mantissa 2^52, exponent −52)` in binary64.

Independent observations identify the two subnormals as `2^-1074` and `2^-149`.
Their packed observations follow through the public preservation theorem. The
negative normal flows through the actual packing/observation/interval-square
composition and returns the singleton at one. Negative zero returns the
singleton at zero, while the separate representation theorem retains its sign.

Two small boundary cases explain the hypotheses. Binary32's arbitrary finite
constructor `(positive,1,0)` satisfies the overflow bound but is not canonical;
packing changes its observed value from one to `2^-149`. The canonical constructor
`(positive,2^23,105)` violates the overflow bound and its packed observation is
`none`. These do not refute preservation under the stated premises.

## Statement and acceptance boundaries

Statement inspection covers the actual format widths and operations, signed
versus numerical zero, finite constructor versus finite unpack result, strict
overflow inequality, canonical exponent equation, subnormal branches, the
positive-mantissa premise and optional observation domain. The connected client
retains those conditions in its input relation and uses the public preservation
laws. Small concrete cases are kernel checked; no exhaustive generated graph or
native-evaluation proof substitute is introduced.
