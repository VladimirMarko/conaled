# Uniform guarantees for actual floating numeral folds

This development adapts all eighteen named contracts from checkpoint 335's
`FloatingNumeralsUniform`. The exact source hash, line coordinates and local
destinations are in `adwh-floating-uniform-provenance.tsv`. The code belongs to
the existing `Numerals.Floating` owner and uses its literal right-fold executor,
partial rational observations, separate operation laws and certificate bounds.

## Actual arithmetic supplies the local laws

`stepLaws64` and `stepLaws32` specialize the existing `StepLaws` proposition to
the actual `operations64`/`operations32` data and `decode64`/`decode32` decoders.
The formatted addition and division-by-ten contracts from local 1019 supply
their operation fields; existing proper-digit observations supply exact natural
conversion. The existing zero-decoding theorems remain explicit arguments to
the generic proper-run and certificate results.

| Format | Addition error allowance | Division error allowance | Uniform envelope |
|---|---:|---:|---:|
| binary64 | `2^-50` | `2^-53` | `2^-52` |
| binary32 | `2^-21` | `2^-24` | `2^-23` |

For either row, with allowances `a` and `b` and envelope `u`, the exact rational
identity is `(10/9) * (a/10 + b) = u`. The generic propagation results then give
the finite-length bound

`u * (1 - 1 / 10^digits.length)`.

The new module specializes the existing induction and geometric calculation.
Operations, observation and arithmetic laws retain their separate interfaces.
Rational absolute value and the error-propagation framework keep their existing
owners.

## Constructed success and precise domains

For every finite list of proper decimal digits, the contracts construct
a successful certificate and observation of the actual floating fold. The
certificate has one recorded step per input digit. Every conversion, addition
and division has a finite observation, and `stagesFinite64`/`stagesFinite32`
transport this to the actual format's `isFinite` predicate.

The final observed rational lies in closed `[0,1]`. Its error relative to the
independent `Decimal.fractionRat` is bounded by both the finite-length expression
and `u`. The certificate's operation bound retains the finite-length expression.
The existing exact-fold/specification equality transports the numerical error
to `Decimal.fractionFold`, with coarse and length-sensitive statements.

The all-proper-list theorems require proper digits only. They construct the
successful run using the actual-format laws. The per-certificate
`observations64_bounds` and `observations32_bounds` refine any resulting
certificate with `StepBounds` for every recorded step; the existing observation
theorems identify those fields with the actual conversion, sum and quotient.

Closed bounds retain both relevant endpoints. Many nines can round to one;
small positive exact decimals can underflow to zero. The strict rational upper
bound and positivity of an exact rational are not assertions about the rounded
output. NaN/infinity observation failures and out-of-proper-domain examples keep
their existing contracts.

## Existing interval consumption

`certify64_all_digits` and `certify32_all_digits` target the existing checker at
the corresponding envelope. Their composition with `consume_isSome` constructs
successful existing consumer outputs. The generic actual-format consumer
theorems also reuse `Examples.FloatingNumeralBounds.proper_consume`, whose proof
combines the generic checker theorem with the existing release/soundness laws.

`decimalSquare64_all_digits` and `decimalSquare32_all_digits` use the existing
`decimalSquare64`/`decimalSquare32` and their soundness theorems. The returned
interval contains the square of the original exact decimal. The implementation
still encloses that decimal using the certificate's computed operation bound;
the requested tolerance controls acceptance and does not replace the computed
radius.

The connected cases retain the independent expectations:

| Input | Existing observed behavior | Connection to the new contracts |
|---|---|---|
| Empty list | Finite zero in both formats | Length-sensitive error bound is zero; consumer contains zero |
| `[1,2,5]` | Exact eighth in both formats | Finite-length bound and a consumer interval containing `1/64` |
| `[1]` | Observation differs from exact one tenth in both formats | Error bound and a consumer interval containing `1/100` |
| Seventeen binary64 nines; eight binary32 nines | Observed value is one while the exact decimal is below one | Closed range, finite-length error and original-decimal-square enclosure |
| Binary32 `replicate 45 0 ++ [1]` | Observed zero; exact value is positive `1/10^46` | Proper-digit premise, finite-length bound and enclosure of the exact positive square |

These cases reuse the named floating computations. Small exact decimal
calculations identify the intended square; the large concrete floating traces
are not regenerated. Existing tighter single-digit and underflow certificates
remain available. The uniform envelope is not claimed optimal.
