# Actual bounded floating operations

This development adapts the complete checkpoint335 `FloatingOperations.lean`
slice: fourteen named theorems and three source cases. The source SHA256 is
`9ba55e7bf4ceeafcfb9368e7515480fe037548b8fa20456e08aaf3c0a1c4c119`.
The exact declaration locations, block hashes and owners are recorded in
[the provenance table](adwh-floating-operations-provenance.tsv).

## Interfaces and separate obligations

`Floating.Operations.add64_bounds` and `add32_bounds` concern actual conversion
and addition. They take a proper decimal digit and a tail successfully decoded
in closed `[0,1]`, and return an actual successful observation in `[0,10]`.
Their absolute errors are bounded by `2^-50` and `2^-21`, respectively.
`divideTen64_bounds` and `divideTen32_bounds` take a successfully decoded input
in `[0,10]` and return an observation of the actual division in `[0,1]`, with
error bounds `2^-53` and `2^-24`.

Canonicality, alignment, rounding-unit bounds and absence of overflow are
internal obligations. The public callers do not supply an arithmetic epsilon
axiom or a normal-number restriction. The generic raw addition law retains
both input canonicality hypotheses because zero can return the other operand
unchanged. The raw division law obtains its own alignment from the actual
quotient/remainder core and needs no input canonicality hypothesis.

Closed range and error are separate facts. Integer endpoints are exact points
of the binary grid whenever its exponent is at most zero. The existing
nearest-even endpoint law then preserves the upper endpoint. This argument
belongs in `Floating.Rounding.Bounds`, alongside the complete raw rounding
contracts; its interval-only theorem keeps the weaker source hypotheses.

The strict magnitude companions extend `Floating.Rounding.Magnitude`. The
strict sum bound `sum ≤ 10 < 16` saves a precision bit relative to an inclusive
bound; division uses the inclusive `quotient ≤ 1`. The source's strict power
comparison helper is a direct use of Mathlib `zpow_lt_zpow_iff_right₀`, with
rational base two. The actual positive-add formula extends ArithmeticCore.
No second floating executor, dyadic meaning or absolute-value theory is added.

## Connected interval use

`Examples.FloatingOperations` executes the literal digit step
`(convert digit + tail) / 10`. The addition law constructs a finite sum in the
division law's domain. The existing `Numerals.FloatingError.Step` meanings
combine its independently observed residuals into a bound
`additionEps / 10 + divisionEps` against the exact rational `(digit + q) / 10`.

The example maps the actual successful decoder to an interval centered at its
observed value with that radius. It composes this interval with an existing
relational consumer and specializes to the existing interval square consumer.
The conclusion retains successful decoding and encloses the square of the
original rational step. A successful observation outside the stated input
domain does not certify the missing domain premises. Rejection remains `none`.

All four closed-endpoint source equalities, both least-subnormal divisions to
zero and both negative-zero divisions are retained. Their public-law
specializations keep the numeric and bit-level claims distinct. The existing
nonexact tenth value cases are reused; the connected square encloses exact
`1/100` despite the binary observations being unequal to exact one tenth.
The interval arithmetic is the existing exact rational four-corner enclosure;
it is not a claim about rounded multiplication or a sharp interval image.

## Scope

These results concern the pinned logical `Float` and `Float32` model. They do
not claim native, GHC or hardware correspondence. The actual-format StepLaws
instances and universal proper-numeral error/checker guarantees remain the
separate 1020 connection to the existing generic numeral bounds. The source is
supplied checkpoint335 Lean material; unavailable original textbook prose is
not inferred. Chapter 1 and the full book remain open. The entire queens-16
numerical proof is excluded.
