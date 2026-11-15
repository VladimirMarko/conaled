# Exact decimal numeral realizations

The available official extraction has `integer` at original `LINE 1043`, physical
line 157, and `fraction` at original `LINE 1048`, physical line 159 of
`part0/chap1.hs`. The book PDF/full text was not available for a fresh quotation.
The source's historical completion judgment does not establish conaled integration.

## Existing owners and actual execution

`Applications.Numerals.Decimal` uses standard Lists, natural numbers and rationals.
`integer` executes the literal left fold `10*n+d`, starting at zero. It proves
an invariant for every initial natural accumulator and every natural-entry list:

```
foldl shiftl seed digits = seed * 10^length + positionalValue digits
```

The positional specification reuses Mathlib's `Nat.ofDigits` on reversed input,
because that interface reads least-significant digits first. A separate theorem
connects this specification to the source independent indexed sum assigning
exponent zero to the last input digit. The proper-digit bound reuses
`Nat.ofDigits_lt_base_pow_length`; it does not reimplement a digit foundation.

`fractionFold` executes the literal right fold `(d+x)/10` over exact rationals.
`fractionParts` is a separate actual right fold producing an unreduced numerator
and denominator. Its result is precisely `(positionalValue digits, 10^length)`.
The denominator is always positive, even for an empty digit list.

`decodeParts` gives pairs their total rational quotient. Its update law is proved
only for positive denominators. `SquareKit.ListFusion.foldr_reachable` then proves
that the whole pair-producing execution decodes to the rational fold. The invariant
holds initially at `(0,1)` and survives multiplication of the denominator by ten.
The checked zero-denominator counterexample shows why this condition matters:
totalized rational division does not supply a commuting update on every raw pair.

The source `fractionRat` uses `mkRat`. The new `decodeParts_eq_mkRat` theorem retains
that exact normalized-rational observation while making the pair interpretation
available through the existing representation-square interface. `fractionPartsSquare`
and `decodeSquare` compose using `Squares.compose`; no new square or arithmetic
framework is introduced.

## Independent parallel realization

`Examples.Numerals.parallel_integer` connects the new public meaning to the existing
`Applications.Parallel.evaluatePolynomial`. For every `ScanPlan` and every natural
coefficient container of its shape:

```
evaluatePolynomial plan data 10 = integer (plan.shape.flatten data).reverse
```

The proof consumes `evaluatePolynomial_correct`, whose implementation computes a
scan of powers followed by a dot product, and the new positional bridge. The
coefficient-order polynomial specification is independent of both implementations.
The representation explicitly reverses low-to-high coefficients into source digit
order. The resulting exact square applies to arbitrary plans, including distinct
product and functor-composition recipes.

The actual scan output also feeds an exact quotient by `10^shape.size`.
`parallel_fraction` proves that this observation equals the literal fractional
right fold. The shape's length theorem justifies the denominator; it is not an
assumed agreement between an unrelated coefficient count and the input.

## Retained cases and boundaries

| Case | Checked intended observation |
|---|---|
| Empty digits | Integer 0, rational fraction 0, pair `(0,1)` |
| `[2,7,1,8]` | Integer 2718; initial accumulator 42 produces 422718 |
| `[1,4,8,4,9,3]` | Integer 148493 and exact fraction `148493/1000000` |
| `[1,2,5]` | Unreduced pair `(125,1000)` and exact fraction `1/8` |
| Improper `[10]` | Fraction 1 and false proper-digit premise |
| Leading zero `[0,1,2,5]` | Integer 125, pair `(125,10000)`, fraction `1/80` |
| Any all-zero list | Fraction 0 while the pair denominator remains `10^length` |
| Zero denominator outside the invariant | The proposed unrestricted pair-step decoding law fails |
| Four coefficients `[8,1,7,2]` | Balanced and composed scan recipes both produce integer 2718; fractional observation is `1359/5000` |

Value refinement requires no proper-digit assumption. The integer bound and strict
rational upper bound require every digit to be below ten. Leading zeros preserve
integer value but divide the fractional value by ten; they are not erased from
fractional scale or denominator observations.

These are exact Nat/Rat claims. Lean natural numbers and integers are unbounded;
the source `Nat = Int` synonym does not prove a bounded machine execution cannot
overflow. No Float/Float32 algebra, rounding, comparison policy, native runtime,
allocation, arithmetic bit complexity, or partial/infinite execution theorem follows
from this slice. In particular, the rational strict `<1` theorem must not be
transferred to a rounded floating fold. Those source families remain separately
tracked, as do the rest of Chapter 1 and the book. The complete queens-16 numerical
proof and its generated artifacts remain excluded.

## Validation boundary

The modules enter the ordinary public import closure through `Examples.Numerals`.
Focused elaboration, statement inspection, and declaration correspondence support
development review. Integration acceptance still requires the exact candidate's
normal full build, exhaustive proof audit, final candidate verification and both
independent Standards and Spec outcomes in the existing workflow.
