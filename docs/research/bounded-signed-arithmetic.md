# Bounded signed arithmetic for one motion step

Issue [#538](https://github.com/VladimirMarko/conaled/issues/538) adds a fixed-point
realization of the arithmetic in
[RationalMotion](../../Applications/Orbifold/RationalMotion.lean) and its
[admission and error-budget calculations](../../Applications/Orbifold/CheckedMotion.lean).
The evaluator rounds and checks the range after each primitive. Its theorem
relates the resulting enclosure to the exact rational formula. It does not
establish a bounded-precision trajectory theorem.

## Frozen workload and representation

The source workload is `RationalMotion.step` together with `CheckedMotion.budget`
and `CheckedMotion.Admissible`. The coordinate operations are:

| Calculation | Required operations |
| --- | --- |
| Complex velocity `frame * control.velocity` | Four signed products, subtraction, addition |
| Position norm square and gap `1 - normSq position` | Signed squares, addition, subtraction |
| Coefficient `-2 / gap` | Negation and guarded division |
| Frame derivative | Conjugation, two complex products, coefficient scaling, angular scaling of the rotated frame, addition |
| Euler update | Duration scaling and coordinate addition for position and frame |
| Budget `(1 + 13*d)*e + 39*d²` | Addition and signed multiplication |
| Admission | Velocity/frame/post-step norm squares; absolute angular value; nonnegative error; position absolute-coordinate sum plus error and half-duration; comparisons |

The duration is nonnegative in the existing `Tick` type. Conjugation and rotation
use negation and coordinate permutation. The bounded admission function checks
every predicate of `CheckedMotion.Admissible`; its soundness theorem takes the
existing `Tick`, so it retains that duration hypothesis.

The chosen scalar stores an integer tick in `[-65536, 65536]` with decoder
`tick / 256`. Thus its real range is `[-256, 256]`, and its quantum is `1/256`.
These constants are an explicit workload choice, not a universal precision
claim. The nonzero motion fixture, constants 13 and 39, and its intermediate
coefficient and products fit this range. Other inputs can be rejected even when
their final exact answer would fit.

A `Box` stores three such scalars: the selected value, lower endpoint, and upper
endpoint. Construction checks `lower ≤ selected ≤ upper`. Input uncertainty is
represented by the endpoints. Every theorem quantifies over every real input in
those intervals; a selected center alone is insufficient evidence of admission.

## Comparison with the pinned floating model

The repository pins Lean `v4.35.0` in [lean-toolchain](../../lean-toolchain).
[Floating.Operations](../../Applications/Floating/Operations.lean) proves
`unpacked_add_bounds` for nonnegative operands whose sum is at most 10, and
`unpacked_div_ten_bounds` for a nonnegative numerator at most 10 and denominator
exactly 10. Its `add64_bounds`, `add32_bounds`, `float_div_ten_bounds`, and
`float32_div_ten_bounds` discharge the actual pinned Float/Float32 model obligations
for those decimal consumers, including their zero and subnormal cases.

Extending that route to this workload would need signed cancellation, signed
multiplication, general separated division, and their format-dependent packing
proofs. The present implementation does not apply the nonnegative lemmas to
signed inputs. It reuses Mathlib's integer-division/floor correspondence and the
repository's `NumericalError` composition interface; it gives the new operations
their own proofs. Existing floating, numeral, and rational-interval files are
unchanged.

Exact unbounded rational evaluation would preserve formulas but would not bound
denominator growth. A bounded rational representation would also require a
choice of denominator bound and a reduction/rounding policy. Fixed scale makes
each primitive's storage and intermediate limits explicit, and permits the same
outward certificate throughout the expression evaluator. No IEEE semantics are
claimed for this choice.

## Operations, rounding, and rejection

[Core](../../Applications/FixedPoint/Core.lean) defines integer `down n d = n / d`
and `up n d = -((-n) / d)`. Their real bounds are proved for positive integer
`d`; selection rounds toward negative infinity. The
[primitive operations](../../Applications/FixedPoint/Intervals.lean) use:

| Primitive | Selected tick | Outward endpoints |
| --- | --- | --- |
| Add | `a + b` | Lower sum, upper sum |
| Subtract | Add the negated second box | Negation reverses endpoints |
| Multiply | `down (a*b) 256` | Down of the minimum four endpoint products; up of the maximum |
| Divide with positive denominator interval | `down (a*256) b` | Minimum of four downward endpoint quotients; maximum of four upward quotients |
| Divide with negative denominator interval | Negate both input boxes, then positive division | Same normalization |
| Absolute value for admission | Absolute selected tick | Zero lower bound; maximum absolute endpoint upper bound |

Division rejects every interval containing zero. `divide_separated` proves that
success separates **every** possible denominator by at least `1/256`. It does
not just test the selected denominator. Every primitive also rejects if its
computed endpoints or selected value cannot form a bounded ordered box. In
particular, overflow is rejection, with no wrapping or saturation.

Addition and subtraction have exact selected-value equations. Multiplication
has local selected-value error at most one quantum; division has error strictly
less than one quantum. These are local errors relative to the decoded selected
operands. The enclosure theorems separately account for all input uncertainty.
`Expr.sound` composes those enclosures through every node of a finite expression;
`Expr.error` bounds its selected result against the exact expression meaning.

There is one zero tick, and the decoder is injective. There is no exponent,
signed-zero bit, subnormal class, infinity, or NaN. Positive products below one
quantum round to zero. Negative products between minus one quantum and zero
round to minus one tick. Checked examples retain both cases, so the floor rule
is observable at underflow rather than silently replaced by truncation.

## Computed certificates and resources

The error certificate is the integer
`max(selected - lower, upper - selected)`. Its real interpretation is that
integer divided by 256. `certificate_sound` proves its absolute-error bound for
every enclosed exact value, and `radius_range` proves it is nonnegative and at
most 131072 ticks. Certificate computation performs exact integer subtraction
and maximum; it never rounds a certificate inward.

| Quantity | Proved bound |
| --- | --- |
| Each stored scalar | Absolute tick at most 65536; injective code into `Fin 131073` |
| One box | Three such scalars; selected value between endpoints |
| Sum or difference intermediate | Between -131072 and 131072 |
| Product intermediate | Absolute value at most 4294967296 |
| Scaled division numerator | Absolute value at most 16777216 |
| Normalized division denominator | From 1 through 65536 |
| Down/up product quotient | Absolute value at most 4294967297 |
| Down/up division quotient | Absolute value at most 16777217 |
| Certificate radius | From 0 through 131072 |

The quotient bounds deliberately follow the general `|quotient| ≤ |numerator|+1`
lemma; they are conservative. Negative-denominator normalization produces valid
bounded scalars before using the same bounds. Min/max only select existing
intermediates. The finite scalar code fits in 18 bits, so three scalar codes fit
in 54 bits; the implementation uses Lean `Int`, not a packed 54-bit machine
layout. Proof fields are erased. The integer magnitude bounds do not measure
allocator overhead, generated machine instructions, or division latency.
Expression size and recursion depth remain input-dependent. There is no global
bound on the number of nodes in an arbitrary expression, and no stack or timing
theorem. The fixed motion expressions are finite executable clients.

## Checked consumers

[BoundedArithmetic](../../Examples/BoundedArithmetic.lean) retains cancellation,
signed multiplication, both underflow directions, positive and negative small
denominators, zero and uncertain-zero rejection, addition/multiplication/division
overflow, and a threshold case where the center passes but the upper endpoint
fails.

Its `executed_composition` connects two executed multiplications to
`NumericalError.compose`. The ideal stages multiply by `3/2` and `-1/2`;
the selected stages apply the proved floor map. The first domain is `[-1,1]`
and the second is `[-2,2]`. Separate proofs admit the exact and rounded first
outputs. The second stage sensitivity is `1/2`, with local error `1/256` for
each stage. Starting from one tick, the executed output is minus one tick;
the exact result is `-3/1024`, and the composition theorem gives bound `3/512`.

[BoundedMotionArithmetic](../../Examples/BoundedMotionArithmetic.lean) builds the
entire coordinate field, Euler update, budget, and admission formulas from
primitive expressions. `step_meaning` and `budget_meaning` identify their exact
meanings with the existing rational definitions. The fixture starts at
`(1/8,-1/8)` with frame `(1/2,-1/4)`, moves with control `(-1/2,1/4)`, uses duration
`1/16`, and starts with error `1/256`. Executed selected ticks and enclosures are:

| Output | Selected | Lower | Upper |
| --- | ---: | ---: | ---: |
| Position real | 29 | 29 | 29 |
| Position imaginary | -28 | -28 | -28 |
| Frame real | 128 | 128 | 129 |
| Frame imaginary | -65 | -65 | -64 |
| Budget | 40 | 40 | 41 |

The exact frame coordinates are `1997/3968` and `-1001/3968`. The primitive
composition and computed certificates prove errors at most `1/256` for each.
The exact budget is `653/4096`, enclosed by `[40/256,41/256]`; its selected value
alone would underestimate it. The bounded admission checks accept this fixture.
A second fixture's position center passes its margin but its uncertain endpoint
causes rejection. `admitted_sound` proves that successful bounded checks imply
the complete existing rational `Admissible` predicate for any enclosed inputs.

The retained `#eval` observations exercise compiled Lean evaluation. Kernel
proofs establish the logical operation contracts and checked fixture equations;
those runtime observations are smoke checks, not a proof of Lean's code generator,
integer runtime, physical hardware, or IEEE conformance. A later trajectory
realization must propagate these arithmetic enclosures and budget upper bounds
through the existing motion stability/truncation result. That integration is
outside this arithmetic prerequisite.
