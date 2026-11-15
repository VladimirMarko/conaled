# Steepness: measured short-circuiting and shared tuple demand

## Source and ownership

The selected source is `adwh-checkpoint-335-compact-recovery`, member
`project/adwh-lean/ADWH/Chapter01/SteepCosts.lean`, SHA-256
`4c2b647c723f24564fd88f6bb9d4883a58bd112ed768ae1949c59c54cab0b963`.
The [declaration ledger](adwh-steepness-costs-provenance.tsv) accounts for all
27 named declarations. Its bytes agree with the predecessor inventory.

The available extracted official `part0/chap1.hs` has SHA-256
`51bc05fb7aa76ae5fdbb8cdb4e8d8f99d134e1d21dd7a0fff137776268f82711`.
Original LINE1178 defines direct steepness; LINE1189 gives the tupled helper;
LINE1196 compares their Boolean observations. The supplied chapter ledger
places Exercise/Answer 1.21 at printed pages 19 and 23. Those are retained
source coordinates: the original PDF is absent from the recovery payload.

`Applications.Resources.Steepness` uses the existing `Resources.Measured`
value/observation pair. `Sequences.Steepness.Steep` remains the independent
mathematical specification: for every decomposition `front ++ x :: back`,
`back.sum < x`. The new execution laws connect to the existing direct and
tupled decisions and then to that specification. No second steepness predicate,
writer abstraction, list type, or general lazy-language semantics is added.

The reusable measured integer sum and its value/work laws are public. The
prepared sum and delayed Boolean machinery are private to this module. This
keeps the observation contract small while preserving the explicit execution
that justifies its costs. The two decision squares use the established
`Resources.erasureSquare`; both expose ordinary `steep` as their specification.

## Explicit operation interpretation

One observed list constructor, one integer addition, and one integer comparison
each cost one unit. All integers are unbounded mathematical values. Counts
belong to actual value-producing definitions in this model, not a formula
attached after running an unrelated uninstrumented decision.

`sumRun` recursively observes the finite list. An empty sum costs one
constructor test; a cons adds one constructor observation and one addition.
Its exact result is `(xs.sum, 2 * xs.length + 1)`.

`naive` observes the current list constructor, sums the proper suffix, and
compares that sum with the head. It demands the suffix Boolean only if this
comparison succeeds. A failed comparison returns immediately. Consequently
its nonempty recurrence charges two units for the current constructor and
comparison, the suffix sum's work, and, only on success, the recursive Boolean
work. Empty input returns true with charge one.

The tupled interpretation separates preparing a sum from observing a Boolean.
Preparing a finite suffix traverses it once and makes its Boolean observation
available as a delayed component sharing the prepared sum. It does not force
that Boolean. Observation charges one comparison and continues only when the
comparison succeeds. The public `tupled` operation demands the Boolean alone;
it neither computes nor charges the unused outermost sum.

These are local source-equation demand rules. Closure construction, memory
allocation, compiler optimization, native execution time, garbage collection,
peak memory and integer bit complexity are outside this charge model. It is
not a proof of Lean's evaluation behavior or a whole-language GHC semantics.
The value equality does not establish those rules; the separate instrumented
definitions and proofs establish the claimed model.

## Exact bounds and witnesses

Let `n = xs.length`.

| Public result | Claim and hypotheses |
|---|---|
| `sumRun_value`, `sumRun_work` | Ordinary list sum and exact work `2n + 1`. |
| `naive_value`, `naive_correct` | Direct measured Boolean equals the existing decision, and is true exactly when the independent `Steep xs` holds. |
| `naive_work_le` | Every input uses at most `(n + 1)²` work. |
| `naive_work_eq_of_steep` | `Steep xs` implies exact work `(n + 1)²`, including the empty input. |
| `tupled_value`, `tupled_correct` | Tupled measured Boolean equals the existing tupled decision, and is true exactly when `Steep xs` holds. |
| `tupled_eq_naive_value` | The two decisions agree for every input; no equality of charges is inferred. |
| `tupled_work_cons_le`, `tupled_work_le` | Nonempty input uses at most `3n`; the all-input bound is `3n + 1`. |
| `tupled_work_eq_of_steep` | A nonempty steep input uses exactly `3n`. |
| `naive_cons_failure`, `tupled_cons_failure` | If the head is at most the proper suffix sum, both executions return false with work `2 * suffix.length + 3`; later Boolean demand is omitted. |
| `worstInput_length`, `worstInput_steep` | The explicit family has every requested finite length and satisfies the independent suffix specification. |
| `naive_worstInput_work`, `tupled_worstInput_work` | Direct charge `(n + 1)²` at length `n`; tupled charge `3(n + 1)` on the nonempty family at length `n + 1`. |
| `naive_quadratic_witness` | Every length has an actual input whose direct measured work is at least `n²`. |

The witness is defined by a short recurrence: start with the empty list and
prepend the preceding list's sum plus one. Its correctness and work are proved
by induction. No generated table of large cases is required. Since its integer
entries grow with length, the unit-arithmetic result does not imply a bound
on bit operations. The statements expose exact natural bounds and witnesses;
this slice adds no separate asymptotic notation or new asymptotic framework.

The source's successful-input premises and witness conclusion were phrased
using the Boolean decision. The adapted exact-work theorems take the existing
independent `Steep` predicate, and `worstInput_steep` proves that predicate.
`Sequences.Steepness.steep_correct` preserves the equivalence to the source
formulation. This makes the public mathematical premise explicit.

## Actual producer and consumer composition

`Examples.SteepnessCosts.measuredDecision` lifts an existing measured decision
square over an already measured sequence, using `Resources.bind` to retain its
incoming charge. `flattenDecision` composes this with the existing
`Resources.TreeFlattening.stackSquare`. The checker receives the list produced
by that traversal; the implementation does not substitute a decoded expected
list or rerun the producer to supply its argument.

`flattenDecision_value` proves the arbitrary-input semantic result for any
supplied checker square. `flattenDecision_work` proves exact work: the existing
pending-tree traversal count plus its terminal observation, followed by the
checker charge on the ordered fringe. Its specialization with either decision
proves that the result is true exactly when that fringe is steep.
`flatten_decisions_agree` retains agreement after composition, while
`flatten_tupled_work_le` combines the producer's exact count with the tupled
bound. The hypotheses do not require valid tree caches: this existing
flattening producer ignores cache values.

The checked composition lives in `Examples`, which already holds universal
cross-application theorems. It does not require broadening the resource or
tree-flattening interfaces.

## Checked cases and development obligations

The original source cases were already reducible. The missing development
connection was a conaled resource execution linked to the independent suffix
specification, followed by a real measured producer/consumer composition.
The expected work values were calculated from the source recurrences before
building those connections. The retained cases use public correctness, exact
work and first-failure theorems; the composed cases also use the general
composition laws.

| Checked case | Independent expectation | Connection exercised |
|---|---|---|
| `signed_sum` | `[-3,0,8]` sums to 5 with work 7. | Both public sum value/work laws. |
| `naive_three`, `tupled_three` | `[4,2,1]` is steep; charges are 16 and 9. | Independent specification correctness and exact successful-input costs. |
| `naive_empty`, `tupled_empty`, `empty_needs_constant` | Both empty results are `(true,1)`; `work <= 3n` is false here. | Terminal source rules and the necessity of the nonempty condition. |
| `naive_singleton`, `tupled_singleton` | `[1]` returns true at work 4 and 3. | Exact cost laws, including terminal direct recursion. |
| `zero_fails`, `negative_fails` | Zero and negative singleton values return false at work 3. | Public first-failure laws over mathematical integers. |
| `first_failure` | `[0,100,200]` returns false at work 7 for both decisions. | Later Boolean observations are skipped. |
| `tie_fails`, `quadratic_equality_needs_steep` | `[3,2,1]` fails the strict head comparison at work 7, not 16. | Strictness and substantive successful-input premise. |
| `no_unconditional_strict_improvement` | Equal work on the first-failure case refutes strict improvement for every input. | Both public failure results. |
| `witnessed_comparison` | Every nonempty length has an independent steep witness attaining both exact charges. | Source witness family, its length/specification and both actual execution laws. |
| `produced_naive`, `produced_tupled` | A three-leaf forest produces `[4,2,1]` at work 6; complete charges are 22 and 15. | Actual square composition and general value/work laws. |
| `produced_failure` | The same shape produces `[0,100,200]`; both complete results are `(false,13)`. | Short-circuit cost retained after actual production. |
| `produced_empty` | Empty forest construction costs one, then either empty decision costs one. | Composition retains both terminal observations. |

## Statement review and remaining scope

The independent quantifiers cover every finite suffix decomposition, including
the empty suffix at the last element. Strict comparison therefore requires a
positive last element. No premise restricts arbitrary inputs to positive
numbers. Failure branches use `head <= suffix.sum`, exactly the complement of
the success test. The work bounds concern the second projection of actual
measured executions; their correctness theorems concern the first projection.

Exact direct work assumes a satisfiable independent predicate, witnessed at
every finite length. Exact tupled `3n` work additionally requires nonempty
input; the counterexample at the empty list retains that boundary. First-head
failure shows why universal strict improvement would be false. Private demand
helpers expose no assumption equivalent to the desired whole-list cost bound:
their local comparison and preparation counts are proved from the definitions.

The representation squares erase only the work observation. Composition keeps
the actual producer result and adds the actual consumer work; it does not
derive cost equality from semantic agreement. The preserved producer theorem
identifies the ordered fringe and the complete pending-tree charge.

Elaborated-type inspection confirms integer list values, natural work counts,
Boolean decisions, the existing `Sequences.Steepness.Steep` premises, and the
arbitrary checker/forest quantifiers in the composition laws. In particular,
the measured representations decode the Boolean first projection, while the
work laws observe the natural second projection.

This slice does not cover other structural or fusion list costs, complete
collapse demand and append costs, general partial/infinite-list semantics,
productive streams, positional numerals, or Float/Float32 error analysis. It
does not change the exclusion of the entire large queens numerical proof.
Full candidate build/audit and independent Standards and Spec review remain
the acceptance gates; focused checks are development evidence only.
