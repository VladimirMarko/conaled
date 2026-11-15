# Staged unary-comparison cost model

This is cross-cutting preparation for the VFA formalization. It is outside the
integrated conaled source tree and does not close Perm, SearchTree, Extract,
Trie, or any other chapter. See `VALIDATION.md` for the exact checked input and
compiler result.

## Source issue and model

The pinned VFA 2.1 source describes unary comparison costs in terms of the
difference between operands at `Extract.v:65–66` and
`SearchTree.v:1290–1292`. Those paragraphs require qualification. The adjacent
source discussion concerns Coq's unary representation; it supplies no cost
theorem about Lean's native `Nat`, compiled machine code, or elapsed time.
`RESOURCE-AND-EXECUTION-OBLIGATIONS.md` records the wider source audit.

`unaryLE` explicitly compares two unary constructor shapes: zero on the left
returns true; a successor on the left and zero on the right returns false;
two successors recurse on their predecessors. `unaryLERun` follows exactly
that recursion and charges **one unit for each call**, including the terminal
call. A simultaneous constructor-pattern comparison is one counted event.
Bookkeeping additions and proof execution are not charged. These are chosen
structural observations, not a machine-time adequacy claim.

The exact number of calls is `min n m + 1`. In particular, comparing equal
values `n` and `n` takes `n + 1` calls in this model, despite their difference
being zero. This refutes every finite bound depending only on absolute operand
difference, not merely a particular linear formula.

This model is for **less than or equal**. It is not silently identified with
Coq's `Nat.ltb`: identifying a strict comparator would require pinning its
definition and accounting for any successor introduced by its implementation.
No such strict-comparison bridge is claimed here.

## Public claims and statement review

| Declaration | Intended statement and review |
|---|---|
| `unaryLE_eq_decide` | For every pair of naturals, the recursive Boolean equals Lean's decision of mathematical `n ≤ m`. The target is independent arithmetic semantics, not a restatement of the definition. |
| `unaryLERun_erases` | Projecting the measured value gives the actual unmeasured `unaryLE` algorithm for all inputs. Instrumentation does not change the answer. |
| `unaryLERun_true_iff` | The measured Boolean is true exactly when `n ≤ m`; both directions are proved. |
| `unaryLERun_steps` | For every pair, the charged count is exactly `min n m + 1`. Zero inputs include one terminal comparison; the assertion does not omit a base-case charge. |
| `unaryLERun_spec` | Combines the semantic result and exact count in one pair equality. It uses the separate erasure, arithmetic correctness, and count proofs. |
| `equal_inputs_steps` | Every equal-input comparison costs `n+1`, including `n=0`. This supplies concrete nonvacuous witnesses. |
| `no_difference_only_bound` | For each arbitrary function `bound : Nat → Nat`, there is no bound of all runs by `bound ((n-m)+(m-n))`. Both subtractions are natural truncated subtraction; their sum is absolute difference. Quantifier order lets the equal witness depend on `bound 0`; no bounded-input restriction is assumed. |
| `equal_inputs_beyond_threshold` | For every input threshold and cost budget, an equal pair at or above the threshold exceeds the budget. Excluding finitely many small operands does not repair the difference-only explanation. |
| `unaryLESquare` | Uses `Resources.erasureSquare` with paired natural inputs, the actual measured recursion, and its existing erasure theorem. The source representation decodes by `id`; the result decodes by `Prod.fst`. It adds no cost equality to the square contract. |
| `unaryLESquare_value` | A consumer of the shared square's `commutes` field obtains `decide (n ≤ m)` via `unaryLE_eq_decide`. The claim covers all natural inputs and checks the actual public adapter. |
| `compareBothWays` and `compareBothWays_value` | Two existing `Resources.bind` calls execute `n ≤ m` and then `m ≤ n`, preserve both answers in that order, and finish with zero-observation `Resources.pure`. The value proof consumes `Resources.bind_value`. There is no short circuit when the first answer is false. |
| `compareBothWays_spec` | Both comparisons execute, so their observations add: `(min n m + 1) + (min m n + 1)`. The theorem uses `unaryLERun_spec` and the existing bind/pure definitions, not a duplicate sequencing framework. Pair construction and binding carry no extra primitive charge in this model. |

All claims are unconditional statements about the displayed terminating
recursions and natural arithmetic. None assumes the conclusion, an impossible
representation invariant, an application-specific axiom, or a source admission.
`set_option autoImplicit false` keeps all domains explicit. No claims concern
physical allocation, bit complexity of Lean primitives, or kernel/compiler speed.

## Checked cases and their independent expectations

Before writing the general proof, the expected equal-three run was worked out
as comparisons of `(3,3)`, `(2,2)`, `(1,1)`, and `(0,0)`: true, four calls.
A zero operand terminates at the first comparison. For `(3,8)` and `(8,3)`,
three paired-successor steps lead to a terminal zero case, giving four calls
but opposite Boolean results. These expectations reveal both orientation and
off-by-one mistakes. The missing connection was the exact measured-count
theorem; no syntax/import failure was used as evidence of a mathematical gap.

The file retains named examples for `(0,7)`, `(7,0)`, `(3,3)`, `(3,8)`, and
`(8,3)`, each proved through `unaryLERun_spec`. The 1,000-versus-1,000 example
uses `equal_inputs_steps` to obtain 1,001 calls, and another checked example
connects that result to zero operand difference. No example uses `native_decide`.

The adapter follow-up begins from the independently worked cases already
established above: the square at `(8,3)` must return false; comparing `(3,8)`
and then `(8,3)` must return `(true,false)` with `4+4=8` charged calls. The
previous draft lacked the checked connection to conaled's public resource
interfaces, not the underlying arithmetic result. `example_square_strictly_greater`
now consumes `unaryLESquare_value`; `example_composed_directions` consumes
`compareBothWays_spec`. The differing Boolean answers check their orientation,
and the total checks that both executions are charged.

## Checked resource interface and remaining integration

The initial draft used `Bool × Nat` because the permitted cached imports did
not yet include `Applications.Resources.Measured`. The bounded follow-up
authorizes a focused build of that existing module and its `Workload` and
`Potential` companions in the main checkout. It preserves the independent
candidate-validation checkout and all project sources and dependency pins.

The staged file now imports `Applications.Resources.Measured`, uses
`Resources.Measured Bool Nat` as the definitionally identical result type,
packages erasure through `Resources.erasureSquare`, and composes the client
through the existing `Resources.bind`/`pure`. It uses the existing resource
modules' legacy import style: Lean 4.35 rejects importing their non-`module`
interface from a file marked `module`. All declarations remain public. The
original recursive bodies, mathematical theorems and checked cases are
unchanged. The adapter does not
pretend that equal values imply equal costs, or add a native-runtime claim.
Exact focused-check evidence and input hashes are in `VALIDATION.md`.

Before integrated acceptance, place the reusable theory and meaningful
examples appropriately, connect the VFA coverage ledger, include public
imports and exhaustive proof-audit coverage, and complete the required
candidate validation and independent Standards/Spec review. The follow-up
is cross-cutting preparation; it implements no Sort algorithm and accepts no
chapter. A successful standalone compile does not replace those gates.
