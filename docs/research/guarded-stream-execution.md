# Executing guarded stream bodies

Issue [#307](https://github.com/VladimirMarko/conaled/issues/307) connects the
[#302 compiler](modular-guarded-streams.md) to finite execution and compares
recomputation with retained prefixes. The existing syntax, guardedness test,
semantic solver, and independent triangular-number specification are unchanged.

## Operational boundary

`SquareKit/GuardedStreamExecution.lean` supplies `Execution`: constant,
coordinate parameter, earlier-reference, indexed unary operation, and binary
operation inputs. `Execution.Realizes` states their individual compatibility
with an existing `Meaning`. It contains no whole-program correctness field.
`eval` traverses the finite source body. `compiled_eval` proves it is the
function produced by the existing compiler at the executable target.

All six body forms are supported under these operational inputs. This is a
restricted operation interface: an arbitrary causal stream transformer need
not be expressible as an indexed coefficient operation. In particular,
`addLeft p` reads `p n` in addition to its coefficient argument. The concrete
`inputs` definition and its `inputs_realize` theorem expose that read.
Availability of parameter and reference coefficients is an assumption of the
generic execution interface. Supplying an arbitrary noncomputable Lean
function does not magically make it executable. The concrete Nat client uses
only executable list reads, constants, and addition.

A producer state is a finite list. Its next coefficient comes from evaluating
the body at the list's length, with stored coefficients available by lookup.
Out-of-range recursive lookups use a seed. `next_correct` proves the guard
makes this seed irrelevant when the stored prefix agrees with a fixed stream.
`step_agrees` retains the invariant, and `emitted_correct` identifies every
emitted prefix. These results require the guard and primitive realization
proofs, not a primitive realization of the entire stream.

`Progress.guarded_delivery` proves delivery of any requested finite number of
coefficients. Each transition is one finite body evaluation and append. Its
step count counts outputs; it does not count arithmetic or traversal work and
does not establish wall-clock latency. Compiler recursion, semantic fixed-point
uniqueness, and producer delivery remain separate results. `silent_control`
exhibits a machine that updates the same cache forever without emitting. The
original `.recur` guard rejection is retained.

## Retained earlier definitions

`Applications/GuardedStreams/Execution.lean` executes the original `onesBody`,
`sumsSource`, and `triangularBody`. It retains three prefixes. The sums body
reads the stored ones prefix; the triangular body reads the stored sums
prefix. Both references occur below a delay, so the previous prefixes suffice
for the next coordinate. No call to the semantic `compiledSums` function is
used to realize a retained reference.

`Valid` records agreement with the independent streams `1`, `n + 1`, and
`triangular n`, together with equal prefix lengths. `tick_equation` derives the
next values from actual source evaluation. `tick_valid`, `extend_valid`, and
`computed_prefix` then prove the invariant and independent result.
`compiled_prefix` identifies that result with the existing compiled solution.
The concrete `producer_delivery` theorem gives delivery of the complete
selected triangular prefix, not just its length or a success bit.

`Examples/GuardedStreamExecution.lean` also connects generic execution to the
existing `run` API and transports finite observations along its coefficient
interpretation. The Nat-to-`ZMod 2` sums case uses this theorem. Coefficient
interpretation does not preserve resource observations without additional
primitive cost laws; none are claimed here.

## Measured execution

`Applications/GuardedStreams/Measured.lean` instruments actual branches using
`Resources.Measured` and `Resources.bind`. Its three observations are:

- coefficient constants and additions, plus explicitly supplied parameter reads;
- inspected list cells in history lookup, length, append, and prefix copying;
- allocated list cells and explicit state headers.

The model does not count natural-number comparison/subtraction instructions,
closure allocation, output transport, bytes, or elapsed time. History lookup
charges each inspected cell. List length is traversed and charged rather than
assumed free. Appending rebuilds the old prefix and allocates a final cell;
copying a requested prefix charges its traversal and new cells. Constructor
local erasure theorems establish that measurement preserves the executed value.

`recompute n` allocates fresh state and executes all three definitions up to
`n`, then copies the output. At zero it returns the empty list directly.
`retain n s` measures the stored length, extends only the missing suffix, and
copies the requested output. Repeated and smaller demands leave the cache
unchanged but still pay lookup-length and output-copy work. The workload
consumes each output before its next request; it does not retain all outputs.
The retained workload constructs its cache header even when no positive
request follows. This is the explicit setup cost, not a surcharge inferred
from the desired comparison.

The workloads reuse `Resources.run`, its invariant and append laws, and
additive tariff transport. They need no new universal executor. The homogeneous
key/value storage from [#263](compositional-memoization.md) was inspected; these
three synchronized, growing prefixes use a different state shape. Their
resource composition still uses the same measured operations.

| Demands | Recompute: operations, inspections, allocations | Retain: operations, inspections, allocations |
| --- | --- | --- |
| `[4, 4]` | `(18, 140, 78)` | `(9, 78, 43)` |
| `[1]` | `(3, 1, 6)` | `(3, 1, 6)` |
| `[0]` | `(0, 0, 0)` | `(0, 0, 1)` |

These counts are Lean-checked executable specializations. A fresh prefix of
four uses three initial constants and six subsequent additions. Its 70 list
inspections are 18 length reads, 18 append visits, 30 history visits, and four
output-copy visits. Its 39 allocations are 30 appended list cells, four update
headers, one initial header, and four copied output cells. A repeated retained
request adds four length inspections, four copy inspections, and four copy
allocations. Thus retention saves each measured component on the repeated
workload, ties on the single short request, and loses on the zero case.

`live_after` proves retained cache size is `3 * max oldLength demand + 1`.
This counts one current cache and excludes caller-owned outputs and obsolete
persistent versions. If a caller keeps old versions, its live storage is larger.
There is no bounded-space claim for indefinite streams, universal speedup,
or low-level memory-reclamation theorem.

## Statement review and validation

| Claim family | Intended meaning and checked boundary |
| --- | --- |
| `eval_denote`, `eval_realizes`, `compiled_eval` | Structural execution agrees with semantic body evaluation and compilation; primitive compatibility is local. |
| `next_correct`, `agrees_append`, `step_agrees`, `emitted_correct` | Exact stored and emitted coefficients; guard, fixed equation, and prefix validity are explicit hypotheses. |
| `repeatHead_causal`, `repeatHead_not_indexed` | A causal head-reading operation requires more operational input than a current coefficient. |
| `delivery`, `producer_delivery`, `silent_control` | Finite delivery for the supplied productive machine; semantic existence alone does not make every machine productive. |
| `tick_equation`, validity and prefix results | Concrete reference reads use retained earlier-definition state and recover the independent triangular recurrence. |
| measured erasure and list-cost lemmas | Actual instrumented branches preserve values and charge the documented source events. |
| `retain_value`, `retain_valid`, `retain_length`, `repeated_state` | All finite demands, including zero, repeated, and smaller requests, preserve state validity and return the specified prefix. |
| workload composition and tariff transport | Existing additive resource laws apply; no relation between semantics and arbitrary tariffs is inferred. |
| `live_valid`, `live_after` | Current retained cache cells grow with maximum demand under the stated lifetime boundary. |
| `finite_interpretation` | Finite selected values commute with coefficient interpretation, independently of costs. |

The checked examples cover increasing, repeated, smaller, and zero demands;
sums and triangular earlier-reference reuse; indexed unary and parameter input;
Nat/mod-two observation transport; unguarded recurrence rejection; and silent
non-delivery. `scripts/GuardedStreamExecutionTest.lean` checks fresh and retained
outputs against the independent closed formula `i * (i + 1) / 2` as well as the
resource and operational controls. Formal additions require the issue's fresh
full source compilation and exhaustive proof audit, followed by independent
Standards and Spec review. Delivery evidence records the exact candidate and
commands rather than treating focused checks as acceptance.

## Consequences and limits

A causal semantic contract needs a separate executable primitive contract.
The current indexed coefficient interface is sufficient for this client; it
is not a claim that every causal operator has this implementation shape.
The checked `repeatHead_causal`/`repeatHead_not_indexed` control repeats the
input head: it is causal, but two streams agreeing at coordinate one and
differing at zero rule out this current-coefficient-only operation contract.
Extending to stateful causal primitives requires an explicit operational state
and invariant, with its own availability and work laws.

Retained reuse belongs to executable state, while its meaning remains an
ordinary stream prefix. Existing Progress and resource interfaces can express
both facts without replacing the compiler or imposing a common storage model.
More elaborate schedulers, bounded-storage windows, effectful coefficient
availability, and low-level allocation costs remain separate work. Any such
extension should retain exact selected-prefix observations and the explicit
lifetime and cost boundaries established here; #109/#235 own future scope.
