# Exact agreement of suspension event instruments

## Scope and expected observations, before compilation

This bounded local #10020 development slice connects the existing list-traced
machine to the existing Resources/FreeAddMonoid observer. It adds no evaluator,
event generator, transition rule, completion bound, cache-count assumption or
proof-limit change. Root owns the original cache-count client and full gates.

The required public contract is stated for any primitive type and parameters,
an arbitrary input `(config, prior)`, an output `(answer, events)`, and an actual
`Progress.Evaluates (tracedStep parameters) input output steps`. Observation at
that exact run length must return the same complete, memory-bearing answer,
and `prior ++ toList observedEvents = events`. An empty-prior specialization
then identifies the observer's event list directly with the traced result.

The connected client reuses `Examples.SuspensionPending.firstForce`, whose
thunk at address 0 contains literal 7 under the empty captured environment.
Its independently expected five transitions are:

1. Enter the stored body: `body 0`.
2. Evaluate the integer literal: `core`.
3. Memoize integer 7 before inner matching: `cacheWrite 0`.
4. Match the wildcard: `core`.
5. Deliver `matched []`: `core`.

The final memory is exactly `memoize memory 0 (atom (integer 7))`.
The supplied prior list `[referenceWrite 9, hit 4]` is intentionally nonempty
and distinguishable from all new events. The list instrument must retain this
prefix; the resource observer must contain only the five new events, in the
stated order. This arbitrary prior log does not assert an earlier execution
that produced the starting configuration.

## Implementation and statement review

Owned library: `Applications/Suspensions/TraceObservation.lean`.
Owned client: `Examples/SuspensionTraceObservation.lean`.

Public theorems in `Suspensions.Core.Observation`:

- `traced_evaluates_observe`: complete-answer equality and exact prior-prefix
  event equality, at the actual finite transition count.
- `traced_evaluates_observe_nil`: the corresponding empty-prior equality.

The proof inducts on the existing finite evaluation derivation. Each case
destructs the existing actual `transition` result, uses the precise append in
`tracedStep`, and sequences the existing observation using `workload_succ`,
`measuredAdvance_running`, `workload_finished` and list append associativity.
It preserves every answer class and the full memory by proving answer
equality; it does not erase faults or exceptions. No initial-state validity,
purity, typing, cache uniqueness, event count or termination premise is added
beyond the given actual finite run.

The client proves the five actual traced steps, consumes the public agreement
theorem, and cancels the explicit two-event prior prefix to expose exact new
event order. It does not independently reduce the resource observer.

## Validation status

The initial draft and the expectations above were saved before the first
focused compiler invocation. That first attempt, recorded as
`suspension-trace-observation-r1`, passed both targets with no proof correction
or retry: `Applications.Suspensions.TraceObservation` (177s) and
`Examples.SuspensionTraceObservation` (257s), 754 jobs in total, terminal exit 0.
The wrapper started at `2026-11-02T23:48:08.266123+00:00` and ended at
`2026-11-02T23:55:37.822647+00:00`.

The pinned offline Lean 4.35.0 check used the existing serialized focused
runner, one thread and unchanged default limits. All 26 recorded local source
and configuration inputs were byte-identical at queue, start and completion.
The recorded checkout HEAD was `0ebbf185d084b2cfe0b11501e8c7d4998932c16a`;
the two new files are identified by their own hashes below and await root's
commit. The log includes replayed module-system import warnings from existing
dependencies; neither new module failed. Owner session 73011 was polled through
its actual terminal exit 0 and is now closed. No restart or interruption occurred.

Terminal log and JSON were copied byte-for-byte from `active-validation` to
`session/validation` and checked for equality before this report was finalized.

| Artifact | SHA-256 |
| --- | --- |
| `Applications/Suspensions/TraceObservation.lean` | `69640c7683b3fe9c4212036e29e64bbb319f41beda7d339ecbafd1b1fca66487` |
| `Examples/SuspensionTraceObservation.lean` | `4119e90b2bbf2a51c49844a7343e99fc3507ce5742b906009097e524638e6ce1` |
| `session/validation/suspension-trace-observation-r1.json` | `6381183ca50ec59499b92d7b75e835a6f1a4e84690ad5e5fde7a26671c5acaf9` |
| `session/validation/suspension-trace-observation-r1.log` | `65aaf8af1caa6fae39d0e5902af8b24d40bfbd8b2ec934b55263ce111b81985e` |

Both owned source files are frozen after this focused success. No existing
source, entrypoint, Git index or ref was edited by this slice. Root owns the
unchanged `observe300 = 2` counterexample's consumption of this bridge, its
candidate capture and full gates. No whole-candidate acceptance or full-gate
result is claimed here.
