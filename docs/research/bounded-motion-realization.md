# Bounded motion realization

The second disk-motion executor uses the fixed-point arithmetic accepted in #538: scale 256, signed ticks in `[-65536,65536]`, floor-selected operations, and outward interval certificates. Its driver retains certificates for `Bounded.run`. The existing rational driver still certifies `Numerical.run` and retains its exact equivariance theorem.

The implementation is in [BoundedMotion](../../Applications/Orbifold/BoundedMotion/), with checked applications and executable comparisons in [Examples/BoundedMotion.lean](../../Examples/BoundedMotion.lean). The workload was frozen before integration at base `51160c785e523ba2881c74e508f3906d783231e6`.

## Executed arithmetic and error

Input conversion rejects coordinates, controls, errors, or durations that are outside the signed range or off the `1/256` grid. It does not round command time. Each accepted tick executes the existing position, frame, budget, and admission expression trees. The rounded output receives a separate integer domain check.

For output coordinate boxes with radii `r₁,…,r₄`, the local rounding allowance is `(r₁+r₂+r₃+r₄)/256`. `evaluate_roundoff` proves that this bounds the product norm of the actual selected state minus the exact Euler state. The stored error is the budget's upper endpoint plus those four radii. `checkedStep_correct` combines this allowance with the existing propagated input error and continuous truncation estimate. It proves both position/frame approximation to the continuous command endpoint and domain membership of the rounded output.

`checkedStep_mesh` and `run_mesh` provide a separate comparison with a successful rational Euler execution on the same mesh. Their recurrence multiplies the previous discrepancy by `1+13d` and adds actual rounding. It does not add the continuous truncation term. A comparison between different adaptively selected meshes must instead state which exact trajectory or mesh it uses.

Schedule success preserves every intermediate sample and the exact rational clock. Whole accepted intervals are committed; retries begin at the same incoming packet. On failure, the complete earlier event prefix remains in the report and the failing event remains pending. The event partition theorem retains the original C4 labels. Signed coordinate permutations implement relabeling exactly. Rounded execution is only approximately equivariant: conditional on successful executions in both representatives, `run_representative_bound` bounds the difference through the shared exact trajectory and both certified errors. It makes no promise that both searches choose the same subdivisions or have the same success status.

## Frozen workloads and separating cases

The primary arithmetic/performance packet has position `(1/8,-1/8)`, frame `(1/2,-1/4)`, and error `1/256`. It moves with control `(-1/2,1/4)` for `1/16`, relabels by one quarter turn, then turns at `1/2` for `1/64`. Both routes use the same event list, tolerances `1/4` and `1/2`, four search rounds, work fuel 128, and all four starting representatives. The rational route uses a 4096-bit packet guard.

The first bounded output retains the independent arithmetic oracle: position ticks `(29,-28)`, frame ticks `(128,-65)`, budget upper endpoint 41, and total coordinate radius 2. Its returned error is therefore 43 ticks. The selected budget value 40 would underestimate the exact budget and is never used as a conservative bound. The exact threshold 43/256 is accepted by a one-candidate search; 42/256 is rejected.

At tolerance `1/4`, starting representative zero, the bounded route commits the move and relabel, then rejects the turn. Its four turn candidates fail by accuracy, domain, domain, and precision respectively. The final committed clock is `1/16`, not the requested `5/64`. The rational route completes this word. The finer bounded schedules cannot silently round a duration below the grid. Conservative budget enclosures also need not improve monotonically as the mesh becomes finer.

The primary packet is an arithmetic fixture, not a claimed approximation to a valid Pose with error `1/256`: its frame norm is incompatible with that small error and the conformal frame scale. A separate exact origin Pose with frame `(1/2,0)` supplies the nonvacuous continuous-trajectory application. Its nonzero movement is proved through `checkedStep_correct`, with its incoming approximation premise discharged.

Retained cases cover empty and singleton prefixes, nonzero movement and turns, representative changes, the domain margin, insufficient tolerance, nongrid input, duration `1/512`, an out-of-range coordinate/control, work exhaustion, and a successful prefix followed by unsupported or unrepresentable input.

## Work, storage, and runtime

The model distinguishes attempted ticks from reserved work. Every rejected schedule retains its attempted-tick count, including its failing tick. A candidate reserves its planned tick count plus one search decision; a relabel reserves one unit. Reservations can include a suffix that was never executed.

Arithmetic accounting charges all output and admission expression trees for every attempted tick. The expression traversal bound includes failing nodes and excludes unvisited right subtrees, so the full tree charge is conservative. Conversion, integer guards, search/schedule work, and retained packet writes are separate categories. A boxed arithmetic node is a model unit; it is not a machine instruction or a uniform cost in bits. Rational and bounded costs must not be ranked from attempted ticks alone. Rational normalization and integer allocation remain runtime concerns.

Each bounded scalar has an injective code with 131073 possibilities, fitting in 18 bits. Each packet stores five such scalars. The report's scalar-slot count includes its final packet, every observation's incoming packet, each command result and all samples, counting repeated occurrences without assuming allocator sharing. The implementation uses Lean `Int` and lists, not packed words. Retained rational command durations, labels, counters, errors in attempt logs, and list structure are reported separately from coordinate scalar codes. The common request (initial packet, event word, tolerance, limits, and fuel) remains the same explicit input to both measurements; the retained-report counts do not include that caller-owned request or transient allocation. Constructor tags and allocator headers are not assigned a bit layout. Rational comparison storage sums signed numerator and denominator bit lengths of the corresponding retained coordinate/error slots.

Runtime observations use the pinned Lean evaluator under the repository's direnv shell, one CPU, and the shared build lock. The emitted timings include rendering the result summaries and are separate from the modeled charges. They establish no speedup, allocator bound, or bit-operation theorem.

## Matched observations

The checked evaluator emits these values for representatives 0 through 3. Error entries are returned conservative error budgets, not measured trajectory deviations. In particular, the arithmetic fixture does not discharge the physical-pose premise.

| Route and tolerance | Result and exact elapsed time | Returned error | Attempted ticks / reserved work | Retained scalar code bits | Metadata bits / list cells |
| --- | --- | --- | --- | --- | --- |
| Bounded, 1/4 | precision failure, 1/16 | 43/256 | 7 / 22 | 450 | 109 or 113 / 11 |
| Bounded, 1/2, representatives 0–1 | success, 5/64 | 23/64 | 2 / 5 | 720 | 107 / 9 |
| Bounded, 1/2, representatives 2–3 | success, 5/64 | 93/256 | 2 / 5 | 720 | 111 / 9 |
| Rational, either tolerance, all representatives | success, 5/64 | 52777/262144 | 2 / 5 | 831 | 147 / 9 |

Metadata counts use signed numerator/denominator code lengths for rationals and binary lengths for natural counters. Scalar codes and metadata are mathematical encodings, not measured heap sizes. At the tighter tolerance the bounded route stores fewer packets because it returns an incomplete prefix, so that storage comparison does not describe equal completed work.

The bounded work envelope charges 513 expression nodes per attempted tick, including guard expressions even when execution stops earlier. For tolerance 1/4 its categories are 3591 expression nodes, 33 scalar input conversions, 30 scalar output observations, 294 integer guard/arithmetic units, 25 schedule/search units, and 5 retained packet writes. At tolerance 1/2 they are 1026, 13, 42, 84, 8, and 8. Input conversion includes the five initial scalars and four controls/time scalars per attempted tick. Integer units charge seven threshold comparisons, eight rounded-domain arithmetic/comparison operations, twelve radius operations, four error additions, four packing comparisons, and seven Boolean combinations per tick. The initial domain/error admission is one additional compound predicate unit. Relabeling costs two scalar negations per quarter turn, hence two for this word. Initial representative conversion is common workload setup outside the driver counts.

The matched rational envelope charges 1026 formula-tree nodes, 20 packet-scalar bit scans, 5 setup copies, 42 output scalar observations, 8 schedule/search units, 8 retained packet writes, and 2 relabel negations. A rational formula node includes exact normalization as one model operation. Formula-tree envelopes and compound scheduling units deliberately avoid a host instruction or bit-operation model. Output observations account for reading all retained scalar slots and attempt errors; they need not all be materialized by the driver. The vector reports these categories separately, so it cannot be read as a sum of interchangeable time units. The formal work theorem bounds actual attempted ticks by reserved fuel; the expression theorem bounds visited nodes by full trees. The additional categories are declared executable accounting functions, not a proved machine-level resource bound.

The tools are Lean 4.35.0 and the repository's pinned Lake dependencies and Nix flake. To reproduce the smoke cases and emitted observations after building dependencies, run from the checkout:

```sh
direnv exec . lake build Examples.BoundedMotion
direnv exec . lake env lean Examples/BoundedMotion.lean
```

For the recorded development measurement, execution was serialized with `flock` and pinned with `taskset -c 0`, at `nice -n 10`. Eight bounded runs including rendering took 0.576–1.902 milliseconds; eight rational runs took 0.120–3.567 milliseconds. These are individual observations from the successful focused build, not repeated benchmarks or confidence intervals. Compilation, external process startup, and dependency builds are outside these timers. Rendering, garbage collection, and scheduling noise can dominate these small workloads.
