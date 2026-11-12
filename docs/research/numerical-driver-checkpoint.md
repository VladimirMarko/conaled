# Exact-rational driver feasibility checkpoint

The existing exact-rational backend supports a bounded demonstration envelope. The measured examples include a nonconstant move of duration 1/16, a move–turn–move word of total duration 3/64, and a fixed-duration refinement that changes the tolerance result from failure to success. Finer movement exhibits rapid numerator/denominator growth. The evidence supports continuing #49 with explicit input, search and resource limits; it does not establish practical long-run scaling or require an immediate arithmetic-backend replacement.

This historical checkpoint preceded the driver policy and is retained as input evidence, not candidate validation. The probe, its portable launcher, and sanitized output records now live in this repository. The completed driver and its acceptance evidence are described in [the driver report](budget-disk-driver.md).

## Inspected contracts and reuse

The frozen request is [issue #49](https://github.com/VladimirMarko/conaled/issues/49). Inspected production modules were `RationalMotion`, `CheckedMotion`, `NumericalExecution`, `NumericalSymmetry` and `MeasuredNumericalExecution`, alongside `Examples/NumericalMotion`, `Examples/MeasuredNumericalMotion`, `AttemptCounts` and the numerical-motion report. The checked examples contain kernel-checked successful ticks, an apex crossing, the word, two-half-step refinement, quarter-turn behavior and rejection controls; their `#eval` calls are short execution demonstrations. There is no existing command-level parser/retry driver in these modules.

The actual executable step is exact rational Euler arithmetic. `checkedStep` first checks `Admissible`, including control bounds, nonnegative incoming error, the conservative position margin, incoming frame size, and the advanced point/frame bounds. Its accepted result is `advance`; no normalization or float conversion occurs. The budget is

```
nextError = (1 + 13*d)*error + 39*d².
```

`run_correct` supplies final and sample approximation plus numerical-domain evidence, conditional on the initial `Approx`. `run_error` and `run_clock` recover the exact budget and clock. `run_append`, `execute_replicate` and `run_interval_correct` already supply composition and the equal-duration constant-command bridge. A driver should reuse them rather than reprove the Euler consistency/stability analysis.

The #193 measured adapter executes actual checked branches. `Measured.run_erases` recovers the unchanged native result; `run_append` composes successful traces and retains spent attempts on failure; `run_first_failure` ignores the unexecuted suffix. Counts are `(attempted,(accepted,rejected))`. These laws are ready for retry accounting, but attempts are not bit operations, wall time or a memory bound. `NumericalSymmetry.checkedStep_rotate` supplies a computable rotation comparison, while the abstract C4 action uses noncomputable enumeration. Mid-request events therefore need a finite executable label plus a proved semantic adapter and retained label, not execution of the abstract action instance.

## Probe and controls

`scripts/probes/DiskDriverFeasibility.lean` imports the actual measured executor and numerical symmetry. Its initial packet uses exactly the expression from `Examples.NumericalMotion.initial`: position `(-1/4096,0)`, frame `((1−(1/4096)²)/2,0)`, error zero. The existing `initial_approx` proves the matching fixture's exact-pose relationship. The probe duplicates that expression for execution; it introduces no new initial-state theorem or host axiom.

Move control is `(1,0)`, turn speed is 1. A case parameter n divides each command's declared rational duration by n. A word is n move ticks, n turn ticks and n further move ticks, carrying the same packet and error throughout. The harness chooses these ticks explicitly: this is a feasibility experiment, not the automatic-refinement acceptance test required of the eventual driver.

Two execution modes are recorded:

- `whole` calls `Measured.run` once on the complete list, retaining the actual result and measured counts. Sizes are maxima across returned samples plus the initial packet.
- `steps` calls `Measured.run [tick]` on successive returned packets, logs each accepted prefix and checks a packet-bit threshold before the next tick. Its correspondence to sequential native execution uses the existing append/erasure contracts; the harness is not a new proved runner. A resource stop is reported as `bit_cutoff`, never as whole-request success or backend domain rejection.

Bit sizes are the binary lengths of reduced rational numerators and denominators, maximized separately across the four state coordinates and the packet error. They exclude intermediate arithmetic temporaries, allocation overhead and time spent computing GCDs. For the large movement cases these maxima exceed the budget's own bit lengths and therefore reflect coordinate growth. Exact errors and clocks are retained in the logs; decimal values below are display approximations only.

Each numerical process ran via direnv, `lean -j 1 --run`, existing imported artifacts, and the shared `build.lock`. No `.olean`, `.c` or other project output was requested. The launcher used a 16 GiB virtual-address-space ceiling, 15/16-second soft/hard CPU limits, a 25-second wall timeout, an 8 MiB output limit and a five-second lock-acquisition wait. The source probe's packet-bit threshold varied as recorded below; it applies before a tick, so the final accepted output can exceed that threshold. The OS limits remain the outer bound on an individual attempted tick.

Initial smoke launches under a 4 GiB virtual-address ceiling failed to create a thread before numerical execution, including after requesting one Lean worker. Raising the ceiling to 16 GiB allowed elaboration. One subsequent probe had a formatting parser error, corrected before measurement. Those failures are preserved as `smoke*` logs and are not evidence of rational numerical failure. No artifact mismatch or integrity-guard incident was observed.

## Results

`W` means whole-list execution time. `S` means the stepping harness's total time, including log formatting and flushing. For cutoff/rejection rows, the time is the sum of measured checked-step times before stopping. Startup, import and elaboration are excluded from those times. These are individual measurements, not statistical benchmarks or standalone compiled-executable timings.

| Case | Command duration(s), subdivisions | Requested final tolerance | Outcome / final or prefix budget | Maximum numerator / denominator bits | Measured execution |
|---|---|---|---|---:|---:|
| Existing move | 1/1024, n=1 | 1/32768 | Accepted; budget ≈0.00003719 exceeds tolerance | 47 / 48 | 0.323 ms W |
| Existing turn | 1/1024, n=1 | 1/32768 | Accepted; same budget exceeds tolerance | 24 / 36 | 0.214 ms W |
| Existing word | Each 1/1024, n=1; 3 ticks | 1/8192 | Success within tolerance, ≈0.00011300 | 131 / 132 | 0.289 ms W |
| Fixed-duration refinement | 1/1024, n=2 | 1/32768 | Success within tolerance, ≈0.00001866 | 116 / 117 | 0.391 ms W |
| Same move | 1/1024, n=4 | 1/32768 | Success within tolerance, ≈0.000009343 | 705 / 706 | 0.892 ms S |
| Same move | 1/1024, n=8 | 1/32768 | Success within tolerance, ≈0.000004675 | 23,950 / 23,951 | 5.819 ms S |
| Refined short word | Each 1/1024, n=4; 12 ticks | 1/16384 | Success within tolerance, ≈0.00002839 | 25,298 / 25,299 | 16.464 ms S |
| Longer move | 1/16, n=4 | 1/16 | Success within tolerance, ≈0.05134 | 488 / 489 | 0.745 ms S |
| Longer move refined | 1/16, n=8 | 1/32 | Success within tolerance, ≈0.02738 | 17,875 / 17,876 | 1.778 ms S |
| Finer longer move | 1/16, n=16 | 1/64 | Resource stop after 11/16 ticks; prefix budget ≈0.008489 | 264,672 / 264,673 | 54.104 ms through prefix |
| Longer word | Each 1/64, n=4; 12 ticks | 1/32 | Success within tolerance, ≈0.009515 | 19,725 / 19,726 | 7.029 ms S |
| Finer short word | Each 1/1024, n=8; 24 ticks | 1/32768 | Resource stop after 18/24 ticks; prefix budget ≈0.00001060 | 140,079 / 140,080 | 119.486 ms through prefix |
| Longer turn | 1/16, n=64 | 1/256 | Success within tolerance, ≈0.003639 | 664 / 666 | 2.626 ms W |
| Coarser long move | 1/4, n=4 | 1/4 | Backend rejection on tick 3, after two accepted ticks | 89 / 90 in accepted prefix | 0.489 ms through rejection |

The first three whole runs returned measured counts `(1,(1,0))`, `(1,(1,0))` and `(3,(3,0))`. The two-step refinement returned `(2,(2,0))`; the 64-turn run returned `(64,(64,0))`. The known exact budgets match the checked examples: `39/1048576`, `124247487/1099511627776`, and `160251/8589934592` for a single tick, the word and two half ticks respectively.

Ordinary step-mode cases used the 16,384-bit pre-tick threshold. The n=16 longer move used 262,144 bits and stopped before tick 12; the finer short word used 131,072 bits and stopped before tick 19. Both stopped by the harness guard, not by CPU, memory or wall timeout. Their prefix budgets must not be compared with the request tolerance as if the requests completed. `planned-budget-only.json` evaluates the documented recurrence using Python exact `Fraction` for the hypothetical full schedules: each would satisfy its tolerance if every tick completed and passed admission. This is a budget calculation only, not a successful execution or a proof that the remaining domain checks pass.

The rejected 1/4-duration run has incoming error `1755/4096` after two ticks; this is a failed conservative checked execution, not proof that the exact free trajectory is invalid. Refinement may help some cases but has no blanket completeness guarantee.

Process wall times were roughly 1.67–1.77 seconds, dominated by startup/import/elaboration. Recorded maximum resident usage was roughly 4,151,000–4,153,000 KiB for most processes. That measures the whole Lean invocation and loaded development environment, not the numerical packet or a prospective standalone executable. No memory or performance claim about a compiled driver follows from those figures.

## Supported envelope and practical obstruction

The evidence supports a declared small demonstration using the existing exact initializer, bounded rational controls and a bounded finite schedule: the checked apex-crossing case, move–turn–move, and refinements through the measured n=4/n=8 movement cases. Longer physical duration is possible at coarse certified tolerances, as the 1/16 move and 3/64 word show. It is not justified to advertise all combinations within a rectangular duration/tolerance/tick-count range from these selected examples.

Movement's nonlinear rational division grows coordinates much faster than pure turn stepping. The finer word shows that a long rational move prefix also makes later turns more expensive even when their bit growth is modest. Therefore a count of accepted or attempted ticks cannot protect the runner from impractical rational arithmetic. Input numerator/denominator sizes, accumulated packet sizes, attempted prefixes and operational limits all matter.

The conservative bound also constrains accuracy independently of bit growth. For zero initial error and n equal ticks over T, the documented recurrence gives the necessary lower bound `errorAfter ≥ 39*T²/n`. For T=1/16 and tolerance 1/32768, that alone requires n≥4992, before the amplification term is included. This arithmetic observation explains why the short-duration high-accuracy fixture does not establish a useful long-duration high-accuracy envelope. It is not a new formal theorem or a claim about actual approximation error.

These measurements establish neither an impossibility result for exact rationals nor a need to replace the current backend before #49 can demonstrate its stated class. If the requested demonstration later requires substantially longer motion at tight tolerances, rerun the matching workload and decide whether a separately specified bounded-precision rational prerequisite is needed. Do not silently substitute floats or turn the checkpoint into a different simulator.

## Decision taken from the checkpoint

The driver uses at most four candidates (1, 2, 4, 8 subdivisions) per command, bounded exact input rationals, a saved incoming packet on every retry, actual measured checked-step counts, and pre/post packet-bit guards. A separate process wrapper retains the checkpoint's outer limits. This is a smaller admitted envelope than all of the measurements above: for example, an output above the driver's 16,384-bit ceiling is rejected even if the historical pre-step harness returned it. See the driver report for the exact policy and failure precedence.

## Reproduction and evidence

[`numerical-driver-checkpoint/manifest.json`](numerical-driver-checkpoint/manifest.json) records the numerical source, fixture, toolchain, dependency-manifest and original probe/runner hashes. The measurement revision was `68c85372b1754658786614bf2cc295ea9ec1293a`. These runs consumed existing artifacts; they are not fresh-source validation. Host-specific checkout and lock paths have been redacted from the retained metadata and logs. Source hashes and numerical arguments are retained; the portable launcher replaces the original host-bound launcher.

The adjacent `*.meta.json`, `.stdout` and `.stderr` retain caps and outcomes, including setup failures; `summary.json` contains exact fractions and `planned-budget-only.json` contains only hypothetical recurrence calculations. To reproduce after building the imported modules in the pinned shell:

```sh
direnv exec . python3 scripts/probes/run-disk-feasibility.py ./probe-output rerun-long-word word 4 1 64 32 16384 steps
```

When other agents are building, serialize this invocation using the orchestrator's shared build lock. The portable launcher uses `lake env` from the current checkout instead of a saved host-specific `LEAN_PATH`. Measurements may vary with the environment; neither agreement nor faster timing changes the proof boundary.

The current portable launcher uses [shared measurement support](measurement-support.md).
It preserves the positional command and `.stdout`, `.stderr`, `.meta.json` files,
adds a reserved `.setup/` directory and rejects reused evidence names. Current
receipts include source/toolchain/environment identity, explicit process and
publication outcomes, and a separately validated `numerical.outcome`. A zero CLI
exit retains its process-based meaning; inspect the numerical outcome for missed
tolerance or checked rejection. The retained historical logs above are unchanged.
