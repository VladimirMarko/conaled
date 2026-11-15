# Bounded budget-driven disk execution

The command-level driver selects subdivisions for the existing exact-rational Euler backend. It accepts finite move, turn and hold requests, returns explicit C4 representative events, and either completes with a certified coordinate-error budget or reports why its bounded search stopped. It does not require callers to enumerate numerical ticks.

The [feasibility checkpoint](numerical-driver-checkpoint.md) determined the practical scope before the policy was implemented. Exact rational movement can grow very rapidly. The driver therefore combines finite search, bounded input, packet-bit checks and an independently bounded process launcher. These are different guarantees: a bound on attempted ticks is not a runtime or memory bound.

## Request and execution

Build the public modules using the repository's ordinary check procedure, then run inside the pinned shell:

```sh
direnv exec . python3 scripts/run-disk-driver.py tests/disk-driver/refine.json
```

The wrapper runs the Lean executable `scripts/disk-driver.lean`. The request is a JSON object:

```json
{
  "initial": "negative-axis",
  "commands": [
    {"kind":"move", "velocity":[["1","1"],["0","1"]], "duration":["1","1024"]}
  ],
  "tolerance":["1","32768"],
  "work":128,
  "rounds":4,
  "packet_bits":16384
}
```

Every rational is `[numeratorString, positiveDenominatorString]`; a complex coordinate is a pair of rationals. Exact reduced numerator/denominator pairs are also used in output. No decimal conversion participates in the claimed numerical result.

`initial` selects a supported packet, rather than accepting an arbitrary packet and treating its entered error as a proof. The only supported preset is `negative-axis`: position `(-1/4096,0)`, frame `((1−(1/4096)²)/2,0)`, error zero. `initial_exact` and `initial_approx` relate that executable packet to the exact pose. Output contains the complete initial packet. The core `drive` operation can receive other packets, but its soundness theorem requires their actual initial `Approx` relation.

Other physical commands are `{"kind":"turn","speed":["1","1"],"duration":["1","1024"]}` and `{"kind":"hold","duration":["1","1024"]}`. An event `{"kind":"relabel","quarter_turns":1}` changes representative between commands. Labels are integers 0–3, retained even for the identity event. Both position and frame rotate; the physical body control, error budget and physical time do not change.

The JSON envelope permits at most 65,536 bytes, 16 commands/events, 20 characters per rational component, numerator absolute value and denominator at most `2^63`, durations in `[0,1/4]`, supported unit-bounded velocity/angular controls, tolerance in `[0,1]`, at most 128 work units, 1–4 search rounds, and a packet-bit limit in `[64,16384]`. These are input limits, not a promise that every admitted request succeeds. Unsupported initializers and controls are explicit input failures.

For each command the search tries a bounded prefix of 1, 2, 4, 8 equal subdivisions. Each candidate executes from the **same incoming packet**, including its accumulated error. The candidate succeeds only if all backend checks and packet-bit guards pass and its final budget is at most the requested tolerance. Earlier successful commands remain committed if a later command fails. Failed candidates contribute actual work and diagnostics, but no committed samples or physical duration.

The same tolerance is used for each command. Overall success guarantees the final tolerance and each sample's own valid budget. The theorem does not advertise the requested tolerance for every sample, although the budget recurrence supplies additional monotonicity in suitable cases. The policy is neither complete nor optimal: a different allocation or finer schedule may succeed when this search fails. A nonzero incoming error is never reset, and refinement is not asserted to repair every failed sufficient domain check.

## Accounting and failures

Each candidate reserves its planned tick count plus one search unit before executing. A relabeling reserves one unit. Actual measured attempts, accepted steps and rejected steps are reported separately; discarded retries remain in these counts. `drive_work` proves `attempted ≤ charged ≤ supplied work`. Reservations can include unexecuted suffix ticks after an early failure. The distinction makes the work limit deterministic without presenting it as an exact count of every host operation.

Diagnostics have this precedence: parsing/admission before execution; insufficient candidate reservation before its packet checks; incoming bit guard before backend domain admission; outgoing bit guard after the attempted backend step; tolerance after a complete candidate. Packet-bit failure stops search. Domain failure or failed accuracy may try the next candidate; if no candidates remain the last reason is returned. If the next candidate cannot be reserved, the outcome is work exhaustion with earlier attempts retained. Failure after an accepted prefix returns that prefix, remaining input count and failure position, with `status="failure"`.

`domain-check` means the sufficient conservative backend guard could not certify this candidate. It is not proof that the exact trajectory leaves the disk. `packet-bit-limit` is distinct from domain rejection. Malformed requests, unsupported inputs, IO errors and process/resource failures are outside the formal numerical result. Admission errors inside the command/event array carry a zero-based `commands[i]:` prefix; request-level syntax and field errors have no command position. Each search attempt has `status="accepted"` with `failure=null`, or `status="failed"` with its explicit failure category. A rejected accuracy candidate and the selected candidate therefore remain distinguishable in successful requests.

Bit guards examine the reduced numerator and denominator lengths of the four coordinates and error, before and after each actual checked step. They exclude arithmetic temporaries and GCD work. One attempted step can exceed its incoming cap, so the wrapper adds a 16 GiB virtual-address ceiling, 15/16-second CPU limits, a 25-second wall limit and 8 MiB output-file limits. An interrupted or malformed child output is never reported as a certified success. These operational limits are Linux process assumptions, not Lean cost theorems.

## Formal connection

The implementation lives in `Applications/Orbifold/Driver/` and reuses `Numerical.run`, `Measured.run`, `checkedStep_correct`, repeated-command execution and the existing C4 action. It introduces no alternative physical dynamics.

- `schedule_control`, `schedule_clock` and `schedule_execute` connect a positive equal subdivision to the original exact command, including zero duration and holds.
- `guarded_sound` erases successful packet guards to the existing numerical executor. `Selected` stores evidence acquired from that execution and its checked tolerance; callers do not supply a desired success equation.
- `drive_chain` retains the actual execution evidence for every committed observation, even in a failed request. `drive_partition` proves that committed events followed by pending events equal the original request, preserving order and controls.
- `chain_correct` proves final approximation and `TraceSound` for the committed prefix. Physical samples satisfy the existing position/frame maximum-norm approximation and numerical domain condition. `run_exact_domains` additionally proves the required domain condition along each exact tick trajectory. Relabeling advances the exact representative through its retained finite label.
- `success_sound` and the preset specialization `request_success` combine completion, sample correctness and final tolerance. `success_clock` proves the original exact rational duration. `selected_samples_length`, `sample_clock_bounds` and `last_sample_clock` justify sample counts and assigned local endpoint times; `endpoints_replicate_get` identifies each such timestamp with the corresponding original exact trajectory point.
- `drive_action` proves equivariance of the **actual search and driver**, including selected subdivisions, work, failures and event labels. `inserted_event_replay` applies at an arbitrary saved incoming packet: inserting a relabel event with one extra fuel unit rotates the subsequent actual driver result, retaining body controls, searches and budgets. This covers changes midway through a request, not merely rotation of its initial condition.

The serializer prints packet fields and certified endpoint times as exact rationals. Parsing, file IO, process limits and rendering remain outside the analytic theorem. Endpoint samples do not certify a continuous interpolated drawing.

## Evidence and scope

The automatic-refinement fixture executes the one-step candidate with error `39/1048576`, discards it because it misses `1/32768`, then selects two half steps with error `160251/8589934592`. It commits exactly `1/1024` physical time and two samples while reporting three attempted ticks and five reserved work units. This distinguishes accuracy-driven selection from a caller-supplied fine schedule.

The move–turn–move fixture carries accumulated error across all three commands, with final budget `124247487/1099511627776` and total duration `3/1024`. Its first move crosses the apex in the existing exact fixture. The runtime suite also inserts a labeled quarter turn between the first move and turn, comparing rotated position and frame, unchanged error/time/body controls and one extra event charge. Zero-duration, positive hold, failed-retry, input and resource-bound controls use the same public JSON seam.

These are bounded demonstrations, not evidence of real-time performance or practical long-run scaling. The historical checkpoint records larger examples and cutoffs separately. Rendering, general FRP integration, numerical-backend replacement, general atlas descent and intrinsic-distance bounds remain outside this driver.
