# Representable-classification elaboration costs

This bounded experiment follows #643/#644 and supplies evidence to
[#636](https://github.com/VladimirMarko/conaled/issues/636). It compares three
encodings of the same native cubical interface. Mathematical recovery remains
unchanged; the experiment measures Lean elaboration, not execution of a compiled
functional program or author productivity.

## Inputs and method

The [runner](../../scripts/benchmark-representable-classification.py) builds the
import closure in each isolated workspace before timing. Each workspace has its
own project `.lake/build`; pinned dependency artifacts may be shared. The
[retained results](../../experiments/representable-classification/results.json)
record commits, source hashes, the direct variant's complete diff, Lean version,
dependency-manifest hash, runner hash, per-probe source hash, diagnostics and host.
Inputs are checked before/after builds and after measurement. The three inputs are:

| Variant | Source |
| --- | --- |
| Original native | `7f0d436bfc932ddd6b36d0e8f75f4cb30cdb8d5c`, before the #643 extraction |
| Direct generic | `290a15d8322cbd8f5ffc6186a589f4bfdec5827a` plus the retained [patch](../../experiments/representable-classification/direct.patch) |
| Specialized | `290a15d8322cbd8f5ffc6186a589f4bfdec5827a`, the published #643 implementation |

The direct patch removes the `dsimp%` coding specialization and uses the generic
`Evaluation.iso` directly for both native classifiers. It reconstructs the
representation choice being tested from public commits; it does not claim byte
identity with every intermediate failed #643 candidate. The generalized #644
sources are checked by the full acceptance build, rather than silently included
in these historical comparison variants.

Two probes exercise different behavior:

- **Nested recovery:** repeatedly code and decode an arbitrary `LocalFamily`, at
  depths 0, 2, 4, 8 and 16. The measured declaration composes every recovery
  isomorphism explicitly. Family setup declarations are outside the measurement.
- **Retained regression:** the [package identity declaration](../../experiments/representable-classification/reduction-repro.lean.txt)
  from the #643 recursion failure, using the existing finite-state structured
  transport API. This probes the dependent reduction that simple isomorphism
  chains do not expose.

Each probe runs twice at five `(maxRecDepth, maxHeartbeats)` pairs:
`(512, 50000)`, `(512, 200000)`, `(768, 200000)`, `(1024, 200000)` and
`(2048, 800000)`, with a 30-second process timeout. There are 180 measured
processes. The budget grid is sampled evidence, not a search for exact minima.

`#count_heartbeats` counts allocation-based Lean heartbeats for the final
command, in units of 1,000 internal heartbeats. It disables asynchronous
elaboration and temporarily disables the heartbeat limit; the generated source
therefore restores the requested `maxHeartbeats` **inside** that wrapper.
The [integration test](../../scripts/test-benchmark-representable-classification.py)
checks that a budget of 1 fails while 200,000 succeeds, both with a reported
count. Counts on failure are work up to failure, not estimates of successful
completion. They are not allocated bytes or peak memory measurements.

Wall time covers the whole `lake env lean` invocation, including process startup,
imports and setup. It is not pure declaration elaboration time. Runs are sequential
with warm dependency artifacts, but this is a shared development host and no
CPU isolation is claimed. Two repetitions cannot establish small timing differences.

## Results and decision

The retained regression gives the following declaration heartbeat counts on
successful runs; each count repeats across the passing budgets and repetitions.

| Variant | At 512 / 200,000 | Lowest tested passing recursion budget | Successful heartbeats |
| --- | --- | --- | --- |
| Original native | Pass | 512 | 109,979 |
| Direct generic | Recursion failure | 768 | 112,844 |
| Specialized | Pass | 512 | 111,506 |

Successful regression process times ranged from 4.94–5.01 seconds for native,
5.20–5.45 seconds for direct, and 5.02–5.08 seconds for specialized. These are the
observed ranges across the passing budget cells and two repetitions, subject to
the startup and shared-host limitations above.

The direct version fails at 512 after 15,321 heartbeats, well before its heartbeat
budget. Raising recursion alone to 768 resolves this retained failure. Native and
specialized versions fail at the deliberately reduced 50,000 heartbeat budget;
raising that budget restores success. The direct version hits recursion first
at 512 even with the reduced heartbeat budget. A larger recursion budget and a
larger heartbeat budget address different failure modes.

The simple nesting probe passes at every tested depth and budget for all three
variants. Its cost grows with the explicit composition chain, but it does not
reproduce the dependent package's recursion failure. It cannot justify a claim
that all deeper clients are cheap, or that arbitrary nesting will hit the same
threshold. The regression is needed alongside the synthetic depth probe.

For this client, the specialized version costs about 1.4% more successful
heartbeats than the original native version; the direct version costs about 2.6%
more. Neither difference supports a general runtime or productivity conclusion.
The larger difference is where elaboration crosses the recursion guard.

Keep the existing shallow native specialization and shared mathematical proof.
A local recursion increase is also a reasonable option when a concrete client
benefits from the direct form: this experiment establishes that it works here.
There is no evidence requiring a repository-wide increase, and the exact minimum
was not measured. The [four-client follow-up](#four-original-clients-at-depth-1024)
below tests the broader regression set. No production limits were changed.

The demonstrated simpler-adapter alternative is direct generic specialization
with a local recursion increase. The matrix compares the combined shallow coding
and native-component choices against removing both; it does not isolate their
individual costs. Removing either globally still needs the broader client check
above.

Reduction lemmas need a different experiment. The retained failure occurs while
Lean checks an existing term against a dependent target, with no simplifier step.
Ordinary `[simp]` lemmas are not automatically used by definitional equality, so
adding such lemmas alone is not an evidenced fix for the unchanged caller. An
explicitly rewritten target or helper proof might use reduction lemmas to avoid
that conversion path, but it would be a new client variant with setup and
maintenance costs to measure. The shallow definitions already present the needed
computational shape before conversion. Retain them for now; no lemma-driven
variant was measured, and no claim is made that it would improve these results.

This is not yet a minimal upstream Lean reproducer: it imports substantial project
semantics. The retained source and direct patch make reduction behavior reproducible
for further minimization if it obstructs a useful client. The observed failure is
consistent with deeper elaborator reduction reaching a configured guard; it does
not by itself establish a Lean correctness bug. Further minimization or broader
budget tuning belongs to the continuing #235/#636 evidence assessment when needed.

In the pinned Lean 4.35 toolchain, the default recursion guard is 512 and the
default heartbeat budget is 200,000. Both are configurable resource guards;
`maxRecDepth` is not a theorem about expressible programs or a runtime call-stack
limit. Compiled tail recursion or iteration can run for arbitrarily many steps
without increasing elaborator recursion depth accordingly. More deeply nested
terms or reductions can still require more elaboration resources. These concerns
should inform representation and local budgets without becoming mathematical
restrictions on the shared interface.

## Reproduction

Create detached worktrees at the revisions above, apply `direct.patch` only to
the direct workspace, and initialize the pinned development environment and
Mathlib cache. Keep each project's build directory private. From the current
repository's development shell, run:

```sh
python3 scripts/benchmark-representable-classification.py \
  --workspace native=/path/to/native \
  --workspace direct=/path/to/direct \
  --workspace specialized=/path/to/specialized \
  --depths 0,2,4,8,16 \
  --budgets 512:50000,512:200000,768:200000,1024:200000,2048:800000 \
  --repeats 2 --output /tmp/representable-costs.json
python3 scripts/test-benchmark-representable-classification.py
```

The test defaults to the current checkout; `REPRESENTABLE_BENCH_WORKSPACE` can
select an independently built stable checkout. Do not edit a measured workspace
during a run. A report is complete only when `inputs_verified_after` is true;
partial output is retained for diagnosis if a run is interrupted. Source-policy,
full-build and exhaustive-axiom validation remain separate acceptance checks.

## Four original clients at depth 1024

The [#648](https://github.com/VladimirMarko/conaled/issues/648) follow-up compares
all four original regression files without changing their statements or proofs:
`CubicalAuthorTransport`, `CubicalConstructorState`,
`CartesianPackageRecomputation`, and `CubicalInterpretationObservations` in
`Examples/`. Both workspaces start at
`bc95f503ccbf043136c6699992388f750270e8e6`; the direct workspace applies only the
retained `direct.patch`. The four clients and four patched classifier files are
byte-identical to their versions at `290a15d8322cbd8f5ffc6186a589f4bfdec5827a`.
The rest of the import closure uses the current pinned sources, including the
generalized shared classification interface.

The [client runner](../../scripts/benchmark-classification-clients.py) reuses the
original runner's source fingerprinting and checks complete imports before
measurement. Project build directories are private; pinned dependency artifacts
are shared. The [client results](../../experiments/representable-classification/clients-results.json)
retain the complete direct diff, source and client hashes, dependency revisions,
Lean version, runner hashes, commands, diagnostics and individual measurements.
Both inputs are checked after the run. Each file is run twice in each of three
configurations, for 24 processes:

| Form | Recursion budget | Heartbeat budget | Process timeout |
| --- | --- | --- | --- |
| Current specialized | Original default 512 | Original default 200,000 per command | 30 seconds |
| Direct, control | Original default 512 | Original default 200,000 per command | 30 seconds |
| Direct, proposed local budget | 1,024 | Original default 200,000 per command | 30 seconds |

The sole resource override is `-DmaxRecDepth=1024` on the last row's individual
`lake env lean Examples/<client>.lean` process. It applies to that module's
commands, not its already built imports or any production source. No heartbeat
limit is disabled. All measurements use synchronous elaboration and Lean's
heartbeat profiler via command-line options. Only the inclusive, unindented
`Elab.command` roots are summed, avoiding double counting nested traces. The raw
profiler unit is one internal heartbeat; divide by 1,000 for the budget units
used above. Totals cover all profiled commands in the file and can exceed the
per-command budget. They include profiling overhead and exclude import loading;
they are not directly comparable to the earlier single-declaration wrapper's
counts. Wall time covers the entire profiled process, including startup and
imports. No byte-allocation or resident-memory measurement was made.

The [regression tests](../../scripts/test-benchmark-classification-clients.py)
check the aggregation rule and run a real Lean fixture with heartbeat budgets
1 and 200,000, checking failure and success while preserving the fixture's bytes.
The four-client run separately exercises the recursion guard. Timing was
coordinated with the other active implementation agent, which paused compiler
work. The machine was still a shared host without CPU isolation; two repetitions
cannot establish small timing differences.

For the two completed clients, aggregate profiled heartbeats (rounded to the
nearest budget unit) and process-time ranges across two repetitions are:

| Client | Specialized, 512: heartbeats / seconds | Direct, 1024: heartbeats / seconds |
| --- | --- | --- |
| `CubicalAuthorTransport` | 147,833 / 6.82–7.31 | 149,980 / 6.89–7.40 |
| `CubicalConstructorState` | Censored / 30-second timeout | Censored / 30-second timeout |
| `CartesianPackageRecomputation` | 75,200 / 4.33–4.39 | 74,447 / 4.15–4.38 |
| `CubicalInterpretationObservations` | Censored / 30-second timeout | Censored / 30-second timeout |

At depth 512, direct `CubicalAuthorTransport` and
`CartesianPackageRecomputation` fail with recursion diagnostics in both
repetitions, without a heartbeat-limit diagnostic. At depth 1024 both pass.
The successful heartbeat differences relative to specialized are about +1.5%
and −1.0%, respectively. Their opposite signs provide no uniform cost advantage
for either form. The other two clients hit the process deadline in every
profiled configuration; increasing recursion to 1024 does not make either
finish within that bound. No completed cost or depth-failure diagnosis follows
from these timeouts.

The raw heartbeat field on a timeout sums only command traces emitted before
termination. It is a lower bound, not the successful file cost. Standard-output
buffering can leave no captured count even after elaboration has started.
Recorded wall time includes launch, termination and process reaping, so a
30-second timeout can appear slightly above 30 seconds. The earlier experiment's
30-second bound covered a setup plus one measured declaration; applying the same
bound to a whole regression file is a stricter completion test. These results
do not establish that an individual declaration exceeds that bound or that work
grows nonlinearly.

The separately retained `unprofiled_controls` remove all profiling and
synchronous-elaboration overrides. They run the original files with their
original options, adding only the module-process recursion override for direct.
Each control ran once at the same 30-second process bound:

| Client | Specialized, 512 | Direct, 1024 |
| --- | --- | --- |
| `CubicalAuthorTransport` | Pass, 6.37 s | Pass, 6.42 s |
| `CubicalConstructorState` | 30-second timeout | 30-second timeout |
| `CartesianPackageRecomputation` | Pass, 2.38 s | Pass, 2.37 s |
| `CubicalInterpretationObservations` | 30-second timeout | 30-second timeout |

The same two files time out without instrumentation. Profiling therefore does
not alone explain their failure to finish under this whole-file process bound.
These controls supply no successful whole-file cost for those clients. The
successful process times also differ between profiled and unprofiled runs;
neither set isolates pure declaration elaboration time.

Keep the current specialization. The retained direct patch removes four `dsimp%`
normalizations and replaces two `NatIso.ofComponents` assemblies with
`decodeCodeEvaluation.iso`. Its net source reduction is eight lines across four
files. It deletes no public declaration or mathematical theorem:
`decodeCodeComponent`, `decodeCodeEvaluation`, coding/reindexing laws and the
shared `RepresentableClassification.Evaluation.iso` proof remain. The existing
specialization already reuses that proof's naturality result. This is a choice
between computational presentations of shared mathematics, not between two
independently maintained mathematical implementations.

Callers keep the same names, types, assumptions, statements and proof bodies.
The direct form adds a module-scoped recursion budget to the tested calls; the
successful clients require no rewritten targets, casts or helper lemmas from
the caller. A depth of 1024 is an acceptable finite engineering budget. Retaining
the specialization is justified by its small maintenance footprint and the lack
of a complete four-client cost/compatibility result under the bounded protocol,
not by requiring every future client to fit 512.

The changed computation passes through the generic evaluation component's
`Equiv.cast` before the native `mapIso`. Native `decodeCodeComponent` omits that
extra reducible layer. `chartDecodeIso` and `decodedLocalFilling` use the selected
comparison, so replacing it affects the reduction path used to compute fillers,
even though their source definitions and laws are unchanged. The completed
unchanged clients check their existing package, record and transport contracts.
The censored files supply no complete contract check, and this experiment proves
no new cross-implementation equality for arbitrary selected fillers. The generic
coding and evaluation entry points remain available alongside the shallow
specialization; no second public facade or independently maintained proof is
needed.

No production Lean code or resource default changes. No integrated build/audit
is claimed for an adopted direct implementation because none is adopted. The
auxiliary runner is checked on real Lean fixtures, the retained data are checked
against their source/runner hashes, and the report receives content/link checks
and independent Standards/Spec review. A future adoption would still need the
full integrated build/audit and complete original client contracts. There is no
repeated recursion-budget escalation or measured growth series here to justify
an upstream Lean bug report. [Follow-up #661](https://github.com/VladimirMarko/conaled/issues/661),
under the [classification programme #647](https://github.com/VladimirMarko/conaled/issues/647),
subsequently measured these clients with a separately justified whole-file bound.
Its [complete-client diagnosis below](#complete-client-diagnosis-under-a-separate-process-bound)
adds evidence for [#636](https://github.com/VladimirMarko/conaled/issues/636) while
preserving this original bounded result.

To replay the follow-up, create two detached worktrees at `bc95f503`, apply
`direct.patch` to the direct tree, initialize their environments and pinned
Mathlib cache, and keep project outputs private. From a checkout containing the
new runner:

```sh
python3 scripts/benchmark-classification-clients.py \
  --specialized /path/to/specialized --direct /path/to/direct \
  --repeats 2 --timeout 30 --output /tmp/classification-clients.json
python3 scripts/test-benchmark-classification-clients.py
```

The data's `unprofiled_controls.script` stores the complete portable control
harness and its SHA-256. Extract that string to a temporary Python file and run
it from this checkout with `--specialized /path/to/specialized`,
`--direct /path/to/direct`, and `--output /tmp/controls.json`; `--runner` can
select the absolute path of `scripts/benchmark-classification-clients.py`.
Both result objects must report `inputs_verified_after: true`. The retained
`direct.patch` SHA-256 is `2208009fe6828d8c12293ee64d96979af3b137a66d07c70286a760e4a27cb4ba`.

## Complete-client diagnosis under a separate process bound

The [#661](https://github.com/VladimirMarko/conaled/issues/661) measurement uses
`a65430ba42ce5c36a73e66bd9e0c2dd625807a73` for both forms, applying the same retained
`direct.patch` only to the direct worktree. The four clients remain byte-identical
to #648. The original 30-second results above remain unchanged and are not
relabelled as successes under a larger bound.

The [protocol](../../experiments/representable-classification/complete-protocol.json)
predeclares a finite 300-second whole-file timeout, ten times the earlier bound.
This allows accumulated work across the 374-line ConstructorState and 212-line
InterpretationObservations files. It is a completion and diagnosis budget, not
an estimate of their minimum requirement. There is no automatic timeout
escalation. Every invocation explicitly retains `maxHeartbeats=200000`, with
`maxRecDepth=512` for specialized and `1024` for direct. No production option or
client file changes.

The [runner](../../scripts/benchmark-classification-complete.py) checks each
private import closure before timing and checks the complete input identities
afterward. Pinned dependency artifacts are shared; project build directories
are distinct. The [raw results](../../experiments/representable-classification/complete-results.json)
retain the protocol, source and client hashes, complete direct diff, dependency
revisions, compiler version, runner hashes, commands, source-located diagnostics,
all command traces, selected command totals, process wall times and load averages.
Only a result with `inputs_verified_after: true` is a complete run.

All four files receive two synchronous heartbeat-profile runs and one control
with the original asynchronous setting and no profiling. The two previously
censored files also receive synchronous unprofiled and synchronous wall-profile
controls. The latter measures command seconds with Lean's monotonic clock in a
separate run from the allocation-based heartbeat counter. These heartbeat
counts are internal units: Lean multiplies the user-facing `maxHeartbeats` by
1,000. Neither measurement reports allocated bytes or peak memory. Command
sums cover the emitted inclusive command ranges, excluding import setup and
output rendering; they are not a counter for every allocation in the process.
Process wall time additionally includes startup, imports, diagnostic rendering
and process reaping. The inclusive trace counter and the failing guard's
scoped counter are distinct; the observed diagnostic identifies the exhausted
budget, rather than a comparison of the inclusive total with 200,000.

Lean's JSON diagnostics supply source ranges for command traces. A scoped
`set_option ... in` emits separate traces for its expanded commands and their
inclusive parent. The new runner retains all of them but sums only maximal
nonoverlapping source ranges. Missing or ambiguous ranges suppress an aggregate
rather than inventing a total. A checked scoped-option fixture exercises this
case. The two completed #648 clients contain no scoped-option wrappers, and all
retained ConstructorState timeout output ends before its scoped wrappers, so
this correction does not change the published successful totals or those
captured prefixes. It matters for the newly observed full ConstructorState trace.

A second real fixture completes an arithmetic declaration and then sleeps in
IO for ten seconds. Both processes are killed after four seconds. Comparing
default buffering with `stdbuf -oL -eL` checks that a completed trace survives
termination. The fixture's source, hash and raw partial output are retained
separately from classifier costs. All client runs use line-buffered JSON output;
this changes diagnostic delivery, not their source statements or proof bodies.

Timing is sequential. The other implementation agents pause Lean compilation
within each measured block and may compile while the runner waits at an explicit
client-pair boundary. This is a shared host without CPU isolation or guaranteed
resident caches. Per-process load averages are retained; two repetitions do not
establish small speed differences. Failed-file trace totals record observed work
in a rejected elaboration, not successful file costs or estimates of them.

### Repeated heartbeat results

The following are the two synchronous heartbeat-profile runs per form.
Counts are sums over maximal command ranges, in millions of internal
heartbeats. An asterisk marks observed work from a failed file, not a
successful cost. All processes exited before the separate 300-second bound.

| Client | Form | Result, both runs | Internal heartbeats (millions) | Process seconds |
| --- | --- | --- | ---: | ---: |
| CubicalAuthorTransport | specialized | Pass | 147.851 | 7.40–11.94 |
| CubicalAuthorTransport | direct | Pass | 149.980 | 7.46–7.96 |
| CubicalConstructorState | specialized | Heartbeat limit | 681.904 * | 48.87–54.13 |
| CubicalConstructorState | direct | Heartbeat limit | 749.454 * | 52.48–52.98 |
| CartesianPackageRecomputation | specialized | Pass | 75.347 | 4.46–4.52 |
| CartesianPackageRecomputation | direct | Pass | 74.447 | 4.48–4.59 |
| CubicalInterpretationObservations | specialized | Pass | 786.218 | 51.89–53.67 |
| CubicalInterpretationObservations | direct | Heartbeat limit | 796.778 * | 50.82–51.68 |

The only count variation is two internal heartbeats in specialized author
transport; all other totals reproduce exactly. These are not four-client
successes. Constructor state fails in both forms at `carrierComparison`
(line 159), with a `whnf` heartbeat diagnostic. Direct interpretation fails
inside `pathBijection_concat` (command line 80, diagnostic line 89), at
`isDefEq`; specialized interpretation passes. Neither failure is recursion
exhaustion or a process timeout. Subsequent controls below separate the
profiling and asynchronous settings.

The largest measured interpretation commands are `pathBijection_ua` (line 64),
`pathBijection_concat` (line 80), and `no_collapsing_action` (line 100). Their
specialized counts are 476.098, 193.008 and 53.674 million internal heartbeats;
together they account for about 92% of its successful traced-command total.
The corresponding direct observations are 476.508, 200.014 and 53.836 million,
with the middle command rejected. For constructor state, the failed
`carrierComparison` trace accounts for 379.714 million specialized and 379.653
million direct internal heartbeats. `argument_start` (line 291) then contributes
92.215 and 92.400 million. Lean continues after reporting a rejected declaration,
so later trace output does not turn either failed file into an accepted contract.
These locations identify concentrated work; they do not establish asymptotic or
nonlinear growth. No size-growth experiment is part of this protocol.

The buffering fixture retained zero completed command roots with default pipe
buffering and one with line buffering, while both processes reached their
four-second timeout. This is direct evidence of lost completed-message visibility
under the former capture method, not evidence that the sleeping command
completed. The line-buffered runner keeps every observed diagnostic and reports
missing or ambiguous command coverage explicitly.

### Ordinary and synchronous controls

These unprofiled controls run once each. They measure complete process wall time
on exit, not command heartbeats. The async column leaves Lean's original
asynchronous setting untouched; the synchronous column adds only
`-DElab.async=false`. The same explicit recursion and heartbeat budgets apply.

| Client | Form | Original async | Synchronous, no profiler |
| --- | --- | --- | --- |
| CubicalAuthorTransport | specialized | Pass, 6.41 s | Not scheduled |
| CubicalAuthorTransport | direct | Pass, 6.49 s | Not scheduled |
| CubicalConstructorState | specialized | Pass, 42.57 s | Heartbeat limit, 48.06 s |
| CubicalConstructorState | direct | Pass, 45.57 s | Heartbeat limit, 48.47 s |
| CartesianPackageRecomputation | specialized | Pass, 2.38 s | Not scheduled |
| CartesianPackageRecomputation | direct | Pass, 2.38 s | Not scheduled |
| CubicalInterpretationObservations | specialized | Pass, 38.51 s | Pass, 46.72 s |
| CubicalInterpretationObservations | direct | Heartbeat limit, 40.61 s | Heartbeat limit, 47.58 s |

All four specialized clients pass with the original async setting. Three direct
clients pass; direct interpretation still fails at `pathBijection_concat`,
line 89, with a `whnf` heartbeat diagnostic. Its synchronous unprofiled failure
is at the same line, with `isDefEq`, matching the heartbeat-profile location.
That obstruction persists without instrumentation. In contrast, both constructor
forms pass asynchronously but fail at `carrierComparison` under synchronous
elaboration, even without a profiler. The async-setting change alone is enough
to expose that failure. A synchronous rejected-file heartbeat total cannot be
used as the cost of the successful asynchronous run.

These controls separate mode effects from the old process cutoff: successful
asynchronous constructor and specialized interpretation runs take more than
30 seconds, while the direct interpretation process now reaches a specific
heartbeat error. They do not measure profiling overhead by subtracting unequal
accepted/rejected executions, and one control run per mode does not establish a
small performance difference. No asynchronous command-heartbeat total is
reported by an unprofiled control.

To reproduce this separate protocol, create two detached worktrees at the full
`a65430ba42ce5c36a73e66bd9e0c2dd625807a73` pin, apply the retained `direct.patch`
only to the direct tree, initialize the pinned development environment and
Mathlib artifacts, and keep the project build directories private. Run from a
checkout containing this runner and protocol:

```sh
python3 scripts/benchmark-classification-complete.py \
  --specialized /path/to/specialized --direct /path/to/direct \
  --pause-between-clients --output /tmp/classification-complete.json
CLASSIFICATION_BENCH_WORKSPACE=/path/to/specialized \
  python3 scripts/test-benchmark-classification-complete.py
```

The optional pause waits before each client pair, outside measured process time;
use it to coordinate compiler activity. Omitting it runs the same protocol
sequentially without interaction. Input builds occur before timing. The output
must contain all 32 predeclared rows and `inputs_verified_after: true`; each
row's status and raw diagnostics determine whether its cost is complete.


### Wall-profile controls and disposition

The separate synchronous wall-profile runs retain command seconds as well as
whole-process wall time. An asterisk denotes a rejected file, not a successful
execution cost.

| Client | Form | Result | Command seconds | Process seconds |
| --- | --- | --- | ---: | ---: |
| CubicalConstructorState | specialized | Heartbeat limit | 43.888 * | 45.05 |
| CubicalConstructorState | direct | Heartbeat limit | 47.136 * | 48.22 |
| CubicalInterpretationObservations | specialized | Pass | 52.564 | 56.94 |
| CubicalInterpretationObservations | direct | Heartbeat limit | 49.718 * | 51.22 |

The worker reached the platform usage limit while paused before the final
InterpretationObservations pair. The coordinating agent completed that pair
with the same pinned `run` function, budgets and input checks. The raw result
records the continuation script and its hash. All 32 predeclared rows are
present, and the final source, protocol and runner identity checks passed.
No process reached the separate 300-second limit.

Retain the production specialization. With the original async setting all four
specialized clients pass, while direct interpretation still fails at the
unchanged heartbeat guard. Raising direct recursion depth to 1024 therefore
does not establish complete compatibility. The direct patch's small wrapper
reduction does not currently justify migration or maintaining two production
implementations. The original 30-second evidence remains useful as a bounded
experiment; these longer controls diagnose what that bound concealed.

Future measurements must record the async setting and distinguish successful
costs from work observed in rejected files. The synchronous constructor failure
persists without profiling; its precise relationship to Lean's task-level
heartbeat accounting is not established here. This evidence belongs in #636's
guidance reassessment. A further simplification or upstream report needs a
concrete consumer or minimized obstruction; neither is justified merely by the
old process timeout. No production defaults or selected-operation contracts
changed, and no asynchronous command-heartbeat total is inferred from these
unprofiled controls.
