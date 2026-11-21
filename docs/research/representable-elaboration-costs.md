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
an upstream Lean bug report. If removing these thin adapters becomes useful,
[follow-up #661](https://github.com/VladimirMarko/conaled/issues/661), under the
[classification programme #647](https://github.com/VladimirMarko/conaled/issues/647),
owns the censored-client comparison with a separately justified whole-file time
budget or a command-level protocol that preserves the original statements.
Its results will also inform [#636](https://github.com/VladimirMarko/conaled/issues/636).

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
