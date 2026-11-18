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
or the behavior of all four original failing clients has not been measured.
Before removing the specialization globally, repeat the comparison on those
clients and the full integrated suite. No production limits were changed.

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
