# Incremental dependent author trial

Issue #357 asks whether an independently authored extension can use the reviewed
dependent interfaces while retaining native typing, compiled syntax and selected
results. The trial compares a native route with the compositional route from
#356. This report distinguishes correctness, incremental author effort and setup.

## Frozen question and inputs

Task design began at 07:47:23 UTC on 8 November 2026, after independent review and
integration of #355 at `1ff031ca983d02906c26b57af2424c694b6e5a58` and #356 at
`7b5c27c6c607201928d14975611b2e26d450293d`. Protocol/setup candidate
`d39ac0e648310a8d0fcfb5b235233e6dfc9b1b5b` passed both review axes and the complete
1,895-module build and exhaustive axiom audit before dispatch. Immediate
candidate verification matched. These are preparation results, not author results.

The [task](../../experiments/incremental-dependent-authoring/tasks/common.md)
extends the fixed public client to arbitrary finite successor/doubling schedules.
It requires actual native dependent typing, F/fullG translation and pack/split
quotation, separate executable representations, concatenation and empty cases,
and two typed substitutions. The independent specification defines a packet
`(k : Nat) × Fin (k + 2)` and retains a particular component. A five-operation
example yields `(18,18 : Fin 20)`; after the substitutions it yields
`(34,34 : Fin 36)`. A same-index zero component is the negative control.

Both arms received the same task, specification and protocol. The native source
closure came from the pre-#356 commit and contained 40 library modules. The
candidate closure contained 53. Adding the common specification gives 41 and 54
allowed modules. The candidate receives both generic preservation machinery and
client-specific helpers; the experiment cannot isolate the benefit of the
generic theorem from those helpers.

Two fresh agents received no conversation fork or model/reasoning overrides.
The setup helper and protocol designer did not author submissions. Neither arm
received a prepared solution or could inspect the other submission under the
protocol. Private project/dependency copies, source manifests and wrapper checks
support the access contract; there was no operating-system sandbox. Original
project Git history was not copied. A fresh public-only index allowed the pinned
Nix environment to ignore private caches.

## Budget and evidence

The [protocol](../../experiments/incremental-dependent-authoring/protocol.md)
sets 30 minutes or 30 archived Lean checks, whichever comes first. Reading,
editing, diagnostics and reporting count. Every Lean check, including inspection,
uses the unchanged attempt wrapper and a fresh source filename. The wrapper
records exact bytes, input hashes, commands, timestamps, raw diagnostics and
exits. It does not decide whether a statement meets the mathematical task.

Dispatch was specified at 08:05:00 UTC for the native author and 08:05:05 UTC for
the compositional author, with corresponding 08:35 deadlines. These coordinator
clock marks surround dispatch calls; finer tool-dispatch timestamps are not
available. Environment help and shared clarifications are allowed and recorded;
proof hints, interface repairs and task changes are excluded. Exact final replay
and independent statement assessment occur after measured work.

## Observed submissions and replay

Both authors stopped after a complete passing submission, before either cap.
The coordinator copied the exact submitted bytes into normal example modules:
[native](../../Examples/IncrementalDependentNativeTrial.lean) and
[compositional](../../Examples/IncrementalDependentCompositionalTrial.lean).
No coordinator proof repair is included or credited to either author. Exact
replay in each original frozen handoff passed without Lean diagnostics.

| Observation | Native | Compositional |
|---|---|---|
| Final snapshot | Attempt05 | Attempt06 |
| Dispatch-to-stop | Approximately 4 min 40 s | 4 min 2 s |
| Archived Lean checks | 5 | 6 |
| Failed / passed checks | 3 / 2 | 5 / 1 |
| Source lines / bytes | 248 / 11,329 | 328 / 14,222 |
| Final replay | Passed | Passed |
| Assistance or interruptions reported | None | None |

The native stop time was recorded approximately by its author. These elapsed
times include reading and reporting, not just proof construction. The native
arm also reported one missing-file wrapper invocation, rejected before an archive
or Lean process was created. It is recorded in the activity/outcome evidence,
not counted as an archived Lean check; raw diagnostics for that preflight failure
were not preserved by the wrapper. Both authors initially invoked Python outside
direnv while editing and repeated the command inside the pinned environment.
Those are author events, separate from the earlier setup corrections.

The [complete evidence](../../experiments/incremental-dependent-authoring/evidence/)
retains every archived source, raw Lean diagnostic, input manifest, activity log,
outcome, dispatch prompt, freeze approval and exact replay record. The final
native snapshot repeats its previously passing Attempt04 byte-for-byte. Every
failed archived attempt remains available; a later success does not remove it.

## Statement assessment and local obligations

Both submissions quantify over arbitrary schedules and input naturals. Their
concatenation theorems concern generated code and its execution; the numerical
cases consume general preservation results. Runtime carriers contain arithmetic
code and explicit pair/observation operations, rather than derivation trees or
calls to the independent specification. Complete dependent packets are compared,
so the same-index wrong component is rejected.

| Common requirement | Native submission | Compositional submission |
|---|---|---|
| Native typing and actual F/G target | `Ix.typed`, `rawTyped`, `afterF`, `afterG`, `twoStage`, `quotation` | `sourceProof`, `native`, `targetNative`, `native_fullG`, `native_FG`, `target_pack_split` |
| Independent selected execution | `execution`, `selected` for separate source/target carriers | `source_execution`, `target_execution` through the public `compiled_image` law |
| Concatenation and empty schedule | `generate_append`, `eval_append`, `selected_append`, `empty_selected` | `schedule_append`, `code_index_append`, `selected_append`, `empty_execution` |
| Two typed substitutions and dependent boundary | `envTyped`, `firstSubstituted`, `twiceSubstituted`, `twice_raw`, `twice_type`, `twice_target_quote`, `twice_selected` | `nativeSigma`, `nativeTwice`, raw/type replacement laws, substituted quotations, `substituted_execution` |
| Selected oracle cases and rejection | `demo_value`, `substituted_value`, `reject_wrong` | `demo_execution`, `demo_substituted`, `reject_wrong` |

The native author defines a small arithmetic AST and separate source/target
pair carriers, constructs native typing including conversion of the dependent
projection type, and proves a general typed index replacement. The compositional
author reuses the existing arithmetic syntax, code, typed substitution helpers
and whole-proof/code theorem. It still proves schedule generation, concatenation,
raw term/type substitution and selected-output connections. Its submission also
makes equality with two code substitutions explicit; extra declarations receive
no correctness bonus beyond the common outcome.

The native route normalizes its result type to `B(s(index))` using native typing
conversion. The compositional route retains the corresponding projection-based
type and its substitution equations. Neither claims equality of unrelated proof
trees. The interpreted target remains the bounded generated-program image,
not an arbitrary fullG derivation. All new comparisons use Lean propositional
equality; object-language typing remains the existing native judgment.

Failures were local encoding and proof-connection problems. Both first attempts
used unsupported namespace-alias syntax. Native repairs concerned declaration
premises, conversion simplification and equality of dependent packets.
Compositional repairs concerned unfolding, substitution under declaration
arguments, a missing namespace opening and rewrite matching. The raw diagnostics
and author logs support those descriptions. They do not show that the underlying
mathematical statements were false.

Both routes achieved the common outcome on the coordinator's statement assessment;
independent review and the integrated exhaustive audit are the acceptance gates.
The timing difference, extra candidate support, fewer native checks and shorter
native source do not select a superior interface. The useful observation is
that both frozen routes supported this fresh extension without library changes,
and that compositional reuse still left concrete boundary lemmas to write.

## Preparation and interpretation limits

[Setup evidence](../../experiments/incremental-dependent-authoring/setup/VALIDATION.md)
preserves closure creation, independent specification compilation, unchanged-wrapper
success/failure smoke checks and setup corrections. Successful closure-copy
commands took 11.18 seconds and 70.31 seconds. Those durations omit protocol
writing, setup debugging and review; they are not total preparation effort.
The specification focus checks and earlier #351–#356 framework development were
not instrumented by this trial. Their costs are unknown, not zero.

The two authors shared a host and worked concurrently. No token, backend-model
or sampling telemetry is available. One pair of attempts with different
prepared support does not establish causal superiority, human productivity,
or a broad agent-productivity advantage. Code size is supplementary; correctness,
retained selection and boundary obligations determine what was accomplished.

#107 remains paused, #108's reserved independent task remains unselected and
#260 remains inactive. The experiment does not justify a broad migration or an
unrestricted reverse compiler.
