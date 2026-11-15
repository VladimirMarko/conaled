# Chapter 1 Standards review — recovered unified-native run

Independent Standards reviewer:
`/root/chapter01_review_coordinator/standards`.
Source review completed 2026-11-03 at approximately 20:13 UTC.

## Current outcome

**Passed for the complete fourteen-path Chapter 1 candidate.**

Terminal evidence was reconciled on 2026-11-03 at approximately 21:11 UTC.
The required fresh compilation and exhaustive audit passed on exact clean
`07e480f6ec9958d4975bb90151005b84f2907614`; the preserved verification record
matches the actual record, all nine pinned dependencies and the official
Lean 4.35.0 compiler. **Unresolved Standards findings: 0; worst issue: none.**

This approves only the Standards axis on that immutable candidate against
the fixed original base and frozen requirements. The separate Spec outcome,
root's immediate `--verify-candidate HEAD`, and integration/acceptance remain
the coordinator's and caller's subsequent steps. None is claimed here.
The full terminal reconciliation and evidence identities appear below.

## Initial provisional outcome — retained history

**Blocked on completion of the required full candidate validation.**

The complete fourteen-path source Standards assessment is finished with
**zero concrete Standards findings**. No severity applies to the source result.
This is a provisional review outcome, not approval of Chapter 1. The running
check's source/coverage/compiler phase and historical focused success do not
establish full compilation, exhaustive audit or a successful candidate record.
The final evidence reconciliation will be appended to this same report.

The historical Standards reports and their applicability rulings are retained.
There was no earlier Standards source finding to close. SPEC-001, SPEC-002,
SPEC-003 and SPEC-V001 remain visible in the shared record; their dispositions
belong to the independent Spec axis and coordinator, not to this report.

## Immutable scope and continuity

- Fixed base and independently confirmed merge-base:
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `07e480f6ec9958d4975bb90151005b84f2907614`.
- Isolated checkout:
  `/workspace/scratch/31d6377eca78/fdsa/conaled-ch01-review`.
- Review comparison: `git diff BASE...CANDIDATE`; nonempty, fourteen paths,
  1,551 insertions and two deletions. No task source is excluded.
- The original unrelated untracked historical ZIP remains outside this task.
  Tracked candidate content is not excluded from review.
- Candidate HEAD and empty `git status --porcelain` were independently observed.
  `git diff --check BASE...CANDIDATE` exited zero.
- Six commits remain in scope: original implementation `1aabd51`, substantive
  repair `a14977b`, and proof corrections `057e07c`, `94d9af5`, `503081d`,
  `07e480f`. Their Conventional Commit messages retain issue `#174`.

This is the same logical Chapter 1 review loop, continued after workspace
recovery with a replacement live Standards reviewer. It does not replace or
erase the earlier reviews, source findings, failed checks or unknown run
outcomes. The supplied native kit and checkpoint packager are outside this
formal source diff. Their setup/recovery evidence cannot approve a theorem.

The frozen requirements were read and independently matched:

| Record | Bytes | SHA-256 |
| --- | ---: | --- |
| `chapter01-requirements.md` | 2672 | `7b7ce18bcfe9bb888ac9e99810a1095a823f9a67dbb54717c5bf673017a890ba` |
| `chapter01-cost-model-requirements.md` | 9471 | `1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1` |

The full governing `REQUEST.md`, retained author statement review, compiler
findings and shared `chapter01-round1.md` record were considered. The user's
explicit Nix exception and local-ticket/no-GitHub-write instructions govern;
the compiler/library pins and formal acceptance requirements remain unchanged.

## Applicable standards

Read the candidate's AGENTS; README environment/build/audit and proof-boundary
sections; architectural-quality and domain guidance; glossary; ADR index and
ADRs 0001/0010; shared language-direction document; example-driven-development
skill and worked example; code-review heuristics; and shared review procedure.
No applicable CODING_STANDARDS or CONTRIBUTING file was present in the ordinary
candidate inventory. No outside manuscript, upstream TODO or heuristic pattern
was treated as an additional undocumented standard.

The review checks reuse, separation of operations/observations/laws, suitable
assumptions, native clients, explicit interpretation/resource limits, meaningful
connected examples, statement review, public coverage and applicable validation.
It does not require a universal internal language before delivering these
bounded ordinary Lean constructions.

## Reuse of earlier analysis and complete source coverage

Both retained Standards reports were read:

- `chapter01-standards-round1.md`, SHA-256
  `46ffa26db5e0d100340856719fff5ffca730dbb5e015d872e20478253714db78`.
- `chapter01-cost-models-standards-preflight.md`, SHA-256
  `fdb52f4e70c8ef36d4b9bbfd37ed0684d5b271dc937bf0dbfec1d82fc79adcdb`.

Git-blob comparisons confirmed that the original six Lean files
(`EuclidInduction`, `CallCount`, `ListReversal`, `Measured`,
`Examples.FunctionalBasics`, `Examples.ListReversal`) and `docs/SOURCES.md`
are byte-identical to the original candidate `1aabd512284fe86254278ac631eda061d311050b`.
Their prior analyses therefore remain applicable. Their current full contents
were also read to verify the retained interfaces and connected uses.

The complete repair source was inspected: `CallComparison`, `SharedDemand`,
`Examples.CallModels`, `Examples.SharedDemand`, both FDSA research documents,
and the public-import delta. Necessary unchanged interfaces were inspected in
`Measured`, `Workload`, `Potential`, `Growth`, `SymmetricCosts`, and
`TreeFlattening.Core`, together with earlier erasure-square consumers in
`FoldCompiler`, `BinaryCounter`, `Dijkstra/Observation` and `Examples.Resources`.
No old-candidate validation credit is transferred by these source comparisons.

The complete `a14977b..07e480f` diff changes only proof scripts in
`CallComparison`, `Examples.CallModels`, and `Examples.SharedDemand`. Public
definitions, quantified statements, hypotheses, expected outcomes, imports and
warning policy remain unchanged. Specifically, the corrections retain natural
casts through norm simplification, qualify measured operations, unfold the
actual cache example, and remove unused proof syntax. The last prefix-cache
case still uses `request_hit`, `run_preserves_cached`, and `request_miss`.

## Architecture and statement assessment

### Foundational correspondences and existing algorithm reuse

`EuclidInduction.lean:13–28` supplies the branch-sensitive induction rule and
connects its second-argument orientation to standard `Nat.gcd`. The recursive
hypothesis is used only with the nonzero condition, which provides the strict
modulo decrease. The divisor client uses the new induction principle with
satisfiable premises; the zero boundary remains explicit.

`CallCount.lean:16–56` extends the existing measured-value algebra. Generic
application/control rules need only their stated additive structure; they do
not force commutativity. Primitive erasure uses the existing zero/addition
laws. Let evaluates its body at the actual returned value; condition and sum
cases retain only the selected arm. The natural tick is a declared count
convention, not automatic source-language or runtime cost inference.

`ListReversal.lean:23–114` reuses the actual copied-cell append and accumulator
reverse definitions. The additional terminal-entry charge has explicit append
equations, so copied-cell and call observations are not identified silently.
The naive recursive algorithm is defined separately and erases to standard
list reversal; its cost is not assigned to the standard library implementation.
The exact doubled identity justifies the triangular natural-division formula.
The bound and comparison include empty lists; strict improvement alone requires
nonemptiness. Arbitrary accumulator values and arbitrary payload universes are
preserved.

### Shared semantic interface and existing consumers

`Measured.lean:54–64` changes only `erasureSquare`'s universe signature, allowing
the cost carrier below the value carrier. Its implementation, erasure proof
contract, and equal-universe specializations remain available. New generic list
squares exercise the previously unsupported natural-cost case. The examined
prior callers retain their source interfaces; the full project build remains
the necessary confirmation of elaboration compatibility.

`Examples.ListReversal:42–63` uses a continuation square with the correct measured
input boundary and `bind` to preserve accumulated observations. Its pasted-square
theorem and direct/native client both recover the input after two reversals.
The independently expected 10+4 count checks that composition preserves both
observations. These are Type-level semantic contracts; no cross-setting
transport theorem is claimed by this universe adjustment.

### Uniform tariffs and qualified entry omission

`CallComparison.lean:20–90` uses ordinary lists and sums for the same charged
occurrences, including repeats. The refined observation retains each original
entry. Its upper inequality is derived from local bounds, while the finite
catalogue supplies one supremum independent of the input trace. The family
theorem fixes K before the eventual-input premise. Neither construction needs
a finite payload universe or an assumed whole-run inequality. Empty traces and
zero tariffs remain within scope.

The code's two real-cast asymptotic directions use Mathlib's established
interface. The pointwise and family entry comparisons at lines 92–121 retain
positive/eventually positive costs for the forward factor-two bound and no
positivity for the reverse direction. The measured tick and value-preservation
connections are actual public-law uses. The cofinally-zero example tests the
meaningful failure of a weaker non-identically-zero assumption.

The documentation at `fdsa-call-models.md:37–126` states the substantive local
coverage and root-entry conditions, labels the append tariff illustrative, and
excludes unbounded uncharged primitives/callbacks. The one-entry lemma is not
presented as a multi-definition compiler inlining theorem.

### Shared demand, values, and work

`SharedDemand.lean:28–163` separates the option cache, validity, actual request
transition, returned-value laws and repetition. A miss stores and charges its
fixed pure callback; a hit returns the stored value with zero callback charge.
Empty-cache validity is proved. Existing `run_invariant` propagates validity
and preservation of an already stored identity, giving value correctness after
arbitrary prefixes, including repeats.

`DecidableEq` is local to identities and updates, not payloads. `Fintype` starts
at the remaining-work section rather than restricting basic requests or value
laws. No payload equality, order, or inhabitance is imposed. Accounting remains
independent of validity: arbitrary stored payloads may affect meaning, but still
remove their identity's potential. Validity is supplied separately whenever
returned values are compared to the pure computation.

`SharedDemand.lean:169–248` proves exact local remaining-work conservation from
hit/miss transitions and finite-sum decomposition. It then uses existing
`run_potential_exact` to telescope along the actual executor. Natural
nonnegativity derives the bound; the desired total bound is never a premise.
The eager sum is a catalogue specification. Both source comments and
`fdsa-call-models.md:128–192` require external-program correspondence before
identifying it with an external eager execution. Cache administration and
physical runtime remain outside the supplied callback-work observation.

## Connected cases and methodology

The retained independent calculations and author statement-review record were
read. They agree with the candidate's cases and public-law connections:

| Case | Public connection and mathematical distinction |
| --- | --- |
| Euclid divisor and zero | New induction/gcd equation with satisfiable divisibility premises and `(0,0)` boundary. |
| Reversal boundaries and composition | Public exact/value/cost theorems; duplicates, distinguishable order, nonempty accumulator, empty input, singleton strictness, and total 14. |
| Control and argument observations | `primitive_rule`, `let_rule`, `arguments_rule`, `if_rule`, `case_rule`; expensive inactive arms expose selected-branch semantics. |
| Append tariff | Explicit branch equations and `appendEvents_cost`; `catalogue_refined_bounds` and `refinedCost_isBigO`; counts 17 versus 4, plus empty payload and zero tariff. |
| Entry omission | `tick_cost`, `add_entry_isBigO`, `tick_value`, and `zero_cost_entry_matters`; the intermittent family refutes an unsupported hypothesis weakening. |
| Shared repeated/unused work | `run_replicate_empty`, `run_cost_le_eager`, `run_work_remaining`, and `request_after_run_value`; five cheap demands cost 3, unused cost 1000 remains, demanded values remain 7/99. |
| Sharing boundaries | Infinite identities with arbitrary payload, distinct identities with equal payloads, arbitrary intervening requests, and empty catalogue/payload. |
| Duplicated recursive child | Actual request/bind layers, `sharedLayer_eager`, derived recursion laws, same values; depth four gives 16 with costs 5 and 31. |

Simple reduction cases supplement these connections appropriately. No per-helper
example quota or executable test suite is required for the purely formal
mathematical change. No observed statement is supported solely by its own
restated conclusion as a hypothesis. No new suspicious vacuity or unnecessary
capability assumption was found. Scope completeness against the book remains
the independent Spec axis's separate responsibility.

## Documentation, placement, and public integration

Definitions follow existing domain modules, while example modules retain reusable
specializations/compositions. The chapter order is a coverage index rather than
a second parallel module taxonomy. All ten changed Lean modules enter the
public import closure through four new example imports in `SquareApplications`.
The source map preserves source date/digest/provenance, the cost-model correction
and limits, exact statement pointers, and separate acceptance tracking.

The documents explicitly retain pending validation language and direct acceptance
status to the companion control record. Their conditional draft status is not
an acceptance claim. No full manuscript or large extracted source text was added
to the formal diff. The new local recovery packaging is outside this review.

## Initial validation status and retained mode dispositions

The historical four-target focused pass on exact `07e480f` remains supporting
compiler evidence only. C1-ELAB-001/002/003 have that focused confirmation;
source review here confirms their proof-only scope and preserved connections.
Their whole-candidate confirmation is still pending.

The current root-owned run is recorded at
`provenance/chapter01-unified-fresh-attempt4/`. Independently read `request.json`,
`start.json`, and the beginning of `full.log`:

- Start: `2026-11-03T20:08:58.985393+00:00`.
- Initial HEAD: exact `07e480f`; initial status empty.
- Command: supplied kit `run --project <isolated checkout> --threads 1 --
  ./check.sh --candidate HEAD --fresh --jobs 1`.
- Reported compiler: Lean 4.35.0, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
- Source guard passed; source/coverage/version phase reported success.
- The checker announced 961 local modules, with 960 build modules before the
  separate audit. The observed log was still partial; no terminal success or
  verification record was available at source-review completion.

Root selected one stock fresh baseline for the newly adopted native profile,
consistent with README's fresh-baseline rule. Fresh mode compiles private
project outputs and runs the exhaustive audit; it does not use incremental
output-integrity phases. The prior ordinary-mode permission remains limited to
its historical environment/evidence and does not impose a second ordinary run.

The retained validator-fixture applicability ruling remains valid for this
formal/provenance candidate: its checker, proof audit, compiler/dependency pins,
root-selection policy and integrity implementation are unchanged. No concrete
new evidence here triggers an additional fixture suite. The full candidate
audit is still mandatory. Environment setup or checkpoint round-trip success
cannot replace it. New integrity evidence would retain the runbook obligations.

No compiler, build, source-policy runner, cache writer, process stop/restart or
Git mutation was performed by this reviewer. The only permitted write is this
outside-source report. The root-owned isolated check may continue unchanged.

## Initial final-reconciliation hold — retained history

Before this axis can become Passed, inspect the actual terminal exit and complete
closed log, confirm successful full compilation and exhaustive audit, and match
the retained `.lake/verification.json` to the exact candidate, pinned dependency
revisions, compiler and fresh mode. Recheck source identity/cleanliness and retain
the evidence pointers and hashes. A partial count or ordinary per-module axiom
printout is insufficient. A failed or missing result keeps this axis Blocked.

The coordinator must also obtain the separate Spec outcome on the same full
scope. Immediately before accepting/integrating, root must execute stock
`./check.sh --verify-candidate HEAD` in the same isolated checkout and confirm the
approved commit. That final step is not claimed by this source report.

Current base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Current candidate: `07e480f6ec9958d4975bb90151005b84f2907614`.
Concrete Standards findings: **0**. Worst source issue: **none**.
Standards outcome: **Blocked — required final validation pending**.

## Completed terminal-evidence reconciliation — 2026-11-03

The same reviewer resumed only to reconcile terminal evidence. The completed
source assessment above is unchanged; no duplicate source review or new review
loop was started. The original full fourteen-path scope, fixed base, candidate,
frozen requirements and retained findings remain the review inputs.

### Actual successful run and retained identities

Read the root-owned actual result and verification JSON, the complete closed
log, the kit's retained command start/result/log, and the warning observation
under `provenance/chapter01-unified-fresh-attempt4/`. Independently recomputed
the following identities:

| Evidence | Bytes | SHA-256 |
| --- | ---: | --- |
| `result.json` | 1186 | `8f2a76c0f6b3adfb3c1f4c92f8e1aa946ac476cbe3e253869bf0ae1d65ae7873` |
| `full.log` | 201415 | `751732fbf985a26956e27eef716bf88834d41e885494884cd80aa858d9f40af2` |
| `verification.json` | 861 | `8d9257a238ab4c2e0743a41851a080f403aa09b41f4bf34690496c1f9a7b0264` |
| `kit-command-record/result.json` | 571 | `7e827619627c3594a02db8c82030b58356e56cca7c362825b83017a7965e3361` |
| `kit-command-record/output.log` | 201192 | `8a1d74b2d8923512f95ba8251f6d9ee06d803e3690f24bf31b44457a0ef0770e` |
| `warning-observation.json` | 8483 | `583bf6360c3dade04cb4c8fae084f50b1d0e591cf1f8f2878a52ec1a1199cc3a` |

The root recorder reports actual exit **0**, state `passed`, empty final source
status and exact unchanged candidate. It began at
`2026-11-03T20:08:58.985393+00:00` and completed at
`2026-11-03T21:08:58.959923+00:00`, elapsed **3599.974328367 seconds**, with
no progress-bookkeeping errors. The independent nested kit command record
also reports exit **0**, `passed: true`, `timed_out: false`, no recorder error,
the same checkout, command and thread setting. Its entire recorded output
is contained in the outer complete log. This is actual terminal evidence,
not a liveness inference from an old progress file.

### Full build and exhaustive audit

The closed 2,627-line log records the source-policy/public-coverage/compiler
phase, every numbered compilation from **1/960 through 960/960** in exact
sequence, the exhaustive audit and successful candidate-record write. The
checked candidate includes the `SquareApplications` public root. The checker
reports **all 961 local modules checked**, accounting for the separate audit
execution. Fresh compilation took **3534.78 seconds** and the audit
**62.74 seconds**. The reported full checker total is **3599.57 seconds**.

The final exhaustive audit reports **45,074 kernel-safe declarations**,
**24,929 theorem declarations**, and **959 project modules** contributing
to its module-directed audit inventory. Its transitive axiom union is exactly
`[propext, Classical.choice, Quot.sound]`, with **zero kernel-unsafe runtime
declarations excluded from logical roots**. The audit explicitly reports
PASSED. These figures are the actual final audit result, not the earlier
per-module printed axiom lists.

All ten library/example modules in this formal change compiled in the fresh
run and appear in the final audit inventory:

| Module | Logical declarations | Theorem declarations |
| --- | ---: | ---: |
| `Applications.Arithmetic.EuclidInduction` | 2 | 2 |
| `Applications.Resources.CallComparison` | 20 | 19 |
| `Applications.Resources.CallCount` | 9 | 7 |
| `Applications.Resources.ListReversal` | 31 | 22 |
| `Applications.Resources.Measured` | 17 | 12 |
| `Applications.Resources.SharedDemand` | 37 | 28 |
| `Examples.CallModels` | 20 | 15 |
| `Examples.FunctionalBasics` | 17 | 17 |
| `Examples.ListReversal` | 20 | 19 |
| `Examples.SharedDemand` | 53 | 38 |

Every row reports zero unsafe runtime declarations. This supplies the previously
missing full compiler/audit evidence for the repaired proofs and whole-project
compatibility, including the `erasureSquare` universe adjustment and earlier
consumers. C1-ELAB-001/002/003 therefore have matching whole-candidate compiler
confirmation in addition to their retained focused evidence. No unsuccessful
historical attempt is relabelled by this pass.

### Matching current inputs and warning disposition

The preserved verification JSON is byte-identical to the actual
`conaled-ch01-review/.lake/verification.json`. Its candidate is exact `07e480f`,
result is `passed`, mode is `fresh`, compiler is official Lean 4.35.0 at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and completion time is
`2026-11-03T21:08:58.639009+00:00`. Its nine dependency revisions exactly match
the unchanged `lake-manifest.json`. This reviewer separately read all nine
current dependency HEADs and statuses: every revision matches its pin and
every checkout is clean. The current candidate HEAD, clean status and original
merge-base were independently reconfirmed.

The complete log contains nonfatal warnings in 37 source files. The reviewer
read the warning headers and independently matched every warning record's
candidate/base Git blob identity. All 37 files are byte-identical to the
original review base and outside the changed source paths. The source review
already established that no warning policy was weakened. These warnings do
not constitute a newly introduced Standards finding or a failed proof result;
they remain in the complete retained log. No new validator-fixture or integrity
trigger was established by this evidence.

### Final Standards disposition and limits

The validation hold in the initial report is now resolved by actual successful
matching evidence. The source assessment remains zero findings. The prior
fixture-applicability ruling and fresh-mode scope are unchanged; no second
full build or new mechanical gate was introduced. This reviewer performed no
compiler/build command, process action, source/ref mutation, cache write, or
modification to the root-owned evidence. Only this report was updated.

**Standards: Passed**, with **zero unresolved findings** and **no worst issue**,
for candidate `07e480f6ec9958d4975bb90151005b84f2907614` against fixed base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, covering the complete fourteen-path
Chapter 1 scope and both frozen requirement records.

This report does not dispose the independent Spec findings, claim that root's
immediate `--verify-candidate HEAD` has occurred, or claim integration/chapter
acceptance. Both independent axes must pass the same candidate and root must
perform that immediate verification before accepting it. Further source edits
would require candidate-specific evidence and review under the retained loop.
