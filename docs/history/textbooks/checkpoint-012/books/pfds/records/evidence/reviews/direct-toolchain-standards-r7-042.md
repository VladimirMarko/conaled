# Native toolchain and recovery handoff — Standards review, r7-042

## Outcome

**Passed** for the complete operational-toolchain scope on immutable candidate
`af2c53dce68ebb122c81175312d6bb30df9aac05`. There are **zero new and zero
unresolved Standards findings**. DTS-001 and DTS-002 retain their original
Medium severity and their round-2 disposition, **fixed with review evidence**.
No evidence-access blocker remains for this operational review.

Reviewer: `/root/recovery_audit`, the independent Standards axis assigned by
`/root/direct_toolchain_validation_plan` within the existing review loop. I did
not author the implementation reviewed here. My earlier recovery-audit Markdown
and JSON reports are outside this source scope. I performed read-only source,
Git and retained-evidence inspection and wrote only this report. I ran no
compiler, test, build, cache, network, or protected-surface operation.

This outcome does not supply the independent Spec result, approve a different
candidate, or establish a formal full build, proof audit, candidate verification,
chapter completion, or completion of the PFDS book/thesis union.

## Immutable scope and review continuity

| Identity | Value |
| --- | --- |
| Fixed base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `af2c53dce68ebb122c81175312d6bb30df9aac05` |
| Retained ref | `refs/pfds-review/native-toolchain-r7-042` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-042-r7` |
| Diff | `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...af2c53dce68ebb122c81175312d6bb30df9aac05` |
| Commit | `af2c53d feat(toolchain): bind corrected focused native candidates explicitly` |
| Full scope | 18 added files, 3,308 inserted lines |
| Manifest | `session/validation/native-toolchain-candidate-r7-042.json` |
| Manifest SHA-256 | `257e31713ec28c4c12cafb7635ad14098f09d8bc765c79d541b7ff30d27ac593` |

I observed the exact candidate HEAD, empty isolated-checkout status, and
nonempty 18-file diff. The coordinator separately established the exact ref,
merge base, committed/isolated/delivered hash agreement, and requirement hashes.
The retained manifest supplies those identities. Its pending-validation field
describes capture time; the later r7 aggregate supplies actual validation.

I read every authored file in full, rather than reviewing only the last
correction. The earlier Standards reports and `session/reviews/direct-toolchain.md`
retain the prior analysis of the unchanged eight files and the complete
DTS-001/DTS-002 histories. Round 2 approved only those original eight helpers.
Rounds 3 and 4 were incomplete; rounds 5 and 6 were superseded without complete
approval. Neither those incomplete reviews nor matching test results are
treated as an earlier approval of the present expanded scope.

The full authored scope is:

| Area | Files read in the isolated candidate |
| --- | --- |
| Original profile and command interface | `session/environment/make-direct-toolchain-profile.py`; `session/environment/run-direct-toolchain.py` |
| Original public compiler checks | `session/environment/test-direct-toolchain.py`; `session/environment/test-direct-lake-build.py` |
| Original handoff and evidence controller | `session/environment/README-direct-toolchain.md`; `session/validation/run-direct-validation.py`; `session/validation/test-direct-validation.py`; `session/validation/direct-validation-runner-notes.md` |
| Complete environment handoff | `session/environment/RECOVER-ENVIRONMENT.md`; `session/environment/environment-route-comparison-042.md`; `session/checkpoint.py` |
| Native implementation | `session/environment/native-own-exe.c`; `session/environment/run-native-toolchain.py` |
| Native public contract fixtures | `session/environment/test-native-own-exe.c`; `session/environment/test-native-own-exe.py`; `session/environment/native-readlink-fixture.c` |
| Native evidence controller and refusal checks | `session/validation/run-native-validation.py`; `session/validation/test-native-validation.py` |

Formal candidate sources, runtime distributions and caches, historical evidence,
trackers/status, saved requirements and review records are excluded from the
authored diff. Their separate obligations continue. The complete checkpoint
generator is included because it was absent from the fixed repository base.
Comparison with the retained predecessor confirms that this task changes only
its generated README directions and restore-success pointer, not its archive,
hashing or restoration algorithms.

## Applicable requirements and standards

I read candidate `AGENTS.md`, README development-environment/build-and-audit
guidance, the implementation and TDD skills and the TDD test/mocking references,
the code-review skill and heuristics, `docs/agents/review-loop.md`,
`docs/agents/architectural-quality.md`, `GLOSSARY.md`, and ADRs 0001 and 0010.
There is no root `CODING_STANDARDS.md` or `CONTRIBUTING.md`; the nested
toolkit-authoring experiment's AGENTS file does not govern this scope.

The complete saved governing requests are `REQUEST.md`, `REQUEST-union-v2.md`,
`REQUEST-direct-toolchain-041.md`, `REQUEST-environment-handoff-042.md`, and
`REQUEST-native-toolchain-042.md`. The public seams and authored scope are
recorded in `session/environment/direct-toolchain-implementation-scope-041.md`.
The user permits exact Lean/Lake execution without Nix and subsequently asks
for a faster alternative to emulation. This overrides launch-through-Nix only;
it does not remove pinned versions, genuine compiler behavior, fresh validation
after a runtime/tooling change, isolation, source/proof policy, independent
review, local tracking, or checkpoint requirements.

The existing public Lean/Lake/stock-check seams are authorized by the task and
its saved scope. The new native fixtures observe the public `readlink` boundary
and actual launcher behavior. Controlled downstream error results are clearly
owned fixtures, not evidence of accessing or probing protected host paths.
No new library abstraction or integrated mathematical claim is added by this
operational diff, so formal statement review and full-library acceptance are
separate from its artifact-appropriate validation.

## Retained findings

### DTS-001 — Required fresh route and mode-bound verification

- Original severity: **Medium**.
- Original type: documented README/ADR 0010 validation-rule violation.
- Disposition: **Fixed with round-2 evidence; no regression in r7**.

The original controller still provides `full RUN_ID --fresh`, invokes unchanged
stock `./check.sh --candidate HEAD --fresh --jobs 1`, and binds retained
verification to its actual mode. The native controller preserves that contract:
`run-native-validation.py:148–203` checks the successful stock record, runtime,
exact full candidate, command/mode, dependency identities, snapshots and saved
log/verification digests. Lines 238–278 select the full/focus/verify route and
construct the same fresh command. The verify child receives only
`./check.sh --verify-candidate HEAD`; its mode comes from the retained full run.
The parser rejects fresh flags outside full mode.

The complete recovery guide explicitly requires the first full check in the
native environment to be fresh and serial. A successful focused run remains
development evidence. Native records remain distinct from historical QEMU
records; the added `runtime: native` check prevents treating a QEMU full-run
record as a native full-run record.

Round-2 red/green evidence and the original closure remain retained. The r7
public refusal tests establish the changed parser/locking behavior without
fabricating successful formal evidence. Source inspection preserves the fresh
route and mode-binding fix. Actual full formal success remains pending and is
not inferred from these tests.

### DTS-002 — Cold-recovery temporary-parent creation

- Original severity: **Medium**.
- Original type: recovery/fixture setup defect with a concrete failure path.
- Disposition: **Fixed with round-2 evidence; no regression in r7**.

Both unchanged smoke tests create `root / "session/tools"` before creating
their temporary projects. The native contract runner also creates its owned
fixture directory with parents. The r2 cold recovery and index-reconciliation
records retain actual CLI and Lake success with the temporary parent initially
absent. The r6 cold native aggregate separately records
`lake_temporary_parent_absent: true`, followed by genuine Lake compilation,
linking and execution with output `42`. The repaired behavior therefore remains
covered by matching retained public-interface evidence.

The original failed r2 aggregate remains failed: its review checkout lacked a
private index because of an inherited temporary `GIT_INDEX_FILE`. The separate
reconciliation repairs only that index and explicitly reuses successful tests
whose actual source/runtime inputs were unchanged. This does not retroactively
claim a clean original checkout or a successful formal candidate check.

## Full-scope assessment

### Native metadata and profile contract

`native-own-exe.c:28–90` resolves the next `readlink` implementation through
`pthread_once`, protects resolver reentry, delegates before considering the
fallback, and returns original successes and non-ENOENT failures unchanged.
The fallback is limited to this process's exact executable-link spelling,
a matching nonempty absolute per-exec marker and `AT_EXECFN`, a canonical path,
and a currently readable regular ELF. It truncates to the caller's size without
adding a NUL. Failed eligibility checks restore the underlying ENOENT; fallback
success restores the incoming errno. No raw syscall or access-permission change
appears in this source.

The explicit frozen-file/directory, valid-buffer, Linux/glibc/x86-64 and direct
ELF assumptions are material. The documentation and fixture records retain
the exclusions for scripts, loader/descriptor execution, mutable images,
async-signal handlers, invalid pointers, alternate entry points, static/secure
execution and other ABIs. I do not interpret the implementation or its tests
as general libc/procfs equivalence, authentication of a marker, or a proof of
compiler correctness.

The native profile builder verifies the three pinned original entrypoint
hashes, copies them unchanged, stages the new profile and refuses an existing
one. Its receipt records the adapter source/library and C compiler identities.
Read-only description checks the location and recorded executable/wrapper/source
identities. Generated shell commands quote paths and forward arguments.
Each compiler wrapper sets its own marker; the launcher clears stale inherited
markers and only assigns a direct-command marker to an eligible canonical
workspace ELF. Existing preload entries keep precedence and relative order;
unexpected inherited Lean/Lake selectors are refused. All runtime choices
remain child-local.

### Evidence controllers and tests

Both controllers preserve exclusive new evidence names, separate full/focus
locks, clean exact candidate checks, pinned clean dependencies, queued/start/end
input comparisons and actual child terminal results. Successful full evidence
requires a stock verification record; the presence of such a file alone is
insufficient. Signal handling addresses only the owned process group. Hard
interruption can still leave a nonterminal record, which the guide correctly
treats as unknown rather than a success.

The r7 change at `run-native-validation.py:242,269,379–381` admits only an explicit
lowercase 40-hex focus override, checks it against the actual clean HEAD in the
fixed signed-potential checkout, and records requested and resolved identities.
It does not alter the full/verify candidate. The corresponding fourth public
test checks invalid mode/ref rejection and the focused lock. The tests do not
replace Lean/Lake with mock compilers or invent a passing proof record.

The native fixtures use caller-supplied expected paths and literal expected
results, check buffer sentinels, and observe actual launcher and public ABI
behavior. Their controlled layer distinguishes delegated success, ENOENT,
EACCES, EPERM and EIO; instrumentation confirms the owned test layer was reached.
That fixture instrumentation does not establish a claim about protected host
paths. The retained original red failure predates implementation; later expanded
tests are not falsely described as earlier red outcomes.

### Recovery documentation and checkpoint integration

The complete runbook distinguishes PFDS checkpoints from the supplied guide's
other workstream, preserves the source/acceptance frontier, and provides exact
acquisition hashes, pinned dependency restoration, private project build
directories, compiler checks, cache invocation and native full/focus/verify
commands. Its `.lake` recipe rejects directory and build symlinks and does not
reset unknown source/dependency checkouts. The source runbook and checkpoint
entry instructions agree about the Nix exception. The historical QEMU guide
and helpers are retained as a scoped fallback, not relabelled as native results.

I inspected the supplied guide's relevant embedded launcher and the retained
Ubuntu authentication report/input record. The comparison correctly distinguishes
reported other-session behavior from acquisition checks performed here, attributes
the public keyring trust input, and does not infer runtime superiority from a
newer emulator. Its native performance discussion retains the single-pair and
I/O variability limitations rather than asserting a general speedup. No other
conversation's file was accessed for this review.

The checkpoint generator still preserves all named refs and session records,
checks captured hashes, and exercises restoration. The task's two documentation
changes do not alter its pre-existing implementation. The predecessor hash
`617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab`
and the exact comparison are retained. Future checkpoint creation must still
produce its actual restore result and immediate durable delivery; this review
does not claim that a new checkpoint has already been generated.

No additional documented-standard violation or actionable heuristic defect was
found. The duplicated historical/native controller structure is constrained by
their distinct preserved runtime evidence; no speculative refactoring or
additional optional test run is required for this review.

## Validation evidence and limits

The r7 aggregate is `session/validation/native-toolchain-candidate-validation-r7-042.json`,
SHA-256 `e142a541377e59027008d2299fc19dcb9b5a1613cc460409ffbf90c9ae3b8176`.
It is passed, identifies this exact candidate and clean status, retains all
delivered hashes, and explicitly separates new checks from matching-input reuse.

| Evidence | Established result and scope |
| --- | --- |
| r7 aggregate | Four native-controller refusal tests returned zero; shell examples passed syntax checks; two Python recovery recipes passed their existing-state verification branches. This is not a complete new network acquisition or cold source restoration. |
| `native-toolchain-candidate-validation-r6-042.json` | Actual new cold native profile construction and description, exact Lean/Lake versions, a valid implicit-Init theorem accepted without axioms, and a false theorem rejected with a genuine type-mismatch diagnostic. |
| `native-cold-profile-r6-042.json` | Exact unchanged original/real executable hashes, native adapter/helper hashes, construction command and C compiler identity. |
| `native-candidate-lake-r6-042.json` | Lake selected the cold native compiler, compiled and linked the small executable, and ran it with exact output `42`. |
| `native-candidate-contract-r6-042.json` | All 18 public metadata/launcher cases passed; raw observations and command results are retained; all recorded inputs before and after match. |
| Earlier native CLI/Lake records | Genuine broader `import Lean` acceptance/rejection and native executable results remain retained. They are distinguished from the minimal cold r6 CLI cases. |
| r2 reconciled aggregate and final identity record | Actual original-helper public tests and their narrowly justified reuse after index-only repair; both earlier finding closures remain recorded. |

R7 identifies 14 unchanged source files from the r6 snapshot, including the
native implementation/fixtures and original eight helpers. Only the two current
handoff documents and native evidence controller/test changed; their applicable
checks were rerun. The original eight helpers also match their approved r2
manifest. This is reuse of actual tests on identical relevant inputs, not reuse
of a missing r6 review outcome or approval of the entire candidate by test hash.

The native implementation removes emulation from the exercised compiler route;
it does not establish predictable project build time. The metadata fixtures,
small native program and smoke theorems do not replace the full integrated
build or exhaustive proof audit. Formal full901 validation remains a separate
gate; d24/956 failures and corrected candidate3cf3de4f retain their independent
source/evidence histories. No mathematical acceptance is advanced by this report.

## Final record

- **Standards outcome:** Passed.
- **Retained findings:** DTS-001 fixed with evidence; DTS-002 fixed with evidence.
- **New findings:** 0.
- **Unresolved findings:** 0.
- **Worst unresolved severity:** None.
- **Validation/access blockers for operational scope:** 0.
- **Base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- **Candidate:** `af2c53dce68ebb122c81175312d6bb30df9aac05`.
- **Acceptance boundary:** The caller must reconcile both independent axes and
  confirm delivered task bytes still match this candidate before operational
  acceptance. Formal gate, audit, source review and immediate final verification
  requirements remain unchanged.

This report is complete and frozen for r7-042. It does not erase earlier reports
or approve later modifications.
