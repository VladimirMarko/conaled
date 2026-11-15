# #1027 — Optional cache companion review

Current review outcome: **Standards Passed; Spec Passed**, round 2, candidate
`a43cef4881d4eb303a81ef25f5ccff0b801a12fe`. No unresolved findings. This is
review approval; caller acceptance and actual checkpoint operations have their
separate required records. Earlier findings and outcomes remain historical below.

## Scope and controlling evidence

This is the single ordinary implement/code-review loop for the standalone
operational recovery utility and its explicit durability amendment. The
coordinator reconciles the independent Standards and Spec reports; it is not
an additional review axis. No chapter acceptance is implied.

- Operational repository: `work-state/cache-companion/`.
- Fixed empty base: `6f48c1ab7f1e96056c217ca025390aa58a7955b6`.
- Saved requirements: `work-state/specs/1027-cache-companion.md`.
- Requirements SHA256:
  `9d46adc3d69359b29196a615865ce7503a1a073da007cec34dd187da15807f86`.
- Historical full requirements remain unchanged. The amendment is ineffective
  until both independent axes pass the same tested operational candidate and
  root verifies the delivered content against it.
- The formal conaled candidate, active gate, chapter dependencies and every
  original acceptance requirement remain separate and unchanged.
- No source, test, documentation or vendored adapter in this task is excluded.

## Applicable standards

Conaled standards were read from unchanged candidate
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`:
`AGENTS.md`; `.agents/skills/code-review/SKILL.md` and `heuristics.md`;
`docs/agents/review-loop.md`; `README.md` development/build/audit sections;
`.agents/skills/tdd/SKILL.md` and its test/mocking references;
`.agents/skills/writing-for-agents/SKILL-MECHANICS.md`; and
`docs/agents/lake-integrity-incidents.md`.
No `CODING_STANDARDS.md` or `CONTRIBUTING.md` was found.
User-authorized local tracking replaces GitHub writes.

## Round 1 — pinned candidate and validation

- Candidate: `5066fb9d0d0963122332149b3b6984ebea3facda`.
- Tree: `2352eb7a03454d1da1f9be8d0887e7ae830118d4`.
- Verified merge base: `6f48c1ab7f1e96056c217ca025390aa58a7955b6`.
- Diff: `git diff 6f48c1ab7f1e96056c217ca025390aa58a7955b6...5066fb9d0d0963122332149b3b6984ebea3facda`.
- Commit: `5066fb9 feat(recovery): add optional checked project cache companion (#1027)`.
- Full eight-file scope: `.gitignore`, `AMENDMENT.md`, `README.md`,
  `cache_companion.py`, `check_pinned_runtime.py`, `test_cache_companion.py`,
  `vendor/lake-output-hashes.lean`, `vendor/lake_integrity.py`.
- Isolated validation checkout: `cache-companion-validation/`; its exact HEAD
  and clean index/working tree were independently confirmed by the coordinator.

Validation evidence is retained in
`validation/1027-candidate-round1.json`,
`validation/1027-round1-validation.json`,
`validation/1027-round1-tests.log`, and
`validation/1027-round1-pinned-helper.json` / `.log`.
The coordinator verified both log SHA256 values against the validation record.
The initial capture record's validation status was pending at capture time;
the subsequent validation record records actual completion and a clean checkout.

The isolated Python suite passed all 16 tests in the pinned Nix environment
(raw return code 0). Exactly one actual bounded, one-worker invocation of the
unchanged Lake helper passed on two **34-byte** literal private files, with
three requested hashes (one repeated input). The handoff's 33-byte description
was a prose error; the retained measured evidence records 34 bytes. Results:
`d51ab7bea8996f7d`, `074c331011a828ab`, `d51ab7bea8996f7d`.
The actual compiler was Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Linux/x86_64/little-endian.
No compiler artifacts were generated and the private fixture directory was
removed. These are tool/interface checks, not actual project-cache capture
or formal proof validation. Prior TDD attempts include honest failures and
are retained as history, not successful acceptance evidence.

Matching checks are reused. No extra Lean/helper/compiler run is authorized
for this review, and broad repetition of successful tests is unnecessary.
A targeted synthetic check may resolve a concrete risk under the pinned
Nix environment. No active cache/source/build changes or GitHub writes occur.

### Standards

Outcome: **Findings-present**. One unresolved finding; worst severity **Medium**.
Independent reviewer: `/root/cache_review/standards`.

#### ST-CACHE-001 — Medium — A FIFO can block before the regular-file check

Status: **Unresolved on round-1 candidate 5066fb9**.

Location: `cache_companion.py`, `_regular_file`, candidate line 139; reached
from capture through `_read` and `_copy_artifact`, and from archive
verification through `_checked_tar`.

The final path component is opened with:

```python
os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory)
```

The regular-file check happens afterward using `os.fstat`. Opening a FIFO for
reading without `O_NONBLOCK` waits for a writer, so the operation can hang
before it discovers that the path is not a regular file. The helper's
60-second timeout does not cover this earlier file open.

The reviewer confirmed the consequence through the public `create_companion`
API in a private synthetic checkout. Replacing the expected `One.trace` file
with a FIFO caused the call to block until the probe's own two-second timeout
stopped its subprocess. It printed the marker immediately before capture and
never returned. The temporary fixture directory was removed afterward.

Evidence: `validation/1027-standards-fifo-probe.json`, SHA256
`b0d6f7fe25de43dfdeca534061fd02538d82723be302d5009fb015234de4d62e`.
The coordinator independently verified the evidence digest and its measured
2.006-second timeout result. The probe was already in flight when the checkpoint
freeze arrived, then completed before the writer-paused acknowledgement.

Classification: a concrete robustness judgment, not a claim that conaled
prescribes a particular POSIX flag. Code-review guidance requires an identified
consequence and appropriate remedy. The documented capture contract also says
nonregular inputs are rejected and affected families omitted whole; here that
rejection cannot be reached.

Remedy: open the final component without blocking, then reject anything that
is not a singly linked regular file before consuming bytes. Adding
`O_NONBLOCK` to the existing no-follow open while retaining descriptor-based
type and identity checks is a straightforward POSIX remedy. Add a bounded
public-interface regression proving a FIFO family is rejected promptly while
another valid family can still be captured. The shared opening fix should
also cover a FIFO supplied as the archive path.

#### Remaining Standards assessment and validation

The reviewer reused the exact candidate's successful 16-test isolated suite
and single actual pinned-helper check. Both validation-log hashes match their
records. The isolated checkout remained clean after the targeted FIFO probe.
Both vendored adapters are byte-identical to their source files at conaled
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`. The two historical requirements
files and existing source-checkpoint generator retain their recorded hashes.

The test suite uses real private files and Git repositories; substitution is
confined to the external Lake runtime. The amendment, documentation and API
preserve the distinction between optional cache recovery and formal
acceptance, retaining complete source checkpoints, guarded validation and
independent review. Prior TDD attempts honestly retain failures, including
nonzero results in files whose intended-phase labels contain "green"; those
failures were not used as acceptance evidence.

No actual cache capture, additional Lean/helper invocation, formal-source
change, active-build intervention or GitHub write was performed by the
reviewer. The bounded synthetic FIFO probe was the sole additional executable
check. No other Standards findings were identified in this candidate.

### Spec

Outcome: **Findings-present**. One unresolved finding; worst severity **Medium**.
Independent reviewer: `/root/cache_review/spec`.

#### SP-CACHE-001 — Medium — A nonregular input can block before required rejection

Status: **Unresolved on round-1 candidate 5066fb9**.

Location: `cache_companion.py`, `_regular_file`, candidate lines 139–143;
reached by trace reads, artifact copying and archive verification.

Capture requirement 5 requires singly linked regular files and omission of
unsupported families. Recovery requires safe regular-file archive inputs.
An unsupported file should be rejected without preventing completion.

The routine opens the final path using `os.O_RDONLY | os.O_NOFOLLOW`, then
performs `fstat` and the regular-file check after that open returns. Reading
from a FIFO can wait for a writer. A FIFO at an expected trace path therefore
prevents capture from reaching rejection and whole-family omission. The
helper's 60-second timeout does not cover this earlier operation. The same
shared routine exposes archive verification to the behavior.

The Spec reviewer independently identified the issue, then reused the completed
Standards reproduction instead of repeating it. Evidence is
`validation/1027-standards-fifo-probe.json`, SHA256
`b0d6f7fe25de43dfdeca534061fd02538d82723be302d5009fb015234de4d62e`.
The synthetic `One.trace` FIFO produced the marker immediately before the
public `create_companion` call, with no return before the owned subprocess's
2-second timeout; measured elapsed time was 2.0063617569976486 seconds.
The private fixture was removed. No Lean/helper invocation, actual project
cache or formal source was accessed by that reproduction.

Consequence: an unsupported cache entry can indefinitely prevent checkpoint
creation, and a FIFO archive path can hang verification instead of being
refused.

Required correction: make the final-component open nonblocking while retaining
no-follow, regular-file, link-count and identity checks. A prior no-follow
stat may improve early refusal but must not create a replacement race that
restores blocking. Add a bounded public-interface regression showing prompt
omission or refusal without publication or live-cache modification.

This is the same underlying defect as ST-CACHE-001. Both independent finding
IDs and dispositions remain recorded separately.

#### Remaining specification assessment

No other unresolved Spec deviations were found in this candidate.

| Requirement area | Assessment |
| --- | --- |
| Amendment and historical requirements | Explicitly covers cache exclusion and standalone completeness, retains mandatory cache-free source checkpoints, and remains pending until reviews and final content verification pass. |
| Binding and input identity | Requires source-checkpoint binding, clean matching commit/tree, integrated source digests, configuration/toolchain/Nix identities, dependency pins and compiler/platform identity. Successful-upload receipt construction is correctly an operator responsibility. |
| Inventory and complete families | Fixed module-derived paths, declared output variants, raw trace preservation, whole-family omission and zero-family refusal are present. Excludes setup files, sidecars, dependency caches and success records. |
| Private-copy consistency | Streaming SHA256 copies, descriptor/path checks, post-hash live-family rechecks, private guard validation and pinned Lake hashes follow the design, apart from SP-CACHE-001. |
| Hashing limits and provenance | One worker, a 60-second helper bound, file/cohort limits and separate SHA256 transport checks are implemented. Trace agreement is correctly distinguished from source provenance, authentication and chapter acceptance. |
| Archive verification/publication | Uses the same anchored archive descriptor, bounded inventory, exact members and payload digests, complete family descriptions and extraction verification before no-clobber publication. |
| Restore | Explicit idle acknowledgement, clean compatible inputs, absent/empty destination checks, link rejection, independent extracted files and exclusion of success-record restoration are present. Cross-root reuse remains uncertain. |
| Acceptance/scope | Original formal gates remain mandatory. No later chapter algorithm, conaled build configuration or formal claim changes. |

The reviewer independently verified both vendored adapters against conaled
candidate `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec` and their recorded SHA256
identities. The supplied exact-candidate isolated validation establishes all
16 existing tests passing and a clean checkout. The one required real-helper
smoke passed on two 34-byte literal files using pinned Lean 4.35.0, including
repeated-input agreement and no generated compiler artifacts.

These successful results are reused; the FIFO evidence is an additional
failure outside their coverage. The Spec reviewer ran no additional tests,
Lean/helper processes or implementation/shared-record writes. No real project
cache archive has been captured or restored. Spec approval remains withheld
until SP-CACHE-001 is resolved on a corrected, validated immutable candidate.

### Coordinator disposition

Round 1 is complete. Standards and Spec each report **Findings-present**, with
one unresolved Medium finding on immutable candidate 5066fb9. ST-CACHE-001
and SP-CACHE-001 concern the same demonstrated blocking-open defect; their
independent dispositions are retained separately. There are no other reported
findings, and the existing successful validation is correctly scoped.

Root is the implementer for the correction. A new round must use the same fixed
base, a new immutable candidate, matching isolated Python regression evidence,
and both original axes. Reuse unchanged helper evidence only when its relevant
source/runtime/configuration identities still match. The amendment remains
ineffective, and no actual cache companion may be captured or finalized until
both axes pass the same tested candidate and root verifies final delivered
content. No extra ordinary review loop or third axis is added.

Record opened UTC: 2026-11-02T13:52:13.900959+00:00

## Round 2 — FIFO correction

- Fixed base and verified merge base:
  `6f48c1ab7f1e96056c217ca025390aa58a7955b6`.
- Candidate: `a43cef4881d4eb303a81ef25f5ccff0b801a12fe`.
- Tree: `27b06c3e118792cc5a27820540ce22d820ad3ca0`.
- Full diff: `git diff 6f48c1ab7f1e96056c217ca025390aa58a7955b6...a43cef4881d4eb303a81ef25f5ccff0b801a12fe`.
- Full scope: the same eight added files, with no exclusions.
- Commits: original `5066fb9` plus
  `a43cef4 fix(recovery): reject FIFO inputs without blocking (#1027)`.
- Requirements remain SHA256
  `9d46adc3d69359b29196a615865ce7503a1a073da007cec34dd187da15807f86`.

The coordinator independently verified the refs, ancestry, complete eight-file
scope, new tree, operational HEAD/clean status and isolated validation
HEAD/clean status. The correction changes only `cache_companion.py` and
`test_cache_companion.py`: a nonblocking final-component open with explanatory
comment, plus two bounded public regressions covering a FIFO module family
alongside a good family and a FIFO archive path. The original round-1 reports
and their independent finding IDs remain above.

Exact isolated evidence: `validation/1027-candidate-round2.json`,
`validation/1027-round2-validation.json` and `validation/1027-round2-tests.log`.
All **18 tests passed**, raw exit 0, with a clean final isolated checkout.
The coordinator verified the test-log SHA256:
`8eea00a17b7b2498b87f50b2fb5899d76e21009b43977f6b9cfbf55340944811`.
The added regressions first failed by timeout on the old implementation;
`validation/1027-ST-CACHE-001-red.json` / `.log` preserve that actual result.

The one prior actual-helper smoke check is reused. The candidate evidence
records unchanged smoke script, vendored guard/helper, amendment and guide,
and identical `PinnedLake`, `_sha`, `HERE` and `HELPER_SHA` source segments.
Formal source/configuration remains the same clean 3279bac checkouts; no
additional helper/compiler or actual cache capture occurred. Each original
review axis assesses the new full candidate with these matching inputs,
retaining prior unchanged analysis instead of duplicating mechanical work.

### Round 2 Standards

Outcome: **Passed**. **ST-CACHE-001 is fixed with review and regression
evidence** on candidate `a43cef4881d4eb303a81ef25f5ccff0b801a12fe`.
New findings: none. Unresolved Standards findings: **0**.
Independent reviewer: `/root/cache_review/standards`.

The final-component open now includes `os.O_NONBLOCK` with `os.O_RDONLY |
os.O_NOFOLLOW`. Existing descriptor-based checks still reject nonregular,
multiply linked and oversized files before reading; before/after identity
checks remain intact. A FIFO no longer waits for a writer before reaching
`fstat`, while ordinary regular-file reading behavior is preserved.

The reviewer verified both bounded public-interface regressions: capture
omits the FIFO trace family while a valid second family survives, and archive
verification promptly rejects a FIFO archive. Both preserve the FIFO itself.
The red run records both tests timing out after five seconds on the old
implementation. Both now pass alongside the earlier cases: 18 tests, raw exit
0. The reviewer independently verified the exact test-log SHA256 recorded above.

The full eight-file task was reassessed using retained round-one analysis and
the entire correction diff. Only the anchored open, its explanatory comment
and two FIFO regressions changed; the other six files are byte-identical.
Amendment, guide, vendors, smoke script and runtime invocation code remain
unchanged, so the single prior actual-helper result is appropriately reused.
No extra helper or synthetic check was run without a remaining concrete risk.

Both operational and isolated checkouts were verified clean at a43cef4, and
the requirements hash is unchanged. This approval covers the operational
utility/amendment only, with no chapter credit, real-cache provenance
certification or replacement of formal gates. The reviewer made no
implementation, shared-record, cache or formal-source changes in this round.

### Round 2 Spec

Outcome: **Passed**. **SP-CACHE-001 is fixed with verified review evidence** on
candidate `a43cef4881d4eb303a81ef25f5ccff0b801a12fe`.
New findings: none. Unresolved Spec findings: **0**.
Independent reviewer: `/root/cache_review/spec`.

The correction adds `os.O_NONBLOCK` to the final-component descriptor open,
allowing a FIFO to reach the existing `fstat` rejection without waiting for a
writer. `O_NOFOLLOW`, regular-file and single-link requirements, file-size
bounds, descriptor/path comparisons and descriptor cleanup are preserved.
The capture regression promptly omits a FIFO trace while retaining a valid
second family; the archive regression promptly refuses a FIFO input. Both
confirm that the FIFO remains present rather than being modified or replaced.

Both regressions first failed on the old implementation at their five-second
subprocess timeouts. The corrected isolated candidate passes them and all
previous tests: 18 tests, raw return code 0. The reviewer examined the retained
red evidence, round-2 candidate identity, validation JSON and test log,
independently verified the test-log SHA256, and confirmed the exact isolated
candidate has a clean checkout.

The complete task was reassessed with the retained round-one assessment. The
round-to-round change comprises only the final-component open/comment and the
two bounded FIFO regressions plus their import. The specification, amendment,
guide, capture/verification/restore behavior and adapter provenance otherwise
retain their earlier complete assessment.

The prior real-helper smoke remains applicable: its script, vendored helper
and guard, `PinnedLake` implementation and relevant hash/path dependencies
are unchanged. That evidence records one bounded invocation on two 34-byte
literal files with the pinned compiler. No second helper call is required.

The reviewer independently rechecked the unchanged historical requirements
and existing source-checkpoint generator:

| File | SHA256 |
| --- | --- |
| `work-state/REQUIREMENTS.md` | `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84` |
| `work-state/specs/1002-full-requirements.md` | `43dbf2c1104ec2503a0dc89206001fd541daaf7f677ad7e89c7fcbda61f5939a` |
| `work-state/tools/checkpoint.py` | `deeb1cfc3255bff5d4f493d8906c821751006eadd0f1e88583f12f1ff0d4eece` |

Approval concerns this operational utility and amendment. It does not claim
that a real companion has been captured, uploaded or restored, or that any
chapter gate has completed. Root still performs final delivered-content
verification and records acceptance, then creates and uploads a complete
source checkpoint containing the accepted utility and evidence before actual
cache capture. Every original formal gate remains mandatory. This reviewer
performed read-only review/identity checks and reused matching validation;
no implementation or shared-record edits were made.

### Round 2 coordinator disposition

Both original independent axes have **Passed** the same full candidate
`a43cef4881d4eb303a81ef25f5ccff0b801a12fe`, with **zero unresolved findings**.
ST-CACHE-001 and SP-CACHE-001 are separately fixed and verified; no new
findings were identified. Full scope, requirements, exact isolated validation
and the unchanged helper-evidence reuse match across the two assessments.

The ordinary review loop is complete for this operational candidate. Root
must verify the final delivered content against this exact approved snapshot
and record the amendment's acceptance before actual cache capture. The next
complete source checkpoint must preserve the accepted utility and full
review/test evidence and be exposed/uploaded before its linked companion is
created. This disposition supplies no chapter acceptance, success record,
cache provenance certificate or waiver of the original formal gates. No third
review axis or duplicate ordinary review is required for unchanged content.
