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

## Operational follow-up 1 — concrete recovery pair source023/cache001

This is a bounded follow-up within the existing accepted #1027 loop. It
reviews the concrete recovery guide and recorded first capture/publication
sequence; it does not reopen the unchanged utility implementation or create
a new formal acceptance gate.

The approved operational candidate remains
`a43cef4881d4eb303a81ef25f5ccff0b801a12fe`, tree
`27b06c3e118792cc5a27820540ce22d820ad3ca0`. The coordinator checked clean
HEAD/index/working-tree status and compared all eight live files directly
with their approved Git blobs: **zero source deltas**. Both original review
axes assess the operational evidence independently.

### Preservation and exact reviewed inputs

The complete 22,206-byte approved source-review record is preserved unchanged
at `reviews/1027-cache-companion-approved-a43cef4.md`, SHA256
`f547a6c27fed94ee9275ca93f039371bc01cf4e99a0331053b3a8ff013ab29ef`.
It is also the exact prefix preceding this appended follow-up. The original
acceptance record is unchanged; its historical review hash remains directly
recoverable instead of being confused with the expanded record's new hash.

Input identities, the eight unchanged source-file hashes and the ordering
correction evidence are pinned in
`validation/1027-operational-followup001-inputs.json`, SHA256
`e1096ef2cc88b0f968ac818c3d4f28d27b8a1626446d7c3969402ae563378eb5`.
The STATUS and ticket-file hashes identify the observed workflow snapshot;
subsequent ordinary status updates do not retroactively alter that snapshot.

| Reviewed input | Bytes | SHA256 |
| --- | ---: | --- |
| `work-state/CACHE-RECOVERY.md` | 4392 | `be39ebe8d6217d375936ff13d5f73ee5112b6ee824dc3a8316022076f55460ae` |
| `work-state/cache-companions.json` | 1044 | `5a6049c6ad4f589e641cc541bf64a2e743ebda295aa6ddfaa92df54410157f74` |
| `work-state/validation/cache-companion001-source-binding.json` | 313 | `933ef95c7660bc5c7cb3bbe3314d7f242714e92bcaf36bc37bc5e524b5e7b907` |
| `work-state/validation/cache-companion001-launch.json` | 1460 | `0f8e5d497205f7461b53932b092786709109ad2606736141ada39bf8560c2818` |
| `work-state/validation/cache-companion001-attempt1.json` | 1460 | `0f8e5d497205f7461b53932b092786709109ad2606736141ada39bf8560c2818` |
| `work-state/validation/cache-companion001-created.json` | 726 | `6cf83fd69dc5072a84a2f3227337afb1dc60df9bf9543b793c1efb0c761d8212` |
| `work-state/validation/cache-companion001-upload.json` | 680 | `93c84e6f49c7478af58d74447ee50af7f84f1951fe192db4078152a14b4d623d` |
| `work-state/validation/cache-companion001-upload-verification.json` | 815 | `6e04efc60da9859292c15f0bbf7824574a8350ed73f6295f8107fd0e246bb5ac` |
| `work-state/validation/cache-companion001-capture.log` | 319 | `07591a20ca6d2609b83bdfbb70ebff1067cfa8060ce5ce0903bc6cea84c9a52b` |
| `work-state/validation/checkpoint023-created.json` | 437 | `d3680c5be553413eb4f34e8a5a0bea024774d0abb82a714f80968dad620524ef` |
| `work-state/validation/checkpoint023-upload.json` | 703 | `90aeeecd8d273d3f8673859f74713b0f49256354d9f7889c85e07148ba702963` |
| `work-state/validation/1027-acceptance.json` | 2051 | `736bf500005e21ac5072fa207f07b97cd59dc5d720afd84279cd1bb5e6996585` |
| `work-state/validation/1027-final-content-verification.json` | 2405 | `66e8722e26c8846d3f2eb34dc5cfe48aeabe714220122bf4560a669495d691b9` |
| `work-state/specs/1027-cache-companion.md` | 9198 | `9d46adc3d69359b29196a615865ce7503a1a073da007cec34dd187da15807f86` |
| `work-state/cache-companion/README.md` | 9691 | `69fc868da5fdb95d76a921f9376489aa5380e6c941bbacd0d25fb40dd32d1b18` |
| `work-state/cache-companion/AMENDMENT.md` | 2924 | `f66b1aa410d3476128c3bcfe2731034cb84505ca68d1fe304505e34a054c7651` |
| `work-state/reviews/1027-cache-companion-approved-a43cef4.md` | 22206 | `f547a6c27fed94ee9275ca93f039371bc01cf4e99a0331053b3a8ff013ab29ef` |
| `work-state/validation/1027-operational-guide-before-order-fix.md` | 4392 | `1688c27e7e79e8b8302d494a83717f8609e881823cb5460e378d056efa25eba1` |
| `work-state/tickets.json` | 70078 | `7deb4317f71b28f4f1fdba609381855b36fc6523fbba5a74dd2eb68bb4887f52` |
| `work-state/STATUS.md` | 41935 | `6b3eda18e53f1728f4bfdab2c70b8b1490a4ff15b356f9c66ce081b0e70c8099` |

### OP-CACHE-001 — binding construction preceded by its consumption

Observed initial-guide issue, reported by root from an independent read-only
assessment: recovering from source checkpoint023 alone requires reconstructing
its binding JSON, because that checkpoint predates the first cache capture.
The initial guide placed this reconstruction after the verification/restoration
instruction that consumed the binding.

Root swapped numbered steps 3 and 4 so reconstruction occurs first. The frozen
corrected guide is SHA256
`be39ebe8d6217d375936ff13d5f73ee5112b6ee824dc3a8316022076f55460ae`.
The previous guide is preserved at
`validation/1027-operational-guide-before-order-fix.md`, SHA256
`1688c27e7e79e8b8302d494a83717f8609e881823cb5460e378d056efa25eba1`.
The coordinator reversed only this step swap and its numbering and reproduced
the exact previous digest, establishing that every other byte is unchanged.
This is an operational-guide correction, not an accepted-source delta.
Independent confirmation of its disposition belongs to the reports below.

### Recorded operation and evidence limits

- Utility/amendment acceptance was recorded at 2026-11-02 14:07:04 UTC.
- Complete source checkpoint023 was created at 14:24:43 UTC with successful
  bundle, fresh restore and source/index/workflow stability checks. Its
  recorded successful upload supplies the exact source binding used later.
- Actual cache capture ran from 14:45:26 to 14:45:56 UTC, raw return code 0.
  Its result reports 504 retained families, 449 omissions, 249,142,110 payload
  bytes and a passed private extraction/inventory/digest check.
- The final archive is 81,938,603 bytes, SHA256
  `d368761921b3919844fd3c964ded7fd42e2f5ff25ec5f13d24707d8fbd01dc1c`,
  with successful upload receipt `libfile_92fa73b259e4819190db24b064241592`.
  Root reports immediate exposure/upload after creation. The saved post-upload
  verification at 14:46:57 UTC records full SHA256, size and local binding
  agreement with that receipt.
- Its exact source binding remains checkpoint023, 145,936,501 bytes, SHA256
  `92dc6cc6a95847c3cafd21087ca8c2fa8f6d515a28d9eb8db28680a6a5d3ed17`,
  `libfile_34c277ab17e08191a7e09db07802c467`, source commit
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.
- Checkpoint024 is prospective and will preserve the new receipt/guide/tracker
  state. The guide does not claim that its upload has already happened and
  does not rebind the cache to it.

The follow-up reuses saved capture, upload and verification evidence. No test,
helper/compiler invocation, archive rehash/extraction, mutable-cache read,
process/storage survey, remote read or code change is performed. It is not an
independent replay of capture or a remote-file availability/authenticity audit.
No chapter acceptance, current build percentage, cache provenance certificate
or waiver of the original formal gates follows from these records.

### Operational Standards

Outcome: **Passed**. OP-CACHE-001 is fixed; **zero unresolved operational
Standards findings**. Original independent reviewer:
`/root/cache_review/standards`.

The reviewer verified corrected guide SHA256
`be39ebe8d6217d375936ff13d5f73ee5112b6ee824dc3a8316022076f55460ae`.
Binding reconstruction is now step 3, before verify/restore in step 4, so
source023-alone recovery has its required binding before use. Comparing the
preserved earlier guide against the corrected guide confirmed only that
step exchange and renumbering; the initial digest is
`1688c27e7e79e8b8302d494a83717f8609e881823cb5460e378d056efa25eba1`.
Disposition: **OP-CACHE-001 fixed with exact-text comparison evidence**.

The guide requires complete-source restoration and pinned-environment recovery
before optional installation, identifies the exact source commit, requires a
separate clean idle checkout with absent/empty project outputs, prohibits
shared writable outputs/hardlinks, and correctly treats the idle flag as an
assertion rather than process detection.

Source023 and cache001 byte sizes, archive SHA256 values and Library IDs agree
across the guide, source binding, creation records, successful upload receipts,
upload-verification record and cache ledger. The recorded capture has raw
exit 0, 504 retained families, 449 omissions and 249,142,110 payload bytes.
Capture log/creation record report a passed private extraction check; upload
and post-upload verification agree on the same archive and source binding.

The reviewer confirmed that the guide preserves all required limitations:
complete source recovery does not depend on this cache; counts are neither
validation percentages nor an ETA or chapter credit; raw trace agreement does
not establish fresh compilation from the candidate; changed-root reuse is
uncertain; no success record is restored; and the complete guarded check,
managed ProofAudit prerequisite, regressions, both review axes and immediate
final candidate verification remain required. Cache001 stays bound to
source023 and must not be rebound to a later checkpoint.

Checkpoint024 is explicitly future/intended preservation. The guide expressly
withholds any uploaded claim until its actual receipt exists. It was not
used as completed evidence in this review.

The reviewer checked and retained the exact evidence identities listed in the
input table: frozen input inventory; source binding; identical launch/attempt
records; cache creation, upload, post-upload verification and capture log;
source023 creation/upload; and the original approved review. The preserved
approved review is byte-identical to the review referenced by acceptance, so
this append does not erase original approval evidence.

Limits: this assessment reuses recorded capture/extraction/upload outcomes.
No archive rehash/extraction, mutable-cache inspection, Library contact,
remote-availability test, behavioral test or helper/compiler rerun occurred.
It does not independently establish upload timeliness or artifact provenance
beyond those records. This is a guidance/evidence follow-up, not a new source
review or revalidation. The reviewer made no file changes; all its writers
are idle and no commands or writes remain in flight.

### Operational Spec

Outcome: **Passed**. OP-CACHE-001 is fixed and verified; **zero new or
unresolved operational Spec findings**. Original independent reviewer:
`/root/cache_review/spec`.

This assessment reuses accepted utility candidate a43cef4/tree27b06c3 and
does not reopen the unchanged eight-file implementation review.

The reviewer independently compared the preserved initial and corrected
guides. The only differences are the exchange and renumbering of steps 3/4.
Step 3 now reconstructs the binding for source023-alone recovery before step
4 consumes it. The initial/corrected guide digests are exactly the identities
listed above. All five required binding fields are recoverable from the stated
source023 identity: filename, SHA256, byte size, Library file ID and source
commit. The guide distinguishes source023, which predates capture, from newer
tracker checkpoints containing its later saved binding and receipts.
Disposition: **OP-CACHE-001 fixed and verified**.

Source023/cache001 sizes, archive hashes and Library IDs agree across guide,
binding JSON, creation records, upload receipts, post-upload verification and
ledger. Cache001 remains bound to source023 and source commit 3279bac. The guide
prohibits rebinding it to checkpoint024 and preserves newer complete
checkpoints' tracker records as authoritative task history. Creation result,
log, ledger and ticket agree on 504 retained families, 449 omissions,
249,142,110 payload bytes, raw exit 0 and passed private extraction. These
counts are not presented as build percentages or chapter credit.

The independently assessed recorded sequence is:

| Event | Recorded UTC |
| --- | --- |
| Utility/amendment acceptance | 2026-11-02 14:07:04.864935 |
| Source023 creation; bundle/restore/stability passed | 2026-11-02 14:24:43.025610 |
| Cache001 capture starts with source023 binding and approved utility | 2026-11-02 14:45:26.973733 |
| Capture completes, raw exit 0 | 2026-11-02 14:45:56.313011 |
| Cache001 creation result recorded | 2026-11-02 14:45:56.313744 |
| Post-upload identity verification recorded | 2026-11-02 14:46:57.891811 |

The successful source023 upload receipt matches the binding supplied to
capture. Cache001's successful receipt and post-upload verification agree on
full digest, size and local Library binding. Checkpoint024 remains prospective:
its intended role is stated, but no upload is claimed before its receipt exists.

Recovery boundaries remain correct: source023 is complete without cache;
installation requires compatible exact source/environment identity, a separate
idle checkout and absent/empty project outputs; the idle flag asserts rather
than detects idleness; absolute trace captions remain, with no cross-root reuse
guarantee; consistent older outputs may be retained without a fresh-source
provenance claim; no success record or chapter credit follows; all guarded
build, managed ProofAudit, regression, independent-review and immediate final
verification requirements persist.

The Spec reviewer verified the original approved review's independent
22,206-byte preserved copy and acceptance-matching SHA256 f547a6c27fed94ee9275ca93f039371bc01cf4e99a0331053b3a8ff013ab29ef.
It also confirmed the records read match the complete input manifest, including
all capture/source receipt records, acceptance and final-content records,
companion ledger, and the exact observed ticket/STATUS hashes in the table.

Limits: this is read-only assessment of frozen guidance and recorded evidence.
It does not independently re-observe UI exposure or upload initiation times;
the upload receipts themselves contain no such timestamps. It establishes
agreement of saved records, not a new claim about remote bytes, future
availability, source provenance or formal acceptance. No tests, helper/compiler,
archive rehash/extraction, mutable-cache read, process/storage survey or remote
operation occurred. The reviewer wrote no files; no writes remain in flight.

### Operational coordinator disposition

Both original independent axes have **Passed** this bounded operational
follow-up on the exact corrected guide
`be39ebe8d6217d375936ff13d5f73ee5112b6ee824dc3a8316022076f55460ae`
and the pinned evidence inventory. OP-CACHE-001 is fixed and independently
verified; no new or unresolved operational findings remain. The coordinator
rechecked every pinned input digest/size at completion and preserved the exact
original approved-review bytes as both a separate file and this record's prefix.

The accepted eight-file utility has zero source deltas to a43cef4. Its original
implementation approval and acceptance remain unchanged. No duplicate source
review, new implementation loop, test/helper/compiler run, cache inspection or
formal acceptance gate was introduced. These outcomes assess the concrete
guide and the agreement/sequence of recorded evidence, with the explicit
observation limitations in both reports.

The follow-up is complete. All review writers are idle; root may now checkpoint
the corrected guide, both reports, source binding, actual cache receipt and
updated local tracking. That next checkpoint must be exposed/uploaded when
created. Nothing here claims checkpoint024 already exists or grants chapter
acceptance; all original formal work remains governed by its actual gates.

