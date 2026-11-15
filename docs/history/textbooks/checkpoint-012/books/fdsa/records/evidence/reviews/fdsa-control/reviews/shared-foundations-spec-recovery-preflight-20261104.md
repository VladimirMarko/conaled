# Shared foundations — Spec recovery preflight

Recorded 4 November 2026. This is a continuation of the independent Spec axis
for the unchanged combined X002 / APP-A / XB01 / APP-C candidate. The reviewer
authored no foundation code. Its separate, uncommitted Chapter 2 bottom-up
implementation remains outside this candidate and under an edit/build hold.

**Overall outcome: Blocked pending actual full terminal validation evidence.**
The retained complete source assessment has zero concrete Spec findings. This
recovery preflight identifies no new source/spec discrepancy or conflicting
recovery evidence. It is not a Passed review, a new source acceptance, or
permission to integrate.

## 1. Unchanged scope and retained review

| Item | Independently checked identity |
| --- | --- |
| Accepted Chapter 1 base and merge base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Foundation candidate and recovered checkout HEAD | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |
| Original foundation prefix | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Branch | `work/fdsa-foundation-integration` |
| Recovered checkout | `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch01-review` |
| Review comparison | `git diff 07e480f6ec9958d4975bb90151005b84f2907614...f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |

The accepted base and exact original prefix are ancestors of the candidate.
The later potential-accounting candidate `c28ba71863d2a35ee1c3a089caa90464e4cca692`
is not an ancestor. The nine-path diff remains 1,515 insertions and six
deletions, with the same nine-commit inventory recorded in the original review.
All nine current task files match their candidate Git objects byte for byte;
their SHA-256 values also match the original Spec report's complete identity
table. Git status, including nonignored untracked files, is empty.

The full original `reviews/shared-foundations-spec.md` and
`reviews/shared-foundations-round1.md` were read. The original Spec report
remains 32,927 bytes / 510 lines, SHA-256
`06880532472d17d6f9d254165b61d41a437d0a79857323deac231025fd38f599`.
The round record is 13,909 bytes / 216 lines, SHA-256
`21b930204907024a78e3c0adcca8ee0eb6a064e03c2587872b9379d8585b138d`.
Neither historical file was edited.

All four complete frozen requirements were read and independently rehashed:

| Requirement under `reviews/` | SHA-256 |
| --- | --- |
| `insertion-requirements.md` | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `list-library-requirements.md` | `83cffa5aff717943d449f4380189a9e9a761252730f5a14f4e392f1e62d154d4` |
| `list-calls-requirements.md` | `0a2f7a2869c10276da2cc9a852e20936c6aba2d094d5232b96e94fbf47ecf78d` |
| `notation-requirements.md` | `21a4ad13752d4316817e97f655af9a768726aa682124a39a2aeac248460b5a48` |

Their mathematical scope is unchanged. Historical status prose in these frozen
records does not reopen accepted Chapter 1 or remove requirements. The pinned
book was rehashed at its recovered location, confirming
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.

Under the existing review-reuse rule, the complete source assessment is retained:
the insertion execution/count model and occurrence-sensitive contract clients;
all twenty Appendix A list entries; all seven Appendix B.1 primitives and
their exact observations; and all ninety Appendix C rows, including interval,
integer-division, multiset-multiplicity and finite-index-fold boundaries. This
addendum does not replace that assessment with a smaller review or repeat its
source investigation as a new workflow.

The governing `REQUEST.md`, repository `AGENTS.md`, code-review instructions,
review-loop procedure, statement-review guidance and README acceptance rules
remain applicable. The Nix exception does not waive exact pins, proof
restrictions, exhaustive audit, independent axes or immediate verification.

## 2. Recovered qualification and runtime identity

The following complete records were assessed:

- `provenance/recovery-20261104-restored/runtime-content-comparison.json`.
- `provenance/unified-native-recovery-20261104-qualified/qualification.json`,
  `profile-config.json` and `smoke-result.json`.
- The actual attempt4 setup terminal result and complete closed log under
  `provenance/unified-native-recovery-20261104-attempt4-serial/`.
- The accepted native profile configuration under
  `provenance/unified-native-20261103/config.json`.
- The two recorded curl-download concurrency adjustments, the current
  `ENVIRONMENT.md`, the unchanged kit README and the retained Chapter 1
  acceptance record.

Read-only checks at 2026-11-04 04:07:39 UTC independently established:

- All **298** kit manifest entries match their delivered SHA-256 values.
- The actual generated profile configuration equals its saved qualification
  copy. Its official `lean`, `lake`, `leanc` and `leanir` binaries, profile
  payload copies, and four wrappers match the current and accepted historical
  content hashes.
- The actual runtime script, adapter source, compiled adapter and host loader
  match both profile records. Their respective hashes are
  `e790d472353e8d9467d696d2b1f7ae245c731d61e90cbfbcc7a2a576ad4fd695`,
  `fefc39d8645e4a938d6cc27574257d1a1e8e8f0790b75cc15bcf074272066fe0`,
  `124bc3f19426ab6558b3ca134d0afb70435eaff82a659e6e62a05e8e373e337d`, and
  `6222a16be7f2d458d6870efe6e715fc0c8d45766fb79cf7dcc3125538d703e28`.
- Both recorded host modes are `compat`. The disclosed per-program loader
  adapter is retained; recovery did not silently substitute a different
  compiler or execution profile.
- All nine dependency checkouts are real private directories, clean, and at
  the exact revisions in the unchanged `lake-manifest.json`.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` and `check.sh` remain
  byte-identical to the accepted Chapter 1 base versions.

The recovered setup attempt4 exited **0** at 03:53:20.340644 UTC, with the
candidate unchanged and clean. Its closed 6,173-byte log hashes to
`00d21c992d76227360f40022f705938a91b89639a7285d3e7d8762a5da9dcc77`.
The preceding three setup attempts remain recorded as actual failures; the
retry changed only supported curl transfer concurrency after HTTP429 responses.
It did not change cache endpoints, source/dependency pins, compiler inputs or
proof policy.

The smoke evidence covers the exact Lean/Lake versions, direct and Lake-child
prefixes, successful valid proofs, rejection of the false theorem `2 + 2 = 5`,
native build/link/run and the Mathlib import. The false-proof case's exit **1**
is the expected rejection, correctly distinguished from setup failure. The
Mathlib fixture's advisory unused-variable warning is visible in its closed
log; no warning policy was suppressed. These are environment qualification
facts, not foundation acceptance or a substitute for the project audit.

The preserved Chapter 1 acceptance and successful full native fresh baseline
remain valid historical evidence. The candidate changes only source and its
integration documentation. Runtime content, pins and the checker match that
baseline; loss and recovery of regenerable output directories do not identify
a new README fresh-check trigger. The applicable route remains the ordinary
guarded full candidate check. No extra fixture or duplicate fresh baseline is
requested by this preflight. The new check still has to establish its own
complete result, post-build integrity and exhaustive audit.

## 3. Actual validation status

The historical `provenance/chapter02-foundation-full-attempt1/` has no secured
terminal outcome. Its old start/progress records do not establish success or
failure, and no historical execution ID was polled. The original complete
source report's description of that run being active was a historical
observation, not a claim that a process survived recovery.

The newly named root-owned attempt is
`provenance/chapter02-foundation-full-attempt2-recovered-20261104/`. Its request
and start records specify the unchanged native kit command:

```
conaled_native.py --state <recovered-state> run --project <candidate-checkout> \
  --threads 1 -- ./check.sh --candidate HEAD
```

The full paths are preserved in its `request.json` and `start.json`. The start
time is 03:59:45.995203 UTC, initial HEAD is the exact foundation candidate,
initial status is empty, and available space at launch is 27,930,460,160 bytes.
The initial log identifies Lean 4.35.0 and successful source-policy startup
checks. Missing-output trace invalidations are expected for the recovered cold
project tree; they are not a completed build or audit.

At this preflight's evidence observation, **no terminal `result.json`, closed
verification copy, or worktree `.lake/verification.json` was present** for this
run. Its progress record explicitly warns that historical progress does not
establish current liveness. No partial log, setup smoke, focused module result,
or absent visible error is treated as terminal success.

The prior exact-candidate six-module focused success remains retained with its
original limitations. The old Chapter 1 candidate verification cannot verify
this foundation. A new matching success record from the full ordinary check is
still required, and root must perform immediate `./check.sh --verify-candidate
HEAD` after both axes pass and immediately before exact local integration.

## 4. Findings carried forward and continuation

| Stable item | Current Spec disposition |
| --- | --- |
| `FDN-ELAB-001` | Source-adequate ListCalls corrections and exact-candidate focused confirmation retained; complete-candidate confirmation remains pending. |
| `FDN-ELAB-002` | Source-adequate standard API/domain and proof corrections, with exact-candidate focused confirmation retained; complete-candidate confirmation remains pending. |
| New concrete `FDN-SPEC-*` source findings | None identified. |
| New concrete recovery-evidence discrepancy | None identified in the assessed records and independent identity checks. |
| Required validation | Still Blocked pending the actual terminal full build/audit/matching-record evidence. |

When root supplies the actual terminal result, complete closed log, exhaustive
audit result and matching verification record, continue this same Spec axis
against the same immutable source and all four requirement scopes. Reconcile
actual diagnostics and the retained findings without erasing the earlier
failures or promoting focused success. Source changes require full-scope
continuation on a new immutable candidate. Independent Standards completion,
immediate candidate verification, local integration and an acceptance
checkpoint remain separate required steps.

**Base:** `07e480f6ec9958d4975bb90151005b84f2907614`.
**Candidate:** `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.
**Concrete Spec findings:** 0; worst source issue: none identified.
**Overall Spec outcome:** **Blocked**.

Only this new control-directory addendum was written. No historical review,
candidate source, Git ref, dependency, compiler process or cache was modified;
the reviewer launched no build and no additional review workflow.
