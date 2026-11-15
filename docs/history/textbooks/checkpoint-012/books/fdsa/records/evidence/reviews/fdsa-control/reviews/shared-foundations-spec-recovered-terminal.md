# Shared foundations — Spec recovered terminal continuation

Recorded 4 November 2026. **Overall Spec outcome: Blocked.** The complete retained source assessment has zero concrete findings, and this continuation identifies no new source/spec or recovery-evidence discrepancy. The exact foundation full check is still live according to root; its terminal result is unavailable. No full-build, audit, verification or acceptance success is inferred.

## 1. Reviewer independence and scope

The continuing reviewer is `/root/chapter02_quicksort`. I authored Chapter 2 quicksort/value/resource, three-way, uniqueness and numerical development and prepared Chapter 2 reconciliation material. I did **not** author or edit the foundation scope or its two source correction commits. An explicitly authorized merge of this unchanged foundation into a Chapter 2 development branch did not alter the foundation candidate. My Chapter 2 work is outside this review and receives no approval here.

This is the existing independent **Spec** axis continued under the repository review-reuse procedure. The original complete Spec report, round record and recovery preflight remain intact. Their requirement coverage and source findings are retained after exact identity checks; the current work assesses recovered identity and validation readiness. The independent Standards continuation remains separate.

| Identity | Exact value |
| --- | --- |
| Accepted Chapter 1 base, current accepted ref and merge base | `07e480f6ec9958d4975bb90151005b84f2907614` (R) |
| Candidate, current HEAD | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` (F) |
| Exact original foundation prefix | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Candidate tree | `1c657c8923e258758aa1118a618c34732eaa9e45` |
| Branch | `work/fdsa-foundation-integration` |
| Checkout | `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch01-review` |
| Review comparison | `git diff R...F`, with the full SHAs above |
| Scope | X002 insertion costs; Appendix A; XB01 / Appendix B.1; Appendix C |

Read-only observation at 07:56:44 UTC found exact F, empty Git status including nonignored untracked files, the recorded nine-commit inventory, and all nine changed paths identical to their candidate Git objects and to the original Spec report's SHA-256 table. The scope remains 1,515 insertions and six deletions. R and the exact original prefix are ancestors of F. The later potential-accounting prefix `c28ba71863d2a35ee1c3a089caa90464e4cca692` is not an ancestor; no later shared draft is included.

The nine paths are the two resource modules `Applications/Resources/InsertionSort.lean` and `Applications/Resources/ListCalls.lean`; the four examples `InsertionCosts`, `ListLibrary`, `ListCalls` and `FunctionalNotation`; `SquareApplications.lean`; and the two research documents `fdsa-notation-map.md` and `fdsa-reconstruction-map.md`. No task path is excluded. Exact per-path bytes, hashes, Git blobs, commit list and configuration identities are saved in [identity.json](../provenance/foundation-spec-terminal-continuation-20261104/identity.json).

## 2. Complete retained source assessment and requirements

I read the complete retained 216-line round record, 510-line independent Spec report, 191-line Spec recovery preflight and all four frozen requirements. The records remain:

| Retained record | Bytes | SHA-256 |
| --- | ---: | --- |
| `shared-foundations-round1.md` | 13,909 | `21b930204907024a78e3c0adcca8ee0eb6a064e03c2587872b9379d8585b138d` |
| `shared-foundations-spec.md` | 32,927 | `06880532472d17d6f9d254165b61d41a437d0a79857323deac231025fd38f599` |
| `shared-foundations-spec-recovery-preflight-20261104.md` | 11,133 | `9fedd69337033c636e638df20136575a73d5f0af42121dc80bb7c5edcbf33805` |
| `insertion-requirements.md` | 3,257 | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `list-library-requirements.md` | 3,123 | `83cffa5aff717943d449f4380189a9e9a761252730f5a14f4e392f1e62d154d4` |
| `list-calls-requirements.md` | 4,040 | `0a2f7a2869c10276da2cc9a852e20936c6aba2d094d5232b96e94fbf47ecf78d` |
| `notation-requirements.md` | 3,406 | `21a4ad13752d4316817e97f655af9a768726aa682124a39a2aeac248460b5a48` |

The recovered primary PDF again matches 1,742,029 bytes and SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. The original Spec report retains the complete relevant source-page inspection, supporting primary-source provenance, API examination, cases, assumptions, statement review and correction assessment. Identity-preserving recovery permits reuse of that completed work. Historical status prose in frozen requirements does not reopen accepted Chapter 1.

The full retained mathematical assessment covers the following boundaries.

| Unit | Requirements and retained semantic assessment |
| --- | --- |
| X002 | Actual measured insertion and right-fold insertion-sort execution, returned-value correspondence, tie direction and actual sorted tail. Insertion bounds are 1 through n+1; sort lower bound is 2n+1, with exact doubled/triangular and weaker square upper bounds. Best-case assumptions remain input-local, and the strict reversed-range attained family does not assert duplicate-containing inputs are a worst family. Arbitrary payloads use existing key-based contracts. Nil/singleton/duplicate/head-tie/full-traversal clients and sorted-result/repeated-value/small-rank clients are retained; the rank budget covers sorting, not a newly invented selector execution. |
| Appendix A | All twenty list-library entries use canonical operations and their exact domains. Option/proof-based partial interfaces preserve empty and out-of-range cases without payload defaults; total operations retain their boundaries. Arbitrary-relation sortedness is all-later Pairwise, with the nontransitive adjacent-chain boundary retained. Folds, minimum, ranges, updates, filtering, mapping and concatenation keep multiplicity and order. Value correspondence does not itself claim costs. |
| XB01 / Appendix B.1 | All seven primitives retain source call-count recurrences and exact returned values. Measured map/filter charge actual callback results and each occurrence; both filter branches recurse. Constant callback tariffs require only the relevant input-local premise. Append/length use n+1. Separate take/drop each run the actual split observation, giving twice the fused cost. Lookup is sequential with the printed valid-index law and an explicitly identified totalized out-of-range extension. Duplicate callbacks, rejected values, zero/unit costs, composition, empty payloads and separate-versus-fused examples remain substantive. |
| Appendix C | All ninety rows retain their exact typed standard correspondences: 34 symbols, four decorations and 52 syntactic forms. Prop/Bool assumptions are introduced only where used. Multiset multiplicity is distinct from support; list comprehensions retain duplicates/order. Integer floor division retains negative-divisor and zero boundaries. Finite-index-set folds use neutral values outside the finite-index domain and are not silently replaced by support-finite sums. All six intervals use the standard Preorder domain; the printed upper-interval correction and separating examples are retained. |

The complete original source assessment supplies the detailed per-claim evidence behind this table. Four public example imports expose both resource modules as recorded. The current task does not replace full scope with this summary or a fresh sample review.

Applicable guidance was read from the exact candidate: AGENTS, code-review and its heuristics, review-loop, example-driven statement review, implement, architecture/domain/glossary, module and exhaustive-audit ADRs, and README development/acceptance/proof-boundary sections. REQUEST, CURRENT, STATUS and the ticket index were read. The initially truncated CURRENT/STATUS read was fully resolved with bounded rereads. [evidence.json](../provenance/foundation-spec-terminal-continuation-20261104/evidence.json) records exact identities and read scope.

## 3. Recovered environment and applicable validation route

The complete qualified-setup receipt, profile configuration, smoke receipt, setup attempt4 result and its full closed log, recovered runtime comparison, restore identities, accepted Chapter 1 receipt, accepted fresh verification record, current ENVIRONMENT and full kit README/pins were assessed.

The successful restore receipt records 50 references, five worktrees and successful Git fsck. It explicitly records unrelated post-restore temporary asset files in other worktrees; foundation F was clean. The setup history retains the three actual HTTP429 failures. Attempt4 exited 0 at 03:53:20.340644 UTC; its complete 6,173-byte log has SHA-256 `00d21c992d76227360f40022f705938a91b89639a7285d3e7d8762a5da9dcc77`. The transfer-concurrency retry did not change mathematical or compiler inputs.

The environment is kit 1.0.0 with official Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and matching Lake `5.0.0-src+eb6cafb`. The official archive identity remains 594,481,375 bytes and SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`. The retained qualification/preflight verified all 298 kit manifest entries; this continuation does not claim another installation or full manifest run.

At 07:56:59 UTC, additional read-only checks confirmed all nine dependency HEADs and clean statuses against kit pins, with real directories under the foundation checkout. The actual four official binaries, four profile wrappers, runtime script, adapter source, compiled adapter and host loader match qualified hashes. The recovered runtime comparison establishes those content identities against the accepted native baseline. Exact results are in [runtime.json](../provenance/foundation-spec-terminal-continuation-20261104/runtime.json). No runtime, dependency, cache or output was changed.

The disclosed narrow per-program launcher adapter and compat mode are retained. The setup log contains successful exact version/prefix, valid-proof, Lake-child, native build/run and Mathlib import observations. Its false-proof exit 1 is the expected rejection of 2+2=5. An advisory fixture warning remains visible. These receipts qualify the environment and do not establish foundation acceptance.

Candidate toolchain and manifest bytes match kit pins. Toolchain, manifest, Lake configuration, check.sh and README are unchanged from accepted R; the complete nine-path diff contains no build-tooling change. User authorization waives Nix alone. The preserved full native fresh Chapter 1 result remains accepted. Recovery and missing regenerable outputs do not, by themselves, trigger another fresh baseline. No concrete additional fresh/fixture trigger was identified; the ordinary guarded full check is the applicable route. Any actual integrity failure found in terminal evidence must still be addressed under the existing rules.

## 4. Actual validation status and preserved findings

| Evidence | Spec assessment at preparation |
| --- | --- |
| Complete original source review and current identity correspondence | Retained, zero concrete Spec findings. |
| Exact F six-module focused attempt3 | Actual exit 0 retained, with its focused scope only. |
| Qualified recovered native setup/smokes | Actual successful environment qualification retained. |
| Historical full attempt1 | Terminal outcome unknown; no session polling or success/failure inference. |
| Newly recorded full attempt2 | Root reports it remains live. No terminal result is available. |
| F exhaustive audit / matching verification | Not established. |
| Immediate candidate verification / local acceptance | Pending subsequent required gates; none performed here. |

The root-owned attempt is `provenance/chapter02-foundation-full-attempt2-recovered-20261104/`. Its request and start records name the exact kit/state/project, one Lean thread and `./check.sh --candidate HEAD`. The start is 03:59:45.995203 UTC, exact F, empty status; launch-time available space was 27,930,460,160 bytes. Progress records carry their explicit warning that a saved progress observation does not establish present liveness. Liveness here comes from root's current report.

At 07:57:23 UTC the attempt directory had request/start/progress/full-log files but no `result.json` or secured `verification.json`; the worktree had no `.lake/verification.json`. The ongoing log is not closed evidence. The accepted Chapter 1 verification refers to R and cannot verify F. No declaration, theorem or module count from Chapter 1 is presented as the foundation result.

| Carried item | Disposition retained for this continuation |
| --- | --- |
| FDN-ELAB-001 | ListCalls source corrections are adequate and focused-confirmed on F; complete-candidate confirmation remains pending. |
| FDN-ELAB-002 | Standard API/domain/proof corrections are adequate and focused-confirmed on F; complete-candidate confirmation remains pending. |
| New concrete Spec source findings | None. |
| New recovery-evidence discrepancy | None identified in the assessed records and current read-only identities. |
| Required validation blocker | Actual full terminal build/audit/matching-record evidence is still unavailable. |

Prior failures and advisory import warnings remain preserved. No linter or mathematical requirement is suppressed, no prior finding is erased, and no aggregate failure is promoted from successful component targets.

## 5. Terminal evidence to assess when root supplies it

1. **Actual outer terminal receipt.** Read the attempt's final result, actual exit, complete command, start/end/elapsed, before/after F and clean status. Check the closed log byte count/hash and any interruption, timeout or recorder error.
2. **Complete closed full log.** Read all output in bounded chunks. Confirm actual source-policy, public-import coverage, guarded full build, candidate/dependency integrity and exhaustive audit outcomes. Resolve any real diagnostic against the whole four-unit scope.
3. **Secured native command records.** Read the native start, complete output and actual result. Reconcile the project, exact command, one-thread profile, child exit and termination with the outer receipt. An unexplained recorder/child disagreement remains a blocker.
4. **Actual exhaustive audit evidence.** Confirm all required project-root kernel-safe declarations, including private/generated declarations, their real counts and the permitted axiom union only: propext, Classical.choice and Quot.sound. Use the current full audit output and any emitted artifact; do not substitute historical counts or samples.
5. **Matching new verification record.** Read the worktree record and secured copy for F, successful result, exact compiler/dependencies, ordinary mode and completion identity. It must be produced by this applicable full check.
6. **Post-completion source/runtime integrity.** Reconcile immutable F, clean status, the nine source identities, pins and qualified runtime with the check's own guards. If required inputs changed, continue full-scope review on the new immutable candidate with applicable validation.
7. **Carried and new findings.** Establish the complete-candidate disposition of FDN-ELAB-001/002, preserving prior failures and source assessments. Assess new diagnostics without weakening definitions, hypotheses, examples or coverage.
8. **Subsequent acceptance sequence.** Root obtains both complete independent axes on the same candidate, then runs the qualified immediate `./check.sh --verify-candidate HEAD` directly before local fast-forward and the acceptance checkpoint. This continuation does not perform or pre-approve those steps.

The machine-readable checklist is in [assessment.json](../provenance/foundation-spec-terminal-continuation-20261104/assessment.json). It expresses existing gates; it does not add a duplicate fresh check or another review hierarchy.

## 6. Outcome and write hold

**Base:** `07e480f6ec9958d4975bb90151005b84f2907614`.  
**Candidate:** `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.  
**Concrete Spec findings:** 0; worst source issue: none identified.  
**Overall Spec outcome:** **Blocked pending actual full terminal evidence**.

Only this new review and its new supporting provenance directory were written. Candidate source, refs, existing reviews, controls, tickets, build outputs and caches remain untouched. No build, compiler, setup, doctor, fixture or new review worker was started. Chapter 2 numerical and documentation work remains frozen. After saving and reading back this preparation, all further writes are held for checkpoint0092 and root-supplied terminal follow-up.
