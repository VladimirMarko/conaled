# Shared foundations — independent Standards recovery preflight

Recorded: 2026-11-04T04:05:01Z  
Reviewer: independent Standards continuation agent `/root/foundation_continuation`  
Preflight assessment: complete, with no concrete recovery or fresh-trigger findings  
Overall Standards outcome: **Blocked pending full candidate validation**

This is a continuation of the existing shared-foundations review. It preserves
the completed source assessment in
[shared-foundations-standards.md](shared-foundations-standards.md) and the stable
finding record in [shared-foundations-round1.md](shared-foundations-round1.md).
It does not supersede either historical record, claim a completed foundation
check, or authorize acceptance. The separate Spec axis remains required.

## Immutable scope and preserved source assessment

| Identity | Exact value |
| --- | --- |
| Accepted Chapter 1 / review base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Foundation candidate | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |
| Exact original foundation prefix | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Candidate branch | `work/fdsa-foundation-integration` |
| Candidate checkout | `conaled-ch01-review` |
| Full review diff | `git diff 07e480f6ec9958d4975bb90151005b84f2907614...f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |

The full existing review scope remains X002 insertion costs, Appendix A's twenty
list-library mappings, XB01 / Appendix B.1's seven primitives and seven exact
call-count laws, and Appendix C's ninety correspondence rows. The recorded
compiler/API corrections remain in scope. There are no new exclusions. The
later potential-accounting prefix and unrelated shared drafts are not part of
this candidate. Acceptance of these units would not close Chapter 2 or the
remaining Appendix B work.

The prior review covers the full nine-path diff, including all six new Lean
modules, their public integration, and correspondence documentation. Its source
assessment is complete with zero concrete findings. The candidate, requirements,
and applicable source standards are unchanged. This continuation assesses the
recovered validation environment and evidence under the repository's existing
review-reuse procedure; it does not repeat or narrow the source assessment.

The frozen requirements remain:

| Requirement record | SHA-256 |
| --- | --- |
| `insertion-requirements.md` | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `list-library-requirements.md` | `83cffa5aff717943d449f4380189a9e9a761252730f5a14f4e392f1e62d154d4` |
| `list-calls-requirements.md` | `0a2f7a2869c10276da2cc9a852e20936c6aba2d094d5232b96e94fbf47ecf78d` |
| `notation-requirements.md` | `21a4ad13752d4316817e97f655af9a768726aa682124a39a2aeac248460b5a48` |

The historical complete Standards report remains 24,375 bytes, SHA-256
`3f56c01fe4a53f50a2051108a95fa41584d7037a41af3afbd2346f9b25f5c497`.
The historical complete Spec report remains 32,927 bytes, SHA-256
`06880532472d17d6f9d254165b61d41a437d0a79857323deac231025fd38f599`.
Both were rehashed when saving this preflight. Neither report was edited.

## Evidence assessed

All paths in this section are relative to `fdsa-control/`.

| Evidence | SHA-256 at preflight persistence |
| --- | --- |
| `provenance/unified-native-recovery-20261104-qualified/qualification.json` | `37a60985201cda9ac852adbc972483c32e59ee6ee82119b866dbaa4625301629` |
| `provenance/unified-native-recovery-20261104-qualified/smoke-result.json` | `2ffe684a0d37f8ecc70978623a74a4305ffe4957cc8e6703f072b3ab9e416829` |
| `provenance/unified-native-recovery-20261104-qualified/profile-config.json` | `7ba088fe04b1d9087f1a2c61b2c9cb1a902f7dde0601134cac966960776856d3` |
| `provenance/recovery-20261104-restored/runtime-content-comparison.json` | `9242b4dcbe578dd52c52846cd2ce3432be46fee8702c08bede7fe6956fbc5555` |

I also assessed the preserved setup-attempt terminal records and closed-log
hashes, both recorded curl-concurrency adjustments, the newly launched full
check's request/start/launch records, and the candidate's actual `AGENTS.md`,
`README.md`, `docs/agents/review-loop.md`, and
`.agents/skills/code-review/SKILL.md`. The user's Nix waiver applies; the exact
runtime, proof policy, immutable-candidate checks, independent reviews, and
immediate verification requirements remain in force.

## Recovered runtime and dependency identity

The qualified setup uses kit 1.0.0 and official Lean/Lake 4.35.0. The preserved
native baseline identifies the compiler as:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

`runtime-content-comparison.json` compares content identities with the accepted
Chapter 1 native fresh baseline, excluding path and timestamp metadata. Every
listed compiler-tool, wrapper, launcher runtime, adapter source/binary, and
loader comparison matches. I independently hashed the actual restored four
compiler tools, four wrappers, `runtime.py`, `app_path.c`, `app_path.so`, and
loader: all twelve actual file hashes match the qualified profile.

The disclosed compatibility launcher remains in use. Its key identities are:

| Runtime component | SHA-256 |
| --- | --- |
| `runtime.py` | `e790d472353e8d9467d696d2b1f7ae245c731d61e90cbfbcc7a2a576ad4fd695` |
| Adapter source `app_path.c` | `fefc39d8645e4a938d6cc27574257d1a1e8e8f0790b75cc15bcf074272066fe0` |
| Adapter binary `app_path.so` | `124bc3f19426ab6558b3ca134d0afb70435eaff82a659e6e62a05e8e373e337d` |
| Native loader | `6222a16be7f2d458d6870efe6e715fc0c8d45766fb79cf7dcc3125538d703e28` |

Qualification records all nine dependencies clean, at their exact pins, in
private real directories:

| Dependency | Git revision |
| --- | --- |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
| Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

All ten environment smoke cases met their expected outcomes: compiler/Lake
versions, bare and child prefix discovery, valid proof, rejection of a false
proof, child proof, native build/run, and Mathlib import. The false-proof case
exited 1 as expected: its `passed: false` is paired with
`expected_failure: true` and `expected_outcome_met: true`. The suite's overall
result is passed. These are environment checks, not foundation acceptance.

## Hydration failures and successful recovery

The first three setup attempts remain accurately recorded as failed with exit
1. I compared each closed log's actual SHA-256 against the qualification record;
all match. The fourth setup attempt, `unified-native-recovery-20261104-attempt4-serial`,
exited 0 and records final HEAD `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`
with clean status. Its closed log is 6,173 bytes, SHA-256
`00d21c992d76227360f40022f705938a91b89639a7285d3e7d8762a5da9dcc77`.

The two adjustments in
`provenance/recovery-20261104-restored/cache-download-adjustment.json` and
`cache-download-adjustment-attempt3.json` reduced standard curl transfer
concurrency after HTTP 429 responses. They changed download scheduling only:
the kit, official compiler/kernel, runtime adapter, cache client/scope/endpoints,
dependency source/revisions, and proof/check policy were retained. Retrying
the remaining official cache downloads does not constitute a changed formal
validation profile or a reason to weaken the acceptance gates.

## Applicability of ordinary versus fresh validation

The actual candidate README requires `./check.sh --fresh` after changing build
tooling, toolchain, or dependency configuration, or when stale outputs are
suspected. It distinguishes normal cold-build invalidations from unexpected
integrity incidents. Ordinary acceptance still checks source policy, public
coverage, all integrated modules, output integrity, immutable inputs, and an
exhaustive axiom audit on every invocation.

The successful accepted Chapter 1 native fresh baseline remains preserved in
`provenance/chapter01-unified-fresh-attempt4/`, with acceptance in
`provenance/chapter01-acceptance-20261103/acceptance.json`. Its whole-project
audit covered 961 project modules, 45,074 kernel-safe declarations, and 24,929
theorems, with only `propext`, `Classical.choice`, and `Quot.sound`. These are
baseline whole-project counts, not new-book counts and not the pending
foundation audit result.

The recovery evidence establishes matching relevant runtime content and exact
dependency inputs. No applicable tooling/toolchain/dependency change or
suspected stale-output incident is established by this recovery. Mere loss of
regenerable outputs is not a README fresh trigger. Workspace loss also does not
invalidate the preserved accepted Chapter 1 baseline.

**Conclusion:** an ordinary immutable-candidate check is the applicable new
foundation gate. Another full fresh baseline is not required solely because
the workspace was restored. The normal guard's actual output and the closed
full validation log still require terminal review.

## Newly launched foundation gate: pending terminal assessment

The new evidence directory is
`provenance/chapter02-foundation-full-attempt2-recovered-20261104/`.
Its request/start records identify the qualified kit running:

```text
python3 fdsa-control/tooling/unified-native-kit-4.35.0/conaled_native.py \
  --state conaled-native-state run --project conaled-ch01-review \
  --threads 1 -- ./check.sh --candidate HEAD
```

This is a readable rendering of the recorded absolute-path command; the exact
argument vector is preserved in `request.json` and `start.json`. The start
record is dated `2026-11-04T03:59:45.995203+00:00`, resolves initial HEAD to
`f17cc6b1a2bf44215b16202ed0fcee2b5c130761`, records clean initial status, and
records 27,930,460,160 available filesystem bytes. It uses one Lean thread.

At this preflight inspection there was no `result.json`. This addendum makes no
terminal inference from the growing log or launch/progress metadata. Root owns
the live process. I have not polled or controlled any current or historical
execution session, started a build, or changed source, dependencies, or project
outputs. Root's separate Quicksort focused build was reported to use a distinct
qualified real dependency/project tree; it supplies no foundation acceptance
evidence.

The older `provenance/chapter02-foundation-full-attempt1/` remains an interrupted
attempt without a secured terminal result. Its partial log establishes neither
success nor failure and is not substituted for this new run.

## Findings and remaining acceptance evidence

There are **zero new concrete Standards findings** from this preflight.
The completed historical source assessment remains unchanged.

Stable IDs `FDN-ELAB-001` and `FDN-ELAB-002` are retained. Their already assessed
compiler/API corrections and focused confirmation are preserved; this
environment-only continuation does not declare their whole-candidate
validation complete. No finding was removed, renumbered, or silently resolved.

The terminal Standards continuation must assess:

1. The actual terminal result and complete closed full log, with matching
   recorded size and SHA-256.
2. Successful source-policy, public-entrypoint coverage, integrated build,
   output-integrity, and exhaustive axiom-audit results on this exact candidate.
3. The full warning inventory, including actual new-file warnings. The prior
   source assessment of nonfatal import advisories is retained; it does not
   pre-classify unseen terminal warnings as harmless or baseline.
4. A newly produced `.lake/verification.json` matching this foundation candidate,
   exact compiler/dependencies, actual ordinary mode, and successful completion.
   A Chapter 1 verification record cannot satisfy this requirement.
5. Final clean-candidate evidence and stable-input discipline for the complete
   run, including separation of writable project outputs.
6. The final dispositions of `FDN-ELAB-001` and `FDN-ELAB-002` using that
   whole-candidate evidence, preserving the existing source assessments.

After both independent axes pass on the same candidate, the coordinator must
run qualified `./check.sh --verify-candidate HEAD` immediately before accepting
the exact approved commit. Only then may the accepted local branch advance and
the relevant coverage/tickets be marked accepted, followed by an uploaded
acceptance checkpoint. No GitHub mutation or push is authorized.

**Final preflight disposition:** base
`07e480f6ec9958d4975bb90151005b84f2907614`; candidate
`f17cc6b1a2bf44215b16202ed0fcee2b5c130761`; zero concrete preflight findings;
**Standards Blocked pending full terminal candidate validation**.
