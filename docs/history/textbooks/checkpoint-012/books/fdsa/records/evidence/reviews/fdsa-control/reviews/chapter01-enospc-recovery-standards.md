# Chapter 1 disk-exhaustion recovery: retained Standards disposition

Recorded 2026-11-02 within the existing Chapter 1 implementation/review loop.
This preserves the completed applicability assessment of the retained independent
Standards reviewer `/root/chapter01_review/standards`. The review coordinator
`/root/chapter01_review` records it here with the subsequent root-supplied event
facts. This is not a new acceptance review, a successful recovery report, or an
approval of surviving build artifacts.

## Fixed identities and scope

- Original review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Failed old candidate: `1aabd512284fe86254278ac631eda061d311050b`.
- Committed repair candidate: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Failed-run checkout: `conaled-ch01-review`.
- Repair source checkout: `conaled-ch01-cost-models`.
- Failed command, under the pinned Nix environment:
  `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`.
- Root execution session: `80227`, retained as a historical execution identity.

The original requirements, frozen cost-model addendum, full 14-path repair scope
against the original base, and existing finding history remain unchanged. See
`chapter01-round1.md`, `chapter01-cost-models-candidate.md`, and the retained
Standards/Spec source preflights. The two earlier fresh attempts remain separately
recorded as superseded attempts; this event does not change their outcomes.

## Reported event and evidence boundary

Root observed session 80227 exit with status **120** at
**2026-11-02 15:44:10 UTC**. Its read-only inspection found a full 63 GiB overlay
filesystem, with inode usage at 27%. The 294,912-byte
`chapter01-incremental.log` contains explicit error-28/ENOSPC and failed
`.olean`-write diagnostics and ends truncated in the middle of a command.
The coordinator also read a bounded portion of those diagnostics, including
failure to create `Applications/Search/LeftistQueue.olean`.

Root subsequently identified **19 explicitly failed modules** in the truncated
log and **38 surviving source/artifact-family files, totalling 118,086 bytes**,
for preservation before any invalidation. These are the identified evidence
set, not a claim that the truncated log accounts for every possible failure or
that the files have already been archived. Root found **no
`.lake/verification.json`**. No build success, exhaustive-audit success, or
candidate acceptance is inferred.

Root reports that no task-local Lean, Lake or check processes remain. No
unrelated workspace was inspected for this disposition. Space is now available
after root verified all 38 older checkpoint archive SHAs against successful
durable receipts and removed only those duplicate local archives; latest
checkpoint 0039 was retained. This records root's completed space remedy, not a
separate verification of that cleanup by the Standards reviewer. Sufficient
headroom for the next build remains an operational prerequisite.

The observed failure establishes unsuccessful execution with interrupted or
partial output generation. It does **not** establish the condition of each
surviving output, prove unexplained stale-artifact reuse, or rule out additional
errors obscured by the truncated log.

## Standards applicability ruling

**After preserving the failed-run evidence and remedying disk exhaustion, the
next complete guarded incremental validation may directly target the repaired
immutable candidate `a14977b9e316cc484ffad8a470d26b15615956c0`. A complete
rerun of superseded candidate `1aabd512284fe86254278ac631eda061d311050b` is not
required.**

The candidate `README.md`, under "Build and audit", assigns missing or
inconsistent project-output evidence to pre-build guard invalidation and
rebuilding. `docs/agents/lake-integrity-incidents.md`, "Investigate and recover"
step 4, directs a guarded rerun after correcting the cause or stabilizing the
checkout. Explicit disk exhaustion therefore does not, by itself, make a fresh
rebuild mandatory. The next guarded run must assess the surviving normal Lake
outputs; this ruling does not declare those outputs sound in advance.

Neither the README nor the runbook requires acceptance of an abandoned
intermediate candidate before checking its replacement. The shared review
procedure requires matching evidence for the candidate ultimately accepted.
With the old writers stopped, ordinary Lake input tracking, rehashing and the
unchanged integrity guard may assess the remaining normal outputs against the
repaired source. No historical verification result or artifact identity may be
relabeled as validation of the repair.

The existing fresh-mode requirements remain intact. Suspected stale outputs
require fresh validation under the README and runbook step 5. Unexplained
recurrent invalidation or post-build rejection requires investigation and
coordinator notification under step 4, rather than repeated cleanup and retry.
Tooling, toolchain or dependency-configuration changes have their own applicable
fresh-validation requirements. Shared error wording alone does not establish
any such mechanism. Fresh success would not itself repair or establish recovery
of the incremental cache; a successful guarded incremental run is required for
that claim.

## Required recovery sequence and unchanged acceptance obligations

Before manual cleanup of affected outputs or automatic guard invalidation,
preserve the old command, exit status and truncated log, plus the surviving
affected traces, sidecars, artifacts and corresponding source/toolchain
identities. The runbook requires an honest account of anything unavailable;
missing evidence must not be reconstructed as though it survived. Root owns
that preservation and the subsequent recovery operation.

After sufficient space is available and output writers have stopped, establish
the clean repaired candidate in the stable isolated checkout with its pinned
dependencies, compiler and configuration. The existing focused-compilation
requirement and complete guarded candidate check remain applicable. No
source-policy, public-coverage, clean-identity, input-rehashing, pre-build
integrity, full-build, post-build integrity or exhaustive-audit gate is waived.

Preserve the actual new run's command, result, candidate identity and successful
verification record if one is produced. Both retained independent review axes
must assess the same final candidate and resolve their findings. Immediately
before acceptance, `./check.sh --verify-candidate HEAD` must confirm the
matching record. Any source correction requires its own immutable candidate
and matching evidence under the existing loop.

A later successful run validates its recorded candidate and mode. It does not
retroactively turn the old exit-120 attempt into a success or demonstrate that
the old candidate itself passed.

## Issue 272 applicability and local reporting

Root supplied a current read of public
<https://github.com/VladimirMarko/conaled/issues/272> through the GitHub REST
interface: **open**, updated **2026-10-30T19:45:18Z**, **0 comments**. Its full
body was retained in root's tool output and is to be saved with the event
evidence. This report relies on that supplied read and does not claim a second
independent remote fetch.

The issue distinguishes normal never-built missing outputs from unexpected
mismatches, recurring malformed evidence, post-guard failures and suspected
stale-artifact failures. Its known investigated occurrence concerns an inherited
`GraphEmission.olean` of 1,652,536 bytes, reported SHA prefix `1706bc30...`, an
unknown `GraphEmissionPure.ArtifactTyped` declaration, and mismatched trace or
sidecar evidence. It explicitly does not establish a second mechanism.

The present evidence is explicit ENOSPC/failed-write output. **No match with
the investigated GraphEmission occurrence has been demonstrated.** It is not
justified to classify this event as that recurrence or trigger its
matching-recurrence owner alert merely from failure wording. Preserve and
compare this occurrence's source/artifact identities and circumstances,
distinguishing output creation, reuse and propagation if further integrity
evidence arises. Root has already informed the user of the actual disk-full
failure; this is not represented as a matching-recurrence alert.

Under the user's explicit tracker override, maintain one **local** event record
and its evidence, rather than writing an issue comment or taking another remote
write action. The runbook does not impose a pause on the safe recovery described
above. Any later demonstrated recurrence or unresolved integrity evidence must
be handled through the existing coordinator and the issue's applicable
procedure, preserving the local-tracking override.

## Review status and actions taken

**SPEC-001, SPEC-002, SPEC-003 and SPEC-V001 remain unresolved.** Final Standards
remains Blocked; neither source preflight nor this recovery disposition supplies
compilation, audit or acceptance credit. The actual repaired-candidate checks
and final review have not been performed by this assessment.

The retained Standards work used policy reads and the supplied event evidence;
it ran no compiler, checker or project hash helper and made no source, cache,
configuration, Git/ref or remote mutation. After space became available, the
coordinator wrote only this requested outside-source report to preserve the
completed disposition. No other report or review outcome was modified.
