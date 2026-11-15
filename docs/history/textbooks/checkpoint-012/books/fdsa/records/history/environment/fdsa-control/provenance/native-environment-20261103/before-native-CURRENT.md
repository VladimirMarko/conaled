# Native execution investigation — latest steering, 2026-11-03

The user requested alternatives because QEMU emulation is too slow. The exact
cache utility build r2 completed successfully (exit0) on candidate07e480f;
no dependency-cache retrieval or full project gate had begun at this pivot.
Native startup using a small application-path compatibility library now
passes version/hash/prefix checks with unchanged official executables. This
is a prototype under investigation, not approved project validation. Actual
proof tests and independent review are pending. Preserve all prior evidence.
The current task remains the complete FDSA formalization. The earlier handoff
below is historical where it prescribes QEMU or a running r2 cache build.
See provenance/native-environment-20261103/ and REQUEST.md.

# Current continuation handoff

Updated 2026-11-03 after successful application of the user's QEMU setup guide.
The full goal remains all 27 FDSA chapters and Appendices A–C, chapter by chapter.
Use REQUEST.md for authority. Tickets and Git work remain local; no GitHub writes.

## Current result

**No chapter, appendix or shared unit is accepted. Chapter 1 is active.**
The environment startup blocker is resolved. All twelve setup checks passed,
including actual theorem compilation through both bare Lean and Lake's child
Lean, exact version/githash/prefix checks, and matching generated proof outputs.
The official Lean/Lake executable bytes and all project/dependency pins remain
unchanged. The user explicitly waived mandatory Nix use and supplied the working
QEMU route. Do not ask for that permission again.

The authoritative reproduction instructions are **ENVIRONMENT.md**, with complete
adapter source in tooling/pinned_toolchain.py. They include exact downloads,
digests, authentication evidence, layout/relocation, dependency sources and cache
commands. They need no other checkpoint or chat. The unrelated checkpoint039
mentioned in the original attachment is not part of this FDSA lineage.

The pinned cache utility is currently being built in the candidate checkout.
Its current foreground recorder is provenance/qemu-cache-build-20261103-r2/,
using the guide's default one Lean thread. The prior four-thread trial r1 was
stopped after a sustained 29/42 plateau; its interruption record preserves the
actual session exit130 without inventing a child terminal result. The current
actual terminal result belongs in result.json, not this narrative. No full project
check or Chapter 1 final review has started in this recovered workspace yet.
A detached launch intent in qemu-cache-build-20261103/ did not produce a worker
start/log/result; that historical evidence is retained without success credit.

## Source and review identities

- Integration branch work/fdsa-book: 1aabd512284fe86254278ac631eda061d311050b.
- Chapter 1 repaired candidate: 07e480f6ec9958d4975bb90151005b84f2907614,
  retained on work/fdsa-basics-cost-models.
- Full-scope original review base: 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd.
- Isolated checkout: ../conaled-ch01-review, detached and clean.
- The full fourteen-path scope, both frozen requirement records and all prior
  findings remain. SPEC-001/002/003/V001 are still unresolved pending matching
  full validation and final independent review. No readiness/source preflight
  is final approval.
- Initial Chapter 2 shared prefix remains
  c80eec92f5458eccfd1c34c8314d666c2a1e3847.

All named source refs and unfinished cross-cutting drafts remain preserved.
Historical repaired full attempts 1/2/3 have unknown terminal outcomes. The
original old-candidate ENOSPC failure remains distinct. Old process IDs and
running metadata are historical, not evidence of current liveness.

## Next execution sequence

1. Read the actual terminal cache-build result. On successful build, run the
   cache executable explicitly through QEMU inside Lake's environment, exactly
   as ENVIRONMENT.md describes. Preserve its actual exit and closed log.
2. Complete the bounded environment/recovery-tooling Standards and Spec review,
   then create, expose and save checkpoint0068 with the requested instructions
   and all supporting evidence. This review does not accept Chapter 1.
3. From the stable candidate, run one new recorded full guarded check,
   conventionally repaired attempt4:
   python3 ../fdsa-control/tooling/pinned_toolchain.py --
   env LEAN_NUM_THREADS=4 ./check.sh --candidate HEAD
   Use tooling/record_command.py in a retained execution session and a unique
   provenance directory. Keep all earlier evidence. The four-thread setting
   follows the user's tested recipe and can be adjusted for a concrete resource
   issue without changing proof requirements. No source or compiler writer may
   race the candidate's check.
4. Read the complete terminal result/log and matching verification record. All
   source/coverage/compiler checks, pre/post integrity guards, integrated
   compilation and exhaustive audit must pass. Missing or unexplained integrity
   evidence follows the unchanged incident runbook; never bypass it.
5. Resume the existing logical Chapter 1 review loop with a replacement
   coordinator and two independent final axes. Supply original fixed base,
   exact candidate, full fourteen-path scope, both frozen requirements, prior
   findings, matching validation and user environment exception. Both axes must
   pass the same immutable candidate.
6. Immediately run the unchanged --verify-candidate HEAD command through the
   adapter before acceptance/integration. Save and expose the acceptance
   checkpoint immediately; then activate Chapter 2 and continue the full book.

## Durable evidence

Checkpoint0067 is saved as libfile_e4e5f5a888608191a42f300e3ac95d68. Its
post-archive receipt/content inspection are retained and enter checkpoint0068.
The exact user guide/request, Ubuntu signature chain and package index, original
and adapted launcher sources, layout diff, all actual smoke results and unchanged
source/dependency checks are under provenance/qemu-environment-20261103/.
The earlier handoff is checkpoint0067-CURRENT.md in that directory.

The optional record_command helper preserves the owned command's actual exit
before secondary bookkeeping, a closed full.log, and any verification record.
Missing result.json means unknown terminal outcome; progress.json is only a
historical observation. Preserve the execution session for foreground recording.
No full build, proof audit, formal acceptance or later chapter completion is
inferred from environment/cache setup alone.

## Checkpoint0068 saved

conaled-fdsa-0068-qemu-environment-ready.tar.gz is saved as
libfile_9227c82658d88191ae6fc6235a02a424; SHA-256
ef5f503c63c636bce004c8f72369b526227591146d63346a1579f806a14fc2fc,
77,067,734 bytes. Its own post-archive receipt and content inspection enter
the next checkpoint. This preserves pending cache/review state without
formal acceptance. Continue the actual execution sequence above.
