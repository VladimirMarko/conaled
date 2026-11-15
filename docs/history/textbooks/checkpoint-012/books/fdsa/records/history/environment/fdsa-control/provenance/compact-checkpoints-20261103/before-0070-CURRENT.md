# Current continuation handoff

Updated 2026-11-03 after the user's request to replace slow QEMU emulation.
The task remains the entire FDSA book: all 27 chapters and Appendices A–C,
chapter by chapter. REQUEST.md records authority. Tickets and Git work stay
local; no GitHub writes. The Nix exception is already authorized.

## Current result

**No chapter, appendix or shared unit is accepted. Chapter 1 is active.**
The preferred environment now executes the exact official Lean 4.35.0 and Lake
natively, using the included small own-executable-path compatibility library.
Official binaries, the proof kernel, project pins and all nine dependency source
revisions remain unchanged. This extra runtime component is disclosed, hashed,
and independently reviewed; do not describe the host environment as unmodified.

Ten final native setup checks passed, including real bare/Lake-child theorem
compilations with exactly matching proof artifacts. Readlink and executable-launch
boundary checks passed. The native dependency-cache command exited 0 after
retrieving/decompressing all 9,031 files in 70.790899 seconds. Its closed log and
result are in provenance/native-cache-get-20261103/. This is setup evidence,
not a project audit or chapter acceptance.

The self-contained instructions are ENVIRONMENT.md, with complete adapter and
compatibility source/binary in tooling/. Native environment snapshot 9f673480
passed independent Standards and Spec review against fixed base 900614e;
reviews/environment-native-snapshot.json gives full identities, scope and
validation pointers. No new Chapter 1 full gate or final review has begun yet.

The tested QEMU route remains a fallback, fully documented in
provenance/qemu-environment-20261103/ENVIRONMENT0068.md. Its r2 cache utility
build exited 0 in 161.54 seconds. The earlier r1 was interrupted; no successful
outcome is inferred for r1 or the detached no-start launch. The prior narrative
is preserved in provenance/native-environment-20261103/before-native-CURRENT.md.

## Source and review identities

- Integration branch work/fdsa-book: 1aabd512284fe86254278ac631eda061d311050b.
- Chapter 1 repaired candidate: 07e480f6ec9958d4975bb90151005b84f2907614,
  retained on work/fdsa-basics-cost-models.
- Full-scope original Chapter 1 review base:
  7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd.
- Isolated checkout: ../conaled-ch01-review, detached and clean.
- The full fourteen-path scope, both frozen requirement records and all prior
  findings remain. SPEC-001/002/003/V001 stay open pending matching full
  validation and final independent review. Source preflights are not approval.
- Initial Chapter 2 shared prefix remains
  c80eec92f5458eccfd1c34c8314d666c2a1e3847.

All named source refs and unfinished cross-cutting drafts remain preserved.
Historical repaired full attempts 1/2/3 have unknown terminal outcomes; the
original old-candidate ENOSPC failure is distinct. Old process IDs or progress
metadata never establish current liveness or a successful terminal result.

## Next execution sequence

1. Both independent axes have passed the frozen native environment delta with
   zero unresolved findings. See reviews/environment-native-review.md and its
   separate reports. The complete ordinary guarded route is applicable to
   these cold project outputs; every formal acceptance gate remains mandatory.
2. Create, expose and save checkpoint 0069 immediately with native instructions,
   all source/binary hashes, actual setup/cache evidence, prior fallback and
   review records. Preserve exact post-save receipts in the next checkpoint.
3. From stable 07e480f run one recorded full Chapter 1 gate, conventionally
   repaired attempt 4, through tooling/native_toolchain.py. ENVIRONMENT.md gives
   the command and thread semantics. Use the unchanged ordinary/fresh mode
   required by README and the independent Standards disposition. No compiler
   writer or source edit may race this gate. Check actual available disk space.
4. Capture actual exit, closed log and matching .lake/verification.json. Require
   all source/public-coverage/compiler checks, pre/post integrity guards,
   integrated compilation and exhaustive audit. Follow the incident runbook for
   unexplained integrity evidence; never bypass a guard or invent an outcome.
5. Resume the existing logical Chapter 1 review loop with its coordinator and
   independent Standards and Spec axes. Supply original fixed base, exact
   candidate, full fourteen-path scope, both frozen requirements, all earlier
   findings and matching validation. Both axes must pass the same candidate.
6. Immediately verify that candidate using the unchanged --verify-candidate
   gate through the native adapter. Integrate the approved tree, update local
   tickets and save an immediate acceptance checkpoint. Then activate Chapter 2
   and continue the full book, retaining its exact initial shared prefix.

## Durable and runtime evidence

Latest saved checkpoint 0068 is conaled-fdsa-0068-qemu-environment-ready.tar.gz,
libfile_9227c82658d88191ae6fc6235a02a424, SHA-256
 ef5f503c63c636bce004c8f72369b526227591146d63346a1579f806a14fc2fc,
77,067,734 bytes. Its own receipt/content inspection are retained for 0069.

Native setup evidence lives under provenance/native-environment-20261103/.
Regenerable download cleanup is recorded there. Only compressed dependency
cache files already successfully decompressed were removed. Earlier removed
download/bootstrap paths reappeared in later execution views; their previous
cleanup reports remain historical observations. archive-capacity-recovery.json
records a later digest-verified discard of the Lean and Nix download-archive
bytes, retaining zero-byte placeholders. Reacquire before using those archives;
the published digest check rejects a placeholder. All extracted active tools,
dependency build outputs, project source/history and control records remain.
Check actual available disk space at the next launch.

The foreground record_command helper preserves the owned command's actual exit
before secondary bookkeeping, full.log and any verification record. Its prior
progress-save bug was repaired and independently re-reviewed. Missing
result.json means unknown terminal outcome. Keep the execution session owned;
do not infer completion from an old progress snapshot.
