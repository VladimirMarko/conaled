# Comparison of the two direct Lean/Lake environment routes

## Current decision and limits

Pursue native execution of the pinned release. The user subsequently identified
CPU emulation as too slow and asked for alternatives; the exact steering is in
`../requirements/REQUEST-native-toolchain-042.md`. The reviewed QEMU setup is
retained as a recovery fallback. Its slow full run was intentionally interrupted,
with the original partial record and separate tool-interruption evidence saved.

A native compatibility library now supplies only an absent own-executable-path
lookup under an explicit direct/frozen/canonical ELF launch contract. Lean,
Lake and their kernel/compiler libraries remain byte-identical to the official
release and execute natively. Genuine version, valid/false-proof, native build
and executable tests passed; eighteen bounded metadata/delegation cases passed.
This implementation still needs the complete current independent review and
applicable candidate gates. See `RECOVER-ENVIRONMENT.md` and
`native-performance-analysis-042.md` for the executable route and evidence.

The table below compares the two **QEMU** routes assessed before that steering.
They share the same central design: unmodified official Lean4.35.0, bundled
Lake, an executable overlay, and QEMU user-mode metadata support. The supplied
Ubuntu package has stronger independently verified acquisition provenance; no
runtime/performance superiority of that Ubuntu emulator was demonstrated.

This comparison addresses the user's checkpoint-handoff request preserved in
`../requirements/REQUEST-environment-handoff-042.md`. The complete supplied
guide is preserved byte-identically at
`../references/conaled-environment-guide-from-user-042.md`, SHA256
`ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1`,
34828 bytes. Its embedded adapter source hashes to
`a343cdbb5aba405c52bca3f5664dfaef592331fa559ba41c232536907febbc47`.
The guide describes another session's observations; only the separately
identified checks below were repeated here.

**The other guide's checkpoint039 belongs to another workstream.** Its archive
SHA256 begins `5ac95084`, its branch is `local/adwh-continue-2026-11-03`, and
its candidate is `f62c48c8e5703ed68a5882216a07cb5c66d2eca4`. Those are not this
PFDS workstream's checkpoint039, main branch or candidate. Do not copy its
restoration identity, formal acceptance commands, or old Library references.
No other-conversation Library file was accessed during this comparison.

The PFDS-specific takeover entry point is `RECOVER-ENVIRONMENT.md`. It includes
the exact acquisition and dependency recipes, source restoration identity,
public compiler smoke tests, current validation commands, and recovery limits.

## Evidence-based comparison

| Aspect | Reviewed PFDS QEMU fallback | Supplied QEMU guide | Assessment |
| --- | --- | --- | --- |
| Lean and Lake | Official Lean 4.35.0 archive; byte-identical executables; observed Lake 5.0.0-src+eb6cafb | Same official release and executable digests | Same compiler pin; neither needs Nix for this route. |
| QEMU artifact | Debian `1:7.2+dfsg-7+deb12u18+b3`, executable reporting 7.2.22 | Ubuntu `1:8.2.2+ds-0ubuntu1.18` | Different runtime input; a newer version alone does not demonstrate improved reliability or speed. |
| Package provenance | Official HTTPS Debian index and actual package/executable digests checked; no verified GPG chain is claimed | Signed Ubuntu InRelease to exact index to exact package | The Ubuntu acquisition has stronger verified provenance after the independent authentication performed here. |
| Overlay construction | Stage a complete profile, then rename atomically; refuse an existing profile | Fill or verify an existing overlay; refuse conflicting entries; not an atomic construction | Ours avoids exposing a partly constructed profile. The guide's approach is convenient to rerun after a partially completed setup. |
| Inspection | `--describe` is read-only and verifies current identities | `--describe` calls overlay preparation and can create files | Our inspection has a narrower side effect contract. A future session must know that the guide's command is also setup. |
| Child boundaries | Wrap `lean`, `lake`, and `leanir` with regular copies at the profile entrypoints | Wrap Lean/Lake using regular copies in `libexec`; postponed compilation is explicitly unvalidated | Both handle ordinary Lake-to-Lean execution. Our additional `leanir` wrapper is structural coverage; no postponed-compilation acceptance is claimed. |
| Inherited environment | Explicit PATH, library paths, sysroot, both Lake/Mathlib cache paths, TMPDIR, and one Lean thread | Clears several inherited Lean/Lake selectors, scopes XDG cache/config/state, and sets `LAKE_OVERRIDE_LEAN` | The guide better addresses accidental selector inheritance. Our explicit `LAKE_CACHE_DIR` avoids that particular inherited cache input. Any code hardening needs a new frozen candidate and review. |
| Artifact preconditions | Archive and individual executable hashes retained; the new runbook checks originals before profile creation | Expected executable hashes embedded in its adapter | The guide's embedded preconditions are useful defense against selecting the wrong input. Our existing launcher verifies the created profile's recorded identities. |
| Current public tests | Actual version checks, valid theorem with no axioms, false theorem rejected, Lake compiler path, native executable build/link/run, cold-recovery and refusal tests; both review axes passed | Reports version/theorem/cache tests from its own session | Current PFDS evidence is available locally and tied to the active helpers. The other guide's historical runtime logs and review artifacts were not imported. |
| Resource settings | Recorded active full check uses one build job and one Lean thread | Describes a four-thread command on a host reporting nine CPUs and roughly 10 GB memory | Thread count affects scheduling/resources. It has not been compared under the same workload here and must not change inside an active frozen run. |
| Source and cache recovery | Exact nine dependency revisions, origins and clean states verified; cache bootstrap/get completed | Includes detailed clone/fetch and cache recipes | Both preserve pins. The new PFDS runbook makes our previously distributed provenance and recovery steps self-contained. |
| Optional Nix experiment | Nix is not needed under the user's explicit exception | Reports QEMU-backed Nix startup, a tiny offline evaluation, and a local derivation | These limited tests do not establish a working full conaled flake. Recreating Nix is not on the current required path. |

## Ubuntu authenticity checks performed in this workspace

The independent acquisition record is `qemu-ubuntu-042/acquisition.json`; its
human-readable report is `qemu-ubuntu-042/report.md`. It used the installed
public Ubuntu archive keyring at
`/usr/share/keyrings/ubuntu-archive-keyring.gpg`, not an independently acquired
new trust root. `gpgv` returned zero and `VALIDSIG` for
`F6ECB3762474EDA9D21B7022871920D1991BC93C`. The signed release identifies
Ubuntu24.04 `noble-updates`, dated 2026-11-03 12:40:01 UTC, and its signature
is dated 12:40:55 UTC. No `Valid-Until` field is present.

The signed SHA256 entry authenticated `universe/binary-amd64/Packages.xz`.
The download used its by-hash URL, checked its exact bytes and digest, and
selected the exact version/architecture stanza. The downloaded package and
the single regular x86-64 executable extracted from it matched the guide:

| Authenticated object | Bytes | SHA256 |
| --- | ---: | --- |
| InRelease | 126125 | `5f4cbfd1daf09c5c6af3eeb67fe923b15010f28d9189b64995e2c0f68eec7b77` |
| Packages.xz | 1707340 | `2dd82d93dc7fab28f67d5120aa122d8896b557ce4984995635a7dfff1353386d` |
| Ubuntu QEMU package | 14709858 | `5bb397f66063efa349f6fd5cb3b68cd96f29edd0994e4ba5115cf0859a716bf0` |
| Extracted `qemu-x86_64-static` | 3751320 | `90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0` |

Official sources:

- <https://archive.ubuntu.com/ubuntu/dists/noble-updates/InRelease>
- <https://archive.ubuntu.com/ubuntu/dists/noble-updates/universe/binary-amd64/by-hash/SHA256/2dd82d93dc7fab28f67d5120aa122d8896b557ce4984995635a7dfff1353386d>
- <https://archive.ubuntu.com/ubuntu/pool/universe/q/qemu/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb>

The checkpoint retains the signed release, exact compressed index, public
keyring, selected package metadata, actual commands/statuses, and hashes.
This preserves the membership proof from signed release through package
stanza. A copied public keyring records the trust input; it does not
independently establish trust in its own contents. Moving repository metadata
may change after this observation. Newly downloaded moving metadata must be
authenticated again; do not assume a newer release contains the old package.

The Ubuntu emulator was **not executed or selected**. No speed comparison,
Lean/Lake runtime equivalence, four-thread resource recommendation, or formal
project result follows from this acquisition. No system package was installed.

## Current PFDS evidence and adoption boundary

The existing eight operational helper files were reviewed on immutable
candidate `822cb7adeed4943acaf10454e9facfc2e3ee8ceb`, with both Standards and
Spec passing. Their evidence and scope are retained in
`../reviews/direct-toolchain.md` and the round2 reports. This comparison and
the new takeover runbook are subsequent documentation additions; the earlier
approval does not by itself approve these additions. The checkpoint generator's
README template and restore-success pointer are also corrected to name this
runbook and the user's Nix exception. Its previous complete source is retained
at `../validation/checkpoint-generator-before-042.py`, SHA256
`617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab`.
The archive capture, integrity checks and actual restoration procedure are
unchanged by that documentation correction.

`../validation/direct-toolchain-final-verification-041.json` records delivered
helper identity. The CLI and Lake test records establish the actual public
toolchain behavior; `direct-dependencies-after-cache-041.json` establishes all
nine manifest revisions and clean dependency source after cache retrieval.
The cache bootstrap/get records preserve their real exits and commands.

The exact901 fresh full check and exactd24 focused build were launched after
checkpoint041. The focused record `../validation/signed-d24-direct-r1.json`
ended with exit1 at 2026-11-03T16:00:25Z, unchanged inputs and a clean checkout.
Its log identifies ambiguous `bind`/`pure` references and an unresolved budget
calculation in example proofs. The full record remains separate; consult its
actual latest status. No compiler smoke test, package authentication, partial
compile log or documentation review accepts either formal candidate.

The QEMU acquisition comparison did not change the active runtime. The later
native implementation is separately captured and tested, with its own profile,
compatibility source/library and native-bound validation runner. Original
release bytes, dependency pins, stock checks and acceptance requirements are
unchanged. Parallel proof-only corrections produce formal candidate3cf3de4f after the
preserved d24/956 failures; its source review and compiler evidence remain
separate from runtime approval.
New native gate evidence cannot be relabeled as the old QEMU run's result.

## Native behavior and measured performance

The metadata layer first calls the existing `readlink` implementation. It acts
only on `ENOENT` for the current process's own executable link, with a marker
matching its existing `AT_EXECFN` value and a canonical absolute regular ELF.
Other results and permission errors are preserved. Pre-existing preload
entries keep their order and precedence. It does not use a raw-syscall escape,
modify the compiler or kernel, mount procfs, or emulate machine instructions.
Its explicit unsupported cases and frozen-input assumptions are documented in
the recovery guide and source analysis; it is not general libc equivalence.

`../validation/native-cli-042-r1.json` records exact versions, a valid theorem
with no axioms, and a false theorem rejected with an actual type mismatch.
`../validation/native-lake-build-042-r1.json` records Lake using the compiler,
compiling/linking, and running the resulting executable with output42.
`../validation/native-own-exe-contract-042-r1.json` records18 passing cases on
the guarded resolver revision, including controlled downstream success/denial,
child exec, fork, constructor/concurrent calls, buffer behavior, and stale-marker
refusal. Controlled failures are identified as fixtures, not protected-host
observations. The complete current review must bind applicable evidence to the
actual delivered candidate; these records alone are not approval.

For the same import-Lean fixture, a sequential native/QEMU diagnostic measured
31.786seconds versus86.080seconds. Native user/system CPU was1.473/7.885seconds;
QEMU was9.486/21.369seconds. Another native statistics run took102.323seconds.
All11870 imported regions were memory-mapped, totaling2009200824artifact bytes,
so that run does not support failed mapping/wholesale relocation as its cause.
Large major-fault/input counters and wall time beyond CPU time implicate import
I/O/page-fault latency; this is an inference, not a controlled attribution to
one storage cause. The report preserves the actual counters and timing
variability. One pair is not a general2.7-times speedup guarantee.

No alternate normally provisioned execution host is exposed in this session.
Such a host could run the official pinned binaries directly without this
compatibility layer, while retaining the same source/proof gates. No external
host, GitHub workflow, or cloud service was provisioned or published to.

