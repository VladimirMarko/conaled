# FDSA-ENV — QEMU setup passed, cache setup in progress

The user-supplied route has been applied to this FDSA checkout. All twelve
actual setup checks pass, including bare/Lake-child Lean 4.35.0 and exact
commit, shared prefix/path checks, and two real proof compilations with
matching outputs. QEMU's package and executable were authenticated through
signed Ubuntu metadata. Original compiler bytes, project pins and all nine
clean dependency sources are unchanged.

Use ../ENVIRONMENT.md and ../tooling/pinned_toolchain.py for self-contained
recovery. The cache utility build has a foreground recorder under
../provenance/qemu-cache-build-20261103-r1/; no full formal gate or chapter
acceptance is implied. Environment implementation review and checkpoint0068
are in preparation. Earlier blockers below are historical.

# FDSA-ENV — Pinned development environment

State: **exact direct toolchain and dependency sources acquired; Lean startup
blocked by unavailable own-process executable path**.

The user explicitly waived only the Nix-shell requirement on 2026-11-03.
Correct directly acquired program versions are authorized. The stock official
Lean v4.35.0 release matches its publisher digest, and all nine dependency Git
checkouts match the unchanged manifest and are clean. Lake's actual version
command succeeds with explicit shipped-library paths.

Lean's version, githash, prefix and import/compilation smoke tests all fail
before CLI processing with `failed to locate application`. Exact source
inspection confirms its unconditional Linux `/proc/<getpid()>/exe` readlink.
That own-process path is unavailable here. LEAN_SYSROOT does not override the
startup lookup. No compiler patch, interception or security change is selected.

No dependency cache retrieval or project verification has begun. See
`../provenance/direct-environment-20261103/diagnosis.md` and CURRENT.md. The
next prerequisite is a usable native process-filesystem interface, not Nix.

## Historical Nix/recovery status

# FDSA-ENV — Pinned development environment

State: **blocked in recovered workspace**. Cross-cutting setup.

Recovery 2026-11-03: the source checkpoint excludes Nix/Lean and dependency
caches. None was preinstalled here. The standard installation was rejected
before execution by the session approval policy. The documented workspace-local
portable alternatives failed on prohibited tracing and an unavailable `/proc`
file respectively. Exact evidence: `../provenance/recovery-20261103/environment-attempts.json`.
No usable pinned shell or project verification resulted.

Resume in an environment with usable Nix, preserving flake.lock, lean-toolchain
and lake-manifest.json. Then run the smoke check and retrieve/verify the exact
nine dependency revisions. Existing user authorization is sufficient; the
blocker is the current execution environment, not a missing task decision.

## Historical successful setup in the previous workspace

# FDSA-ENV — Pinned development environment

State: checked. Triage: ready-for-agent. Cross-cutting setup.

The unchanged repository Nix flake supplies Lean 4.35.0 and Lake. All nine
manifest dependency revisions are checked out clean; 9,031 cache files were
retrieved successfully. See `../provenance/environment-setup.md`.

The setup check is not a whole-project proof audit. Chapter acceptance retains
its own immutable-candidate checks.
