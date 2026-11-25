# Selected source and provenance

This directory selects source from the user-supplied native kit 1.0.0 of
3 November 2026 and adds a small profile/command interface for the unified
checkpoint. Exact selected source origins and official input identities are
recorded in `PINS.json`.

`lib/app_path.c` is unchanged from the supplied ADWH-derived adapter, SHA-256
`fefc39d8645e4a938d6cc27574257d1a1e8e8f0790b75cc15bcf074272066fe0`.
`lib/runtime.py` retains the narrow per-program launch mechanism and the
outer/inner environment distinction. Its changes remove imposed thread limits,
use the new source-only profile version, and name the current verification
command. `native_profile.py` derives profile creation and integrity checks from
the supplied CLI, without its downloader, dependency-acquisition subsystem,
historical cache relinker, logging subsystem, or stored evidence.

The receiving restart seed selects the host compiler's glibc loader before
standard system paths. This avoids treating NixOS's `/lib64` compatibility
trampoline as a directly callable loader. Official distribution pins and the
per-program application-path adapter are unchanged.

This directory contains no official compiler or runtime binaries, compiled
adapter, generated C from Lean, frozen cache objects, cache executable,
dependency repository copies, downloaded archives, or historical transcripts.
The adapter is compiled locally into external writable state. Official Lean
and other separately acquired dependencies retain their own licenses and
notices in their distributions. This notice does not relicense the user's
source material or override any upstream license.

The old kit's whole-distribution checksums and 299-file inventory do not describe
this selection. Use the seed inventory for the delivered files and
the native helper's explicit verification scope for installed state. Historical
kit acceptance and timings are not validation of this derived implementation.
