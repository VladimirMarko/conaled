# Local #1031: user-authorized direct pinned toolchain

## Authoritative amendment

User message, 2026-11-03, in this continuation:

> The Nix shell is defined for consistency and convenience, but is not strictly necessary for continued development. You have my permission to disregard `AGENTS.md` in this respect, if you are able to separately acquire the correct versions of required programs.

This amendment permits direct acquisition and invocation of the correct required
program versions instead of Nix/direnv. It applies to ongoing development and
validation. Preserve the exact compiler and dependency pins in lean-toolchain,
lakefile.toml and lake-manifest.json. Record the origin, checksum, actual program
versions and environment used. No repository tooling change is needed solely to
exercise this permission. Nix-specific wrappers in historical commands may be
omitted while retaining the same underlying check/audit/regression operations.

All other requirements remain: clean isolated candidate, stable input identities,
fresh and separate guarded validation, exhaustive proof audit, managed ProofAudit
prerequisite and regression, independent Standards and Spec review, immediate
final candidate verification, chapter ordering, local tickets, and promptly
exposed/uploaded recovery checkpoints. No GitHub write is authorized.

The prior Nix environment blocker in #1030 is superseded to the extent a verified
direct toolchain is available; this amendment itself is not a successful setup,
formal validation result, or chapter acceptance.
