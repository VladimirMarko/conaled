# Effective requirements amendments

The historical REQUIREMENTS.md and specs/1002-full-requirements.md are retained
byte-for-byte. Read them together with the following accepted narrow amendment.

## #1027 — Optional project-cache recovery companion

- Amendment: cache-companion/AMENDMENT.md.
- Accepted operational candidate: a43cef4881d4eb303a81ef25f5ccff0b801a12fe.
- Acceptance and exact evidence: validation/1027-acceptance.json.
- Both independent Standards and Spec reviews passed; root verified all delivered
  files against the same approved snapshot.

The explicit exception permits a separate optional cache companion tied to a
named uploaded complete source checkpoint. It changes both the earlier cache
exclusion and standalone-archive rule only for that companion. Complete source
checkpoints remain mandatory and cache-free. Every formal acceptance gate,
chapter dependency and prohibition on GitHub writes remains unchanged.
The accepted tool must first be preserved in a complete uploaded checkpoint.
No actual cache capture or chapter acceptance is implied by this amendment.

## #1031 — Direct pinned toolchain permitted by the user

The user explicitly permits disregarding AGENTS.md's Nix/direnv requirement when
the correct required program versions are acquired separately. The verbatim
authorization and its narrow scope are in
[specs/1031-direct-toolchain-amendment.md](specs/1031-direct-toolchain-amendment.md).
Nix-specific wrappers may be omitted; compiler/dependency pins, formal validation,
independent reviews, chapter order and checkpoint/publication rules remain.
Historical REQUIREMENTS.md and prior evidence are not rewritten.

## #1032 — User-supplied QEMU execution setup

The user supplied a complete QEMU user-mode route and instructed us to apply it,
preserve equivalent instructions in the next checkpoint, and resume VFA. Read
specs/1032-qemu-environment.md and tooling/README.md. This explicitly authorized
execution adaptation runs unchanged pinned compiler binaries inside the existing
host restrictions. It adds no waiver of source/proof/audit/review gates and does
not adopt the guide's unrelated ADWH candidate or acceptance status.

## #1033 — Native alternatives requested by the user

The user explicitly requested alternatives to slow emulated tooling. The exact
steering and bounded native compatibility scope are retained in
[specs/1033-native-app-path.md](specs/1033-native-app-path.md). The supplied QEMU
recipe remains preserved; a successful reviewed native route may replace its
execution role without changing official compiler bytes or formal gates.

## #1036 — Supplied unified native setup and latest-state recovery

The user explicitly selected the supplied unified native kit, allowing a more efficient verified route if found. The kit is included intact in the next checkpoint; `tooling/UNIFIED-NATIVE.md` records the active VFA-specific isolated dependency layout and commands. This is an execution/setup choice, with no compiler-pin, source-policy, proof, review, or chapter-order waiver.

The user also clarified that checkpoints exist for recovery of current work, not reconstruction of previous project states, and should be small to permit frequent uploads. A fixed immutable source-base companion plus each cumulative current checkpoint replaces repeated embedding of the complete history/source in every archive. Recovery requires the base and latest checkpoint only, with no chain. All current source, tickets, required evidence and environment recipe remain recoverable; see `specs/1036-compact-recovery.md`.
