# User clarification: Nix is optional for continued development

Recorded 2026-11-03 (Atlantic/Reykjavik).

The user explicitly clarified:

> The Nix shell is defined for consistency and convenience, but is not strictly
> necessary for continued development. Can you get the required Lean and Lake
> versions without it?

Continue the existing book/thesis formalization task by installing and using
the exact pinned Lean/Lake toolchain directly where supported. This overrides
the repository/session requirement to launch project commands through Nix.
It does not waive any compiler/dependency version pin, clean isolated candidate
requirement, build, proof audit, independent review, final candidate verification,
chapter ordering, local-only tracking, or checkpoint obligation.

Preserve the earlier Nix capability investigation and approval rejection as
historical evidence. A Nix-specific installation failure no longer establishes
that all permitted development routes are blocked. Record actual direct-binary
installation, version, dependency and build outcomes, including any distinct
runtime limitations discovered. Do not infer success from download alone.

Expected Lean pin: leanprover/lean4:v4.35.0. The official matching release also
supplies Lake. Verify both actual version outputs and use exact dependency Git
revisions from the unchanged lake-manifest.json.
