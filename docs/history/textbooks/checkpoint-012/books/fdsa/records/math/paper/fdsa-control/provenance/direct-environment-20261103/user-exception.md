# User-authorized direct toolchain — 2026-11-03

The user supplied this continuation instruction after checkpoint 0066:

> The Nix shell is defined for consistency and convenience, but is not strictly
> necessary for continued development. You have my permission to disregard
> `AGENTS.md` in this respect, if you are able to separately acquire the correct
> versions of required programs.

This explicitly supersedes the Nix-only execution requirement for this task.
It does not waive the pinned Lean/Lake or library revisions, the whole-book
scope, local-ticket and no-GitHub-write rules, source policy, proof audit,
immutable-candidate validation, independent Standards/Spec review or immediate
candidate verification. The former Nix setup failures remain historical.

Root will acquire the official Lean v4.35.0 Linux distribution (which includes
its matching Lake), restore the nine exact Git dependency revisions, and run
unchanged project commands in the isolated Chapter 1 candidate. Record observed
supporting-tool versions and every actual command/outcome. No changed repository
configuration is required or authorized merely to make a check pass.
