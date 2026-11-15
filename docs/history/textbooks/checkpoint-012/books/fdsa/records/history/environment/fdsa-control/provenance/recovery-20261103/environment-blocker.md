# Recovered environment blocker — 2026-11-03

The source recovery succeeded. Compilation cannot start in this session's
available execution environment. This is an environment failure, not a Lean
source failure or a successful verification.

## Observed evidence

- No Nix, Lean, Lake, Elan or direnv was installed; no `/nix`, `.lake` package
  checkout or compiled cache was supplied by the source checkpoint.
- Public downloads work. Current upstream AGENTS.md is byte-identical to the
  checkpoint. The official book download matches the pinned July 27, 2026 PDF.
- The standard Nix 2.35.4 installer was downloaded, but its execution was rejected
  before it ran: the session approval policy forbids the required elevated
  filesystem permission. It was not a refusal by the user.
- A separate workspace-confined portable Nix release was downloaded and checked
  against the release's declared byte size. Its observed SHA-256 is recorded in
  `environment-attempts.json`; no release-provided cryptographic digest was
  available. Its configuration directed the physical store, caches, Elan and
  temporary directories into the task workspace, leaving HOME unchanged.
- That release's proot runtime failed with `ptrace(TRACEME): Operation not
  permitted`. Its bubblewrap runtime failed because
  `/proc/sys/kernel/overflowuid` was unavailable. These are separate observed
  failures. No host tracing, namespace, filesystem or other security control
  was changed; no further workaround is selected.

The exact selected diagnostics and outcomes are in `environment-attempts.json`.
They are transcribed tool-output excerpts, not a claim to have captured a
complete installer log. A missing `/proc` file is not evidence that a process
terminated, and the bubblewrap error does not prove a particular namespace
permission failure. Portable Nix never reached a usable development shell.

## Work preserved and acceptance limits

All 654 input payload checksums passed. All 45 named Git refs match the input
bundle; its eight other advertised HEAD entries have the same object IDs as
retained named refs. Main remains `1aabd512284fe86254278ac631eda061d311050b`.
The isolated Chapter 1 candidate is clean at
`07e480f6ec9958d4975bb90151005b84f2907614`, with original review base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` and the complete fourteen-path scope.

The old guarded attempt 3 has no terminal result in checkpoint 0065. Preserve
its raw running record and partial log as historical; its outcome is unknown.
No new Lean compiler, project checker, proof audit or final review was run.
No chapter, appendix or shared unit is accepted. SPEC-001/002/003/V001 remain
open under their retained final-review and validation requirements.

## Required continuation

Use this source checkpoint in a development workspace with Nix already usable,
or where its normal installation is permitted. Fetch the unchanged pins and
run the candidate's complete guarded check. Then resume the existing logical
review loop with a replacement coordinator and independent Standards and Spec
reviewers, retaining the original base, requirements and all finding IDs.
Immediately verify the successful candidate record before accepting Chapter 1.

`CURRENT.md` gives the exact next sequence. The whole book remains the goal;
this blocker changes neither the coverage scope nor the acceptance standard.
