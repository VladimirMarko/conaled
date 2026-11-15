# Local #1030: checkpoint035 recovery and execution environment

Source: the user's current continuation request, 2026-11-03:

> Continue this work to completion from the provided checkpoint `conaled-vfa-checkpoint-035-returned-archive-preservation.tar.gz`.

Read this alongside the unchanged REQUIREMENTS.md and AMENDMENTS.md. The objective
remains complete chapter-by-chapter VFA formalization harmonized with conaled.
This ticket records recovery and the concrete execution blocker, not a change of
scope or an alternative completion milestone.

Required recovery work: verify the supplied archive, source/index and history;
retain local tickets/reviews; compare current AGENTS and pinned textbook source;
separate historical run state from the new environment; establish the pinned
Nix development shell; then resume the existing formal gates. If that environment
is inaccessible, preserve the exact boundary and useful recovery results in a
complete, restore-checked, promptly uploaded checkpoint. Do not invent validation
results, mark a chapter accepted, start a successor chapter, change the pins,
modify access controls or replay historical cleanup against new paths.

No conaled implementation change is part of this recovery record. Prior source
reviews remain historical source evidence, with overall Standards and Spec
blocked until their existing acceptance gates are discharged.

## Superseding environment amendment

The user's subsequent permission in local#1031 waives the Nix/direnv wrapper
requirement if correct required tools are independently acquired. Read
1031-direct-toolchain-amendment.md and AMENDMENTS.md. The historical Nix blocker
above must not be reimposed. The current blocker is the verified direct Linux
Lean binary's need for /proc/<pid>/exe; all formal gates remain unchanged.
