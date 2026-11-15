# FDSA formalization: governing request

Recorded 2026-11-02. Source: the user's instruction in this conversation.

> https://github.com/VladimirMarko/conaled/issues/174 says:
>
> Formalizing whole books is not required. Okasaki's Purely Functional Data Structures,
> Nipkow and collaborators' Functional Data Structures and Algorithms: A Proof
> Assistant Approach, and Appel's Verified Functional Algorithms are candidate
> sources of useful methods, not coverage milestones.
>
> Nevertheless, let's formalize Functional Data Structures and Algorithms: A Proof
> Assistant Approach in Lean in a way that's compatible with the conaled project
> and its strictures.
>
> Read and obey https://github.com/VladimirMarko/conaled/blob/master/AGENTS.md with
> the exception that we are tracking tickets locally and not on GitHub. Check out
> conaled and work on it locally. Preserve progress in durability checkpoints
> instead of uploading it to GitHub. Their purpose is to allow the recovery of the
> work done (including ticket tracking) in the event of a loss of the chat's
> workspace or even the chat itself. Expose them to me and upload them to "space"
> / "library" as soon as they are created. You have my full permission to do so.
>
> Work through the book chapter by chapter. Whenever one chapter is completely
> formalized and harmonized with conaled, move on to the next until the whole book
> is covered. You may make exceptions for cross-cutting concerns.

## Interpretation and acceptance

- The full book is the requested eventual scope. Do not substitute a small
  selection of useful algorithms or declare completion after a partial slice.
- Pin the official evolving book PDF by version date and SHA-256. Initially the
  official download is the version of July 27, 2026; verify provenance before
  closing coverage tickets.
- Work in chapter order. Earlier chapter acceptance includes all mathematical
  constructions, stated results and exercises, explicit mappings of introductory
  notation to Lean, checked uses, architecture harmonization, validation and
  independent Standards and Spec reviews. Nonformal expository assertions must
  be identified honestly rather than promoted to Lean theorems.
- Reuse existing Lean/Mathlib results when they supply exactly the required
  statement. Document the connection. Existing code is not presumed equivalent
  without checking definitions, hypotheses and resource models.
- Preserve conaled's separation of operations, observations, laws,
  representations, costs and target capabilities. A book representation is an
  optional realization, and its cost count is an explicit model.
- Retain native Lean clients; claim transport across mathematical settings only
  when a corresponding checked preservation theorem is supplied.
- All new formal claims require statement review and meaningful checked
  specializations or applications. Admissions, new axioms and native evaluation
  shortcuts are forbidden by the project proof audit.
- Use the pinned Nix shell and Lean/Lake dependencies. Candidate verification and
  independent reviews must refer to the same immutable source commit. No chapter
  closes while required checks or review findings remain unresolved.
- Tickets are local files in this control directory. No GitHub mutations or
  pushes. Local Git commits and recovery archives are explicitly authorized.
- Each checkpoint is self-contained for task recovery: complete Git history,
  tracked and task-related untracked source changes, local tickets, requirements,
  source provenance, review/validation records, status and recovery instructions.
  Toolchain binaries and dependency caches can be re-fetched from pinned sources.
- Upload each completed checkpoint immediately and expose its saved link to the
  user. A checkpoint may truthfully contain incomplete/unverified work; saving
  it does not constitute chapter acceptance.

## Starting state

Repository: https://github.com/VladimirMarko/conaled.git

Base commit: 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd

On checkout, index and tracked working tree were clean. The following unrelated
untracked file was already present and is preserved in place, excluded from
task changes and recovery archives:

`docs/history/algorithm-design-haskell/.checkpoint-233.zip.n7UlkJ`

Its presence does not authorize deletion or modification. Isolated candidate
checkouts omit it, allowing the project's clean-candidate validation.

This request is the full-spec source for later reviews. Each chapter ticket
adds precise bounded acceptance criteria without reducing the eventual scope.


## Explicit environment exception — 2026-11-03

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

## Working environment recipe supplied by the user — 2026-11-03

The user supplied a verified setup guide and instructed: “Here are instructions
on how to set up the environment by another agent that should work. They do,
please include the equivalent instructions in your next checkpoint. Then resume
work on the formalization.”

Apply its exact official Lean/Lake plus QEMU user-mode procedure to this FDSA
checkout, retaining the previous explicit Nix exception and every acceptance
gate. Preserve the source guide and equivalent FDSA-specific recovery
instructions in the next checkpoint. References in the supplied guide to a
different book/checkpoint are provenance, not a change to this task's source,
branch, candidate or requirements. See provenance/qemu-environment-20261103/
user-request.json and its retained attachment.

## Native environment alternative requested — 2026-11-03

The user identified the supplied QEMU route as too slow and requested: “Let's
find an alternatives.” Prefer a verified native execution route while retaining
the exact Lean/Lake/dependency versions and all formal acceptance gates. This
steers the environment work; the complete FDSA goal and checkpoint obligations
continue. Preserve checkpoint0068 and its tested emulation instructions as
history. See provenance/native-environment-20261103/user-request.json.

## Current recovery and checkpoint steering — 3 November 2026

The user supplied recovery 0069 and the unified native kit and instructed us to
resume the entire formalization and integration preparation. The user explicitly
reaffirmed permission for repeated checkpoint uploads, requested inclusion of
the updated setup, and clarified that checkpoints are for current recovery, not
reconstruction of historical project states; keep them small when possible.
Compact packaging may externalize a reproducible public baseline asset with
strict byte/Git pins, while preserving all new work and exact recovery identities.
See provenance/compact-checkpoints-20261103/user-steering.md. Formal scope and
all acceptance requirements above are unchanged.

## Recovery steering — 4 November 2026

The user supplied exact checkpoint0080 and reaffirmed the whole-book goal,
local-only work, compact standalone checkpoints, Nix-only exception and every
formal acceptance gate. Read provenance/recovery-20261104-host-preflight/
user-steering.md for the current supplied facts and continuation requirements.
It explicitly preserves accepted Chapter1, fixes the first pending candidate
to f17cc6b, declares the old full attempt's terminal result unknown, and forbids
polling historical session IDs. Inspect the new host and respect the unchanged
space prerequisites before starting installation/build. A genuine resource
blocker leaves completion pending; it does not relax the mathematics or gates.
