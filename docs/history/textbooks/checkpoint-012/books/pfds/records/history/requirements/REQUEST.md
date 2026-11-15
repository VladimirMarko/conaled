# User authorization and requested outcome

Recorded 2026-11-02 (Atlantic/Reykjavik). This is the conversation's full task text.

> https://github.com/VladimirMarko/conaled/issues/174 says:
>
> Formalizing whole books is not required. Okasaki's *Purely Functional Data Structures*, Nipkow and collaborators' *Functional Data Structures and Algorithms: A Proof Assistant Approach*, and Appel's *Verified Functional Algorithms* are candidate sources of useful methods, not coverage milestones.
>
> Nevertheless, let's formalize *Purely Functional Data Structures* in Lean in a way that's compatible with the `conaled` project and its strictures.
>
> Read and obey https://github.com/VladimirMarko/conaled/blob/master/AGENTS.md with the exception that we are tracking tickets locally and not on GitHub. Check out `conaled` and work on it locally. Preserve progress in durability checkpoints instead of uploading it to GitHub. Their purpose is to allow the recovery of the work done (including ticket tracking) in the event of a loss of the chat's workspace or even the chat itself. Expose them to me and upload them to "space" / "library" as soon as they are created. You have my full permission to do so.
>
> Work through the book chapter by chapter. Whenever one chapter is completely formalized and harmonized with `conaled`, move on to the next until the whole book is covered. You may make exceptions for cross-cutting concerns.

## Operational interpretation

- Source scope: Cambridge book (1998), all eleven chapters and mathematical obligations in their exercises; Appendix A must be accounted for against the chapter implementations. Do not substitute the thesis for the expanded book.
- Read each chapter before claiming exhaustive coverage. Record every substantive construction, invariant, correctness, complexity, sharing, scheduling, or persistence claim, plus exercises. Classify exposition and programming-language syntax honestly; do not manufacture irrelevant theorems to inflate coverage.
- Sequential acceptance: a later chapter may be researched, and necessary shared foundations may be developed, while the current chapter is open. Do not mark a chapter complete or advance its implementation frontier until its actual scope is checked, reviewed and accepted.
- Reuse existing domain modules, ordinary Lean interfaces, squares, fusion and resource accounting. Keep representations optional; distinguish semantics, invariants, observations, costs and target assumptions.
- Per-chapter implementation uses `.agents/skills/implement/SKILL.md`, the shared review procedure, example-driven development and independent Standards and Spec reviews. A missing build, audit, source or review is a pending gate, not approval.
- Tickets and review records live in `session/`, outside the source diff, and are included in every recovery checkpoint. Local ticket numbers 10000 onward refer only to this workstream, never to GitHub Issues.
- Work branch: `pfds/local`; original base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- All progress stays local with immediately uploaded recovery archives. No GitHub issue/PR/comment/push is authorized by this task.

## Repository baseline

Cloned public `https://github.com/VladimirMarko/conaled.git` with a clean worktree on 2026-11-02. HEAD title: `feat(linear): add measured structured matrix realizations (#265)`.
Lean pin: `leanprover/lean4:v4.35.0`; Mathlib revision: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The full issue #174 snapshot is `github-174.json` (read-only upstream context; task authorization above changes the book-coverage objective and tracking destination).

## Checkpoint recovery policy

Each numbered checkpoint is self-contained: complete Git bundle, exact HEAD/branch and index/worktree patches, untracked task files, local ticket graph, requirements, review records, validation evidence and next actions. Exclude reproducible build caches, downloaded third-party manuscripts and credentials. Verify bundle and member checksums and test restoration before calling a checkpoint recoverable. Preserve an explicit incomplete status when work is in progress. Recovery must not require the original chat.
