# VFA formalization: authoritative local requirements

Source: user instruction in this conversation, 2026-11-02 (Atlantic/Reykjavik).
Upstream baseline: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Repository: https://github.com/VladimirMarko/conaled
Related scope: https://github.com/VladimirMarko/conaled/issues/174

## User request (verbatim)

> Nevertheless, let's formalize *Verified Functional Algorithms* in Lean in a way that's compatible with the `conaled` project and its strictures.
>
> Read and obey https://github.com/VladimirMarko/conaled/blob/master/AGENTS.md with the exception that we are tracking tickets locally and not on GitHub. Check out `conaled` and work on it locally. Preserve progress in durability checkpoints instead of uploading it to GitHub. Their purpose is to allow the recovery of the work done (including ticket tracking) in the event of a loss of the chat's workspace or even the chat itself. Expose them to me and upload them to "space" / "library" as soon as they are created. You have my full permission to do so.
>
> Work through the book chapter by chapter. Whenever one chapter is completely formalized and harmonized with `conaled`, move on to the next until the whole book is covered. You may make exceptions for cross-cutting concerns.

## Interpretation and acceptance

The book is Software Foundations volume 3, Andrew W. Appel, *Verified Functional
Algorithms*, version 2.1 (2026-08-24 10:11). Source archive:
https://softwarefoundations.cis.upenn.edu/vfa-current/vfa.tgz . Hashes and a
declaration/exercise inventory pin this moving URL. All substantive chapters,
including optional and advanced mathematical exercises, are in scope. Preface
and Coq-specific mechanics receive explicit Lean adaptations. Failed/aborted
pedagogical proofs are not separate mathematical claims, but the intended
successful claim must be covered. Manual grading stubs are not algorithms.

Proceed in current table-of-contents order: Preface, Perm, Sort, Multiset,
BagPerm, Selection, Merge, Maps, SearchTree, ADT, Extract, Redblack, Trie,
Priqueue, Binom, Decide, Color. Source reconnaissance and environment/durability
work may cross chapter boundaries. Do not start the next formalization chapter
before the preceding chapter has met its completion gates.

For each chapter retain an explicit source-to-Lean coverage map, faithful source
algorithms or proved adapters, reusable contracts that fit existing conaled
interfaces, checked specializations/applications, and statement review.
Existing theorems may discharge obligations when their assumptions, semantics,
and recurrence match; merely naming a similar container is not coverage.
Separate operations, observations, invariants, and resource assumptions. Do
not claim arbitrary-setting transport or runtime costs from value equality.
Preserve important differences: total/default-valued tables vs optional maps,
maximum vs minimum priority queues, and alternating-split merge sort vs stable
contiguous-split merge sort. Model source extraction assumptions explicitly and
discharge them for Lean realizations; do not introduce prohibited axioms.

Repository AGENTS.md and all applicable pointers apply, except tracker writes
and publication: tickets and review evidence are local, and no GitHub pushes,
issues, PRs, or comments are authorized. Conventional commit issue references
in this branch are local ticket numbers 1000 and above, not GitHub issue IDs.
Use the implement workflow for each chapter-sized implementation/review loop.
Independent Standards and Spec reviewers remain required. Review scope, base,
candidate, evidence, and unresolved findings survive checkpoints.

Formal completion requires the Nix/direnv environment, required integrated
build and exhaustive proof audit in an isolated clean candidate checkout,
`./check.sh --candidate HEAD`, both independent review axes passing on that
same candidate, then `./check.sh --verify-candidate HEAD` immediately before
acceptance. Admissions, new axioms, unsafe definitions, native-decide shortcuts,
and unproved claims are not completion. Build or access failures leave the
chapter pending; they do not waive its gates.

Every recovery archive must preserve complete source, Git history/reachable
work, local tickets, source identity/coverage, review evidence, unresolved work,
and instructions sufficient for another chat to resume. Exclude build caches,
credentials, and downloaded research copies. Verify archive integrity and a
restore smoke check. Upload and expose each completed archive immediately.

## Starting state

Fresh clone on master, HEAD as above, clean index and working tree, no relevant
untracked files and no pre-existing user edits. All task changes belong to this
request. No content exclusions from the source review baseline.

