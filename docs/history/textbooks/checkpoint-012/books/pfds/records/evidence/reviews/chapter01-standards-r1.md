# Chapter 1 — Standards review, round 1

Outcome: **Findings-present**. One unresolved finding; worst severity: medium.

## Pinned scope

- Base and merge base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `99340c79b9123e64f4b5cea313a8dbdf00af740c`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/review-ch01`.
- Diff: `git diff 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd...99340c79b9123e64f4b5cea313a8dbdf00af740c`.
- Commit: `99340c7 docs(pfds): establish source scope and introductory contracts (#10001)`.
- Scope: `docs/SOURCES.md` and `docs/research/pfds-reconstruction.md`; no exclusions.
- Requirements: `session/requirements/REQUEST.md` and `chapter01.md`, version 1.

Reviewed AGENTS, architectural/domain guidance, glossary, ADR 0001/0010,
README validation policy, review heuristics, the changed documents, source
inventory and relevant unchanged declarations. No nested implementation or
review workflow was started. No source mutations were made.

## Finding

### CH01-STD-001 — Qualify completeness inferred from an excerpt

- Severity: **medium**.
- Status: **unresolved**.
- Candidate location: `docs/research/pfds-reconstruction.md`, lines 32–34.
- Evidence: the document describes printed pages 1–5 as the “complete
  substantive introduction” and then states that the chapter contains no
  numbered theorem, exercise, algorithm or code listing. The source register
  correctly identifies the ten-page publisher excerpt as printed pages 1–5
  and 7–11. The supplied source evidence and reviewer handoff establish that
  printed page 6 has not been inspected; its being blank is an inference.
- Applicable standard: the architectural standard requires verifying source
  claims against primary sources and distinguishing implemented/inspected
  scope from unresolved scope; the glossary makes parity relative to explicit
  scope and reference. The candidate's own source-ledger rule likewise
  distinguishes inspected source from anticipated material. The task's saved
  requirements require exact source extent before exhaustive coverage claims.
- Consequence: the provenance record presently turns a plausible completeness
  inference into an inspection fact. That weakens the source-coverage gate
  used to advance the sequential chapter frontier.
- Remedy: explicitly identify pages 1–5 as inspected and page 6 as omitted
  and uninspected; label any conclusion that page 6 has no substantive content
  as an inference. Alternatively obtain primary evidence for page 6 before
  claiming full inspected coverage. Keep the absence-of-theorems statement
  scoped to inspected text until the coverage conclusion is justified.

This finding does not assert that page 6 contains missing content. It concerns
the distinction between direct evidence and inference.

## Other standards observations

The candidate otherwise respects the repository's architectural direction:
existing operation/simulation, square, list and resource interfaces are reused;
no mandatory container hierarchy is introduced; source semantics, invariants,
costs, sharing and actual runtime claims remain distinct. It correctly avoids
presenting sequential accounting as arbitrary persistent amortization, and
does not conflate persistent values with crash durability.

Chapter-specific state and review records remain outside the source diff;
the user-authorized local tracker exception is stated. The Conventional Commit
format uses the local ticket number. Downloaded manuscripts are not added to
the repository, consistent with ADR 0001. There are no new Lean declarations,
new axioms, build changes or kernel-check claims to audit in this candidate.

No heuristic-only findings were raised.

## Validation and evidence

The root supplied successful clean-candidate identity, whitespace and eleven
local Markdown-link checks for this exact candidate under the real Nix shell.
These artifact-appropriate checks are reused; they were not repeated. The
shared record had not yet been updated from its initial pending placeholder
at review start, so this report records the handoff evidence explicitly.

Independently recomputed source-file SHA-256 values using the local research
PDFs; all match `docs/SOURCES.md`:

| Source | SHA-256 |
| --- | --- |
| Frontmatter | `6fdfe24ac29b98252139a1aa483c1a56fba8f5807545d9ce788dc059c57148cb` |
| Excerpt | `a39a8a3adb7e2d718a1395ad040e84403bf9c2bf669ebe4722aa850bea92f87b` |
| Dissertation | `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072` |

Checked the referenced current declarations for operations/simulation,
measured results, workload execution, fresh heap writes, append copied-cell
counts and append visit counts. Their stated distinctions match the code.
No integrated build or proof audit was run or required for these documentation
changes, and no such result is claimed.

## Result

**Standards: Findings-present, 1 unresolved medium finding** on candidate
`99340c79b9123e64f4b5cea313a8dbdf00af740c`, against fixed base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
