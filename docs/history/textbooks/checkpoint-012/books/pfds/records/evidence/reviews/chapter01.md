# Chapter 1 implementation/review loop

Requirements: `../requirements/chapter01.md`, version 1, together with original
`../requirements/REQUEST.md`. No unrelated user work or exclusions.

## Round 1

- Base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `99340c79b9123e64f4b5cea313a8dbdf00af740c`.
- Confirmed merge-base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Review command: `git diff 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd...99340c79b9123e64f4b5cea313a8dbdf00af740c`.
- Commit list: `99340c7 docs(pfds): establish source scope and introductory contracts (#10001)`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/review-ch01`.
- Source files: `docs/SOURCES.md`, `docs/research/pfds-reconstruction.md`.
- `git diff --check`: passed in implementation checkout before commit.
- No Lean/configuration changes; no integrated build/audit asserted.
- Source and documentation checks in isolated checkout: exact-candidate clean identity, whitespace and eleven local Markdown links passed under the real Nix shell. Handoff command/result evidence is preserved in `chapter01-validation-r1.txt`; reviews reuse it and do not claim a Lean build/audit.
- Requirements fingerprints: `REQUEST.md` SHA-256 `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499`; `chapter01.md` v1 SHA-256 `21a48584591c2448fc1fdf2580fad081c17a3d9a4957a30a34f62d589f7779e4`.
- Standards: **Findings-present**, one unresolved medium finding. Independent reviewer `/root/architecture_inventory/chapter01_standards`; full report `chapter01-standards-r1.md`.
- Spec: **Findings-present**, two unresolved findings, worst medium. Independent reviewer `/root/architecture_inventory/chapter01_spec`; full report `chapter01-spec-r1.md`.

Findings remain in separate axes with stable identifiers through corrections.

## Standards findings

### CH01-STD-001 — Qualify completeness inferred from the excerpt

- Severity: medium. Round-1 status: unresolved. Current status: **fixed with round-2 review evidence** in candidate `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; see `chapter01-standards-r2.md`.
- Candidate location: `docs/research/pfds-reconstruction.md`, lines 32–34.
- Inspected pages 1–5 are described as the complete substantive introduction, while omitted page 6 has not been inspected. Exact source-coverage assertions must distinguish primary inspection from inference.
- Required correction: identify page 6 as omitted/uninspected and qualify the absence/completeness assertion, or obtain corroborating primary evidence. Do not claim inspection of an unseen blank page.
- Reviewer independently matched all three PDF SHA-256 fingerprints. Other inspected architectural and source-accounting distinctions passed.

## Spec findings

### CH01-SPEC-001 — State the omitted-page inference explicitly

- Severity: medium. Current status: **resolved with round-3 primary-source evidence**; see `chapter01-spec-r3.md`. Round 2 fixed the wording but correctly retained the missing-p6 gate. Round 3 independently inspected the complete book page as blank and closed that evidence limitation; the historical round-2 report remains unchanged.
- Candidate location: `docs/research/pfds-reconstruction.md`, lines 32–35.
- Full substantive Chapter 1 accounting and exact source extent are acceptance requirements. The ended roadmap on p5 and publisher omission support an inference, but do not constitute inspection of p6.
- Required correction: record the omitted/uninspected page and explicitly dispose of the source-coverage limitation before acceptance, or obtain primary evidence. An inspected-five-section report is immediately supportable.

### CH01-SPEC-002 — Complete the section 1.3 terminology mapping

- Severity: low. Round-1 status: unresolved. Current status: **fixed with round-2 review evidence** in candidate `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; see `chapter01-spec-r2.md`.
- Candidate location: `docs/research/pfds-reconstruction.md`, section 1.3 row and interface paragraph (lines 41, 45–53).
- The source distinguishes an interface function/operator from an operation invocation. It also distinguishes logical persistent identity across versions, which is not root/cell/pointer identity. The map omits these distinctions.
- Required correction: briefly map these terms while retaining project vocabulary; no new theorem, class or global glossary change is required.

## Round 1 disposition

Both axes examined the same nonempty immutable candidate. Neither passed.
The coordinator preserves each axis's report and finding identifiers without
combining their outcomes. Corrections are assigned to root; a changed candidate
requires both axes to review the full scope against the fixed base again.

## Round 2

- Fixed base and confirmed merge-base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Isolated clean checkout: `/workspace/scratch/ca9a61d0bf30/review-ch01-r2`.
- Full-scope command: `git diff 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd...cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Commits: `99340c7 docs(pfds): establish source scope and introductory contracts (#10001)`; `cbb1e27 docs(pfds): qualify source coverage and persistent identity (#10001)`.
- Same two documentation files; no exclusions or Lean/configuration changes.
- Requirements remain `REQUEST.md` and `chapter01.md` version 1, with the round-1 fingerprints. The candidate field in the saved v1 requirements identifies its original capture; the acceptance scope is unchanged.
- Nix validation: exact clean candidate identity, whitespace, eleven local Markdown links passed; output `chapter01-validation-r2.txt`. No integrated build/audit claimed.
- Corrections supplied: distinguish inspected pp1–5 from omitted/uninspected p6, label blank-page conclusion as inference, leave chapter acceptance pending, map operator/invocation and logical persistent identity/root-cell identity separately.
- Source-completeness gate remains unsatisfied under unchanged requirements. Local ticket #10001 is blocked. Correcting the documentation does not remove that blocker.
- Standards and Spec reviewers reused for full-scope review; full reports `chapter01-standards-r2.md` and `chapter01-spec-r2.md`.
- Standards: **Blocked** by required source evidence; zero unresolved code/prose findings. CH01-STD-001 fixed.
- Spec: **Blocked** by required source completeness; CH01-SPEC-001 remains unresolved as an evidence/completion gate (medium), not a defect in the corrected prose; CH01-SPEC-002 fixed. No new findings.

## Round 2 disposition (historical)

Both independent axes reviewed the same exact correction candidate. The
documentation changes accurately preserve the inspected work and its limits,
and all prose corrections are verified. Neither axis supplies chapter acceptance:
printed p6 remains unavailable and uninspected under unchanged whole-chapter
requirements. No later chapter implementation frontier is unlocked. The bounded
cross-cutting persistence prerequisite may proceed under the user's exception,
with its own requirements and review/validation gates.

To resolve this loop, obtain the missing page or equivalent authoritative
evidence, account for any content, capture a candidate, validate applicable
changes and return it to both reviewers with the stable finding record.

## Round 3: complete sources and expanded union scope

- Fixed original base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `1ce161412a2cfb725f27525ff98d400209163316`.
- Implementation branch/worktree: `pfds/ch01-union`, `chapter01-union`, descended
  from the prior Chapter1 candidate cbb1e27.
- Isolated validation/review checkout: `review-ch01-r3`, clean at the candidate.
- Requirements: `requirements/REQUEST-union-v2.md`, its original `REQUEST.md`,
  and `requirements/chapter01-union-v2.md`. The user's new source-union scope
  is the reason for the new spec version; prior findings remain in this record.
- Complete original-base diff has three documentation files only:
  docs/SOURCES.md, docs/research/pfds-reconstruction.md,
  docs/research/pfds-union-coverage.md. No formal/code/config/dependency changes.
- Independent formal ticket10013 is excluded by branch ancestry: it is not
  present in this doc-only candidate. Its proof acceptance is still pending.
- Evidence: source-identity JSON, book-full-inventory.md, book-thesis-union.md,
  thesis-obligations.json, book-exercise-index.json, original PDFs outside
  checkpoint payloads, and visually inspected page renders.
- Both source introductions fully inspected; bookp6 visually blank; thesissp6
  is substantive. Sixteen table rows retain later proof owners and unproved
  status, and eight known variants/supplements are recorded as pending.
- Validation under pinned Nix: `python3 session/validation/check-ch01-union.py`
  from the isolated checkout (absolute script path used). Result is in
  chapter01-validation-r3.txt. No Lean build/audit is claimed for this scope.
- Standards and Spec: **Passed** on the same round-3 candidate, with zero unresolved findings in each axis. Complete reports: `chapter01-standards-r3.md` and `chapter01-spec-r3.md`.

After approval, integrate only identical reviewed documentation blobs into the
main branch. Record scoped blob equality and the unrelated10013 source exclusion.
Any conflict/content change needs renewed review. Source-ledger acceptance is
not acceptance of summary bounds or the full union.
- Requirement fingerprint `requirements/REQUEST-union-v2.md`: `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c`.
- Requirement fingerprint `requirements/chapter01-union-v2.md`: `635724779ed3ea1d5ffd9779df943c1ce9e30ba5cf43a82024c3feb80fea1741`.

### Round 3 independent review dispatch

Replacement coordinator: `/root/chapter01_review`, following the existing loop
and `.agents/skills/code-review/SKILL.md`; no new implementation loop is created.
Confirmed clean isolated candidate, matching original merge-base, nonempty
three-file documentation diff, and commit list:

- `99340c7 docs(pfds): establish source scope and introductory contracts (#10001)`
- `cbb1e27 docs(pfds): qualify source coverage and persistent identity (#10001)`
- `1ce1614 docs(pfds): account for book and thesis union (#10001)`

The axes were dispatched independently and concurrently:

- Standards: `/root/chapter01_review/standards`; report
  `chapter01-standards-r3.md`.
- Spec: `/root/chapter01_review/spec`; report `chapter01-spec-r3.md`.

Both receive the complete original-base scope, version2 requirements, primary
source locations, prior findings and matching document-validation evidence.
The mechanical table check establishes agreement with the inspected source
inventory; source correctness and acceptance interpretation remain review work.
The coordinator reconciles the two reports and does not supply a third review.
Current round3 outcome: **Passed** on both axes; final reports and scope limits below.

### Round 3 Standards outcome

**Passed; 0 unresolved findings; worst severity none.** Complete independent
report: `chapter01-standards-r3.md`, reviewer
`/root/chapter01_review/standards`. CH01-STD-001 remains fixed and its former
primary-source evidence limitation is resolved. The reviewer independently
viewed the blank book page and thesis table, checked all sixteen row/mode
distinctions, and reviewed the complete original-base documentation scope.
No new Standard or heuristic finding was allocated. Matching pinned-Nix
document checks were reused with their stated limits.

### Round 3 Spec outcome

**Passed; 0 unresolved findings; worst severity none.** Complete independent
report: `chapter01-spec-r3.md`, reviewer `/root/chapter01_review/spec`.
CH01-SPEC-001 is resolved with the complete primary source; CH01-SPEC-002
remains fixed. The reviewer read both complete introductions, checked all
sixteen table rows against the rendered primary source, inspected the
consequential claims of all eight known supplements against primary passages,
and checked cited unchanged interfaces. No new Spec finding was allocated.
The review explicitly assessed the original chapter-order and whole-union
requirements rather than treating the bounded spec as permission to omit them.

### Joint round 3 disposition and remaining integration condition

Both axes approve introductory source accounting for candidate
`1ce161412a2cfb725f27525ff98d400209163316` against original base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. This resolves the former source
blocker and permits the primary book frontier to move to Chapter2 once the
caller accepts the reviewed documentation. It does not prove thesis Table1.1,
any later algorithm/cost result, formal ticket10013, or the whole union.
All forward contracts remain pending with their later owners. No Lean build
or axiom audit is asserted for this documentation-only candidate.

The caller still owns final scoped integration verification. For integration
onto the main branch containing unrelated formal work, retain these exact
reviewed blobs and record the actual integration commit plus equality evidence:

| Reviewed file | Git blob |
| --- | --- |
| `docs/SOURCES.md` | `916998a8f67418771229032d60a65ead14a3ae8b` |
| `docs/research/pfds-reconstruction.md` | `8db3de78ee35b13ce93d5c84ca3d1d790b81acd8` |
| `docs/research/pfds-union-coverage.md` | `a0d7d93378ced2a9957933d572d3571a0423e7ad` |

The unrelated10013 formal changes are explicitly excluded from this approval.
Any changed task-file content or conflict resolution requires renewed review;
this is not advance approval of an arbitrary future integration commit.
Both reports and this coordinator record are complete and stable for capture.

## Delivered scoped integration

Integration commit `82501d108f33c62d21b5e0d0f7d2376b902d8d49` cherry-picks the approved documentation onto the local branch at70a1477 without conflict. All three delivered task-file blobs exactly match the reviewed identities; clean status and the explicit unrelated formal exclusion are recorded in `chapter01-integration-r3.json`. Both review outcomes therefore apply to the delivered introductory source-accounting content. Ticket10001 is accepted for that scope, with all forward costs still unproved.
