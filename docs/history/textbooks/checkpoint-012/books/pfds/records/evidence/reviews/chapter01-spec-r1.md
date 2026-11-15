# Chapter 1 — independent Spec review, round 1

Date: 2026-11-02.
Reviewer: `/root/architecture_inventory/chapter01_spec`.

- Base and supplied merge base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate: `99340c79b9123e64f4b5cea313a8dbdf00af740c`.
- Read-only isolated checkout: `/workspace/scratch/ca9a61d0bf30/review-ch01`.
- Scope: `git diff BASE...CANDIDATE`; only `docs/SOURCES.md` and
  `docs/research/pfds-reconstruction.md`. No exclusions.
- Requirements: `session/requirements/REQUEST.md` and `chapter01.md`, version 1.
- Outcome: **Findings-present**. Two unresolved findings; worst severity medium.

## Assessment

The candidate accounts for all five named sections of the supplied introduction
and correctly classifies the chapter as exposition. I read the OCR of all five
available printed pages and visually inspected the final page to confirm the
roadmap's concluding paragraph. No numbered theorem, exercise, algorithm or code
listing appears in those pages. It would add no mathematical value to invent
Lean declarations merely to restate this vocabulary.

The source register preserves the book/dissertation distinction, identifies the
publisher excerpt's actual page range, and provides source fingerprints. The
candidate correctly retains later chapter, exercise, sharing, complexity and
scheduling obligations, and does not claim that a compilation, audit or proof
of those obligations occurred. The statements about the inspected current
`AbstractFIFO`, `Measured`, `Workload` and generic `Durability.Heap` interfaces
agree with their definitions. Existing FIFO behavior is explicitly not treated
as proof of stacks or branching amortization.

The two issues below concern precise source-coverage and terminology accounting,
which are the substance of this documentation-only acceptance scope.

## CH01-SPEC-001 — State the omitted-page inference explicitly

- Severity: **medium**.
- Status: **unresolved**.
- Candidate location: `docs/research/pfds-reconstruction.md`, Chapter 1 opening
  paragraph, lines 32–35.
- Requirement: `chapter01.md` requires exact primary source extent and accounting
  for the entire substantive chapter; `REQUEST.md` forbids claiming exhaustive
  coverage without reading the chapter and treats missing source as a pending gate.
- Evidence: The paragraph calls the inspected pages the “complete substantive
  introduction” while also reporting the chapter's assigned span as pages 1–6.
  The exact excerpt contains pages 1–5, then begins Chapter 2 on page 7. Printed
  page 6 was not supplied or inspected. The end of page 5 is strong evidence for
  an ended roadmap, but it does not amount to direct inspection of page 6.
- Consequence: An unqualified completeness statement currently hides the only
  inference in the source-coverage gate, and could be reused as evidence that
  every assigned page was actually examined.
- Remedy: State plainly that page 6 is omitted and uninspected. Either obtain
  primary evidence resolving its content, or document the inference from the
  ended roadmap and publisher omission as an inference, with an explicit
  disposition of the remaining source-coverage limitation before chapter
  acceptance. Do not describe an unseen blank page as inspected evidence. A
  report limited to the five inspected sections is supportable immediately.

## CH01-SPEC-002 — Complete the section 1.3 terminology mapping

- Severity: **low**.
- Status: **unresolved**.
- Candidate location: `docs/research/pfds-reconstruction.md`, section 1.3 row,
  line 41, and explanatory interface paragraph at lines 45–53.
- Requirement: `chapter01.md` requires all five source sections to be mapped to
  project distinctions; source vocabulary is the principal content of this
  chapter's non-formal accounting.
- Evidence: Printed page 4 concludes section 1.3 by distinguishing a function
  supplied by an abstract interface from an application of that function. The
  source reserves “operation” for an application and “function” or “operator”
  for the function itself. The candidate does not record that distinction and
  uses the repository's operation-record vocabulary without explaining the
  difference. Also, its row substitutes a caution about pointer identity for
  the source's *persistent identity*: the identity shared by successive versions
  of one logical structure need not be the address of any version/root/cell.
- Consequence: The source's meaning of a counted operation can be confused with
  the project interface's field/function, and logical version lineage can be
  confused with modeled address identity in subsequent sharing developments.
- Remedy: Add a short mapping that retains ordinary project vocabulary while
  distinguishing interface function from operation invocation. Explicitly say
  persistent identity is logical identity across versions, distinct from the
  root/cell identity used to model sharing. No new theorem, class or global
  glossary change is needed.

## Validation and limitations

The coordinator supplied successful exact-candidate clean-identity, whitespace
and eleven local Markdown-link checks under the real Nix shell. I reuse that
mechanical evidence; it does not establish the semantic/source judgments above.
No Lean source or configuration changes exist in this candidate, so no new
integrated build/audit result is claimed or needed for this document-only review.

Primary inspection was bounded to the publisher's available introduction,
printed pages 1–5. Page 6 remains uninspected; that limitation is the subject of
CH01-SPEC-001. Future technical chapters have not been accepted by this review.

**Spec result:** Findings-present; base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, candidate
`99340c79b9123e64f4b5cea313a8dbdf00af740c`; 2 unresolved findings, worst medium.
