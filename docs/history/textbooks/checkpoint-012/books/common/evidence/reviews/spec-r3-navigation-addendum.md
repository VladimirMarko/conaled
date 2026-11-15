# Spec round 3 — recovery evidence navigation addendum

**No new Spec finding. The final navigation text correctly identifies the retained evidence and consolidation boundaries. Overall Spec remains Blocked by INT-SP-001; this addendum grants no final approval.**

Reviewer: `/root/recovery_review/spec`, 14 November 2026. This is a narrow continuation of the existing ordinary review loop, not a repeated source review. The original full-spec base remains `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`; the formal candidate remains `16440863ddb14d95c402ce65498e22497e246e72`. Requirements SHA-256 remains `5d48738af724152b67daf993fa0f3d2abd7c2eeb7a47b7e080aa7740de1e07ac`. The earlier Spec reports are unchanged.

## Reviewed navigation identity

The reviewed `books/common/README.md` is **3,834 bytes**, SHA-256 **`652bd813c42775e89ffd7030b7e5af9c26f249a4e6eea146404fb08194556fe3`**. The assessment covers its “Reading retained evidence after recovery” section, including the final explicit mapping for the historical running validation receipt.

## Verified mappings and limitations

- All **14** retained R1/R2/R3 review files match the corresponding workspace originals byte-for-byte: eight earlier Standards/Spec Markdown/JSON records and six R3 Standards/Spec/coordinator records. Their checkpoint owner is `books/common/evidence/reviews/`.
- `REVIEW.json` correctly distinguishes the historical receipt renames. The original R1 `intake/integration-candidate.json` is retained as `evidence/integration-candidate-r1.json`; original R2 `intake/integration-candidate-r2.json` is retained as `evidence/integration-candidate.json`. The R3 receipt keeps its `integration-candidate-r3.json` name. All three copies match the original bytes and candidate identities. The initial and continuation baselines and continuation scope manifest also match their retained copies.
- The checked map handoff, both correction records, all three focused receipts/logs, interruption record and R3 patch-reconstruction record match their `books/common/evidence/` copies. The named statement-review records are present there. These location mappings do not broaden their validation scope.
- `evidence/coverage-20261114.json` contains the two original accounting JSON objects exactly under `fdsa` and `vfa_pfds`. The prose in `COVERAGE.md` preserves their substantive accounts; its differences are heading levels, references to the consolidated structured evidence, and closing operational-wrapper notes. It is deliberately not a byte-identical copy of each temporary Markdown report. The raw temporary report paths/hashes in older reviews identify what those reviewers inspected, not additional required archives. The consolidated coverage and donor-disposition hashes remain those assessed in the R3 source report.
- Reconstructing commit/path lists from the recorded immutable base and candidate is consistent with the supplied source-history model. Old absolute runtime paths and process handles identify historical execution context; they cannot establish a current process or substitute for required checks after recovery.

Standards discovered the initially absent copy of the fingerprinted running receipt as **INT-ST-002**. Root's correction is independently verified: `evidence/full-validation-r3-start.json` is **1,426 bytes**, SHA-256 **`33951558afb5c06a6d3c33141d6279470eed3263bc5d74dcd87e0c5c92a6c28b`**, and matches the reviewed running record exactly. Its candidate/tree match R3, and `terminal_observed` is false. The README now explicitly reserves `evidence/full-validation-r3.json` for a later terminal receipt and prohibits overwriting or inferring that outcome from the start observation. Standards owns INT-ST-002's disposition; no duplicate Spec identifier is created.

## Unchanged gates and handoff

Root's reported compilation progress remains nonterminal evidence. It does not close INT-SP-001 or any inherited current-validation finding. The full check/audit, matching terminal record, both independent final review outcomes, immediate candidate verification and final snapshot comparison remain required. All earlier source findings, retained fixes, 39 PFDS historical identifiers and deferred mathematical scope keep their existing dispositions.

No compiler, setup, checker, process control, source/Git, checkpoint or remote mutation was performed. This new addendum is the only write. Root owns its inclusion in the next verified durable checkpoint; no upload is asserted here.

**New Spec findings: 0. Final approval: none. Overall Spec outcome: Blocked, INT-SP-001 retained.**
