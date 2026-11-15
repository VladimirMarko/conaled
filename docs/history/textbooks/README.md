# Textbook mathematics and receiving provenance

This directory preserves checkpoint 012 of the VFA, FDSA and PFDS workstream.
[Issue #558](https://github.com/VladimirMarko/conaled/issues/558) owns ongoing
coverage and preservation. The [integration account](../../research/textbook-integration.md)
explains the active library contracts and checked clients.

## Finding the mathematics

- [Book coverage](checkpoint-012/books/common/COVERAGE.md) distinguishes integrated
  source, historical checks, paper developments and remaining exercises.
- [Donor dispositions](checkpoint-012/books/common/analysis/donor-dispositions.json)
  identifies deferred Lean capabilities by commit, blob and source path.
- [FDSA](checkpoint-012/books/fdsa/README.md),
  [VFA](checkpoint-012/books/vfa/README.md) and
  [PFDS](checkpoint-012/books/pfds/README.md) lead to the original paper mathematics,
  source correspondence, drafts and evidence. Their `records/` trees are preserved
  byte-for-byte, including counterexamples and unsuccessful investigations.
- [Historical reviews](checkpoint-012/books/common/REVIEW.json) retain finding IDs
  and prior outcomes. Historical blocked reviews remain blocked observations;
  they are not approvals of the receiving candidate.

## Source recovery

The [original ref catalog](checkpoint-012/source/refs.json) and
[delivered identities](checkpoint-012/source/integration.json) identify the full
source history. The receiving integration includes the delivered candidate
`18235331da1fe343d09080ca4c41173f9b4d9963` and the ancestry carrier recorded in
[history.json](history.json). That carrier retains every catalogued donor commit
as an ancestor without selecting its source tree for the active library.
An ordinary full clone therefore retains these objects without fetching custom
refs or recovering the original archive. A shallow clone must fetch full history.

Read a historical file with `git show COMMIT:PATH`, using the exact commit and
source path from the donor ledger. The catalog's original ref names are provenance;
local convenience refs use `refs/textbooks/012/`. The history carrier is preservation
only, not mathematical acceptance of its parents.

The original archive and 99 MB source bundle are not tracked. Git owns restored
history; [preservation.json](preservation.json) records the input digest and omitted
historical setup material. The original manifest is retained as evidence of the
received payload, not as a manifest for this selected repository copy. The archived
checkpoint tool cannot reconstruct omitted packaging material from this directory.

## Current authority and follow-up

Repository AGENTS.md, README, GitHub issues and the receiving review loop govern
current work. All instructions, process handles, host paths, upload requirements,
local-only issue policies and native setup commands inside `checkpoint-012/` are
historical evidence. They do not authorize actions or impose the former session's
workflow. `AGENTS.historical.md` preserves the old instructions without activating
them. Historical links into omitted setup snapshots can be unavailable; mathematical
records and exact Git source identities remain preserved.

The receiving branch was pinned at
`08dbb2a71c8c9236ef2a1283e66f17b5622c3b9e`. Its 18 changed paths since the delivered
upstream pin overlap the active textbook delta only at `SquareApplications.lean`;
the merge retains both import sets. The newer sampler workload and expected-work
contracts require explicit assessment in the sampling follow-up. Toolchain,
dependency pins and proof policy are unchanged.

The original full-spec review base remains
`9175737c2b14ef738cfb6c2cdc68d885c0805ddd`. Final receiving acceptance requires the
exact candidate's full guarded build, exhaustive axiom audit, both independent
reviews, immediate verification and snapshot comparison. INT-SP-001 and INT-090
remain gates until that evidence is recorded; the historical exit-137 runs need
no retrospective diagnosis.

Follow-up owners:

- [#559](https://github.com/VladimirMarko/conaled/issues/559): Connect textbook total tables and remaining map operations to shared contracts.
- [#560](https://github.com/VladimirMarko/conaled/issues/560): Connect VFA sorting specifications to shared sorting and stability contracts.
- [#561](https://github.com/VladimirMarko/conaled/issues/561): Recover deferred FDSA tree and resource capabilities through current library owners.
- [#562](https://github.com/VladimirMarko/conaled/issues/562): Connect FDSA occurrence-index selection to executable tape sampling.
- [#563](https://github.com/VladimirMarko/conaled/issues/563): Integrate preserved VFA positive-key and cost counterexample developments.
- [#564](https://github.com/VladimirMarko/conaled/issues/564): Connect PFDS persistence and suspension costs to library representation choices.
