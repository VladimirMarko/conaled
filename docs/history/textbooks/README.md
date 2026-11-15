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

## Issue references

Use [qualified issue references](issue-lineages.md) and the
[normalized imported history](commit-references.md) to distinguish VFA, PFDS,
FDSA and intake tickets from real GitHub issues. Bare numbers never determine
a lineage, and GitHub has no reserved numeric ranges.

## Source recovery

The [original ref catalog](checkpoint-012/source/refs.json) and
[delivered identities](checkpoint-012/source/integration.json) identify the full
source history. Commit messages in the receiving history now use short book
IDs. Every rewritten commit retains its original tree, author, committer and
timestamps, with parents mapped to their rewritten counterparts. This includes
the ancestry carrier recorded in [history.json](history.json), which retains
all donor source trees without selecting them for the active library.

[commit-rewrite.json](commit-rewrite.json) records every old/new identity and
the original raw commit bytes. In an ordinary full clone, restore the original
objects before using original IDs from proof receipts or donor ledgers:

```sh
direnv exec . python3 scripts/restore-textbook-commits.py --write
git show COMMIT:PATH
```

Without `--write`, the script verifies original hashes, unchanged trees,
metadata and mapped parent topology. Restoration writes only Git objects and
leaves all refs unchanged. Restored objects are unreferenced and can be removed
by Git garbage collection; rerun the command when needed. The checked-in
registry and source trees retain the recovery material. A shallow clone must
fetch full history first. Original local convenience refs remain under
`refs/textbooks/012/`; they are not needed for recovery from a full clone.
The carrier preserves history, not mathematical acceptance of its parents.

The original archive and 99 MB source bundle are not tracked. Git owns source trees and the registry retains original commit objects; [preservation.json](preservation.json) records the input digest and omitted
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
