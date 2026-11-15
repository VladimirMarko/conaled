# Local completed-checkpoint duplicate survey — 4 November 2026

**Contingency inventory only; no cleanup action is selected or authorized.** The 22 completed archives numbered **0083–0104** under `BASE/checkpoints` allocate **373,370,880 bytes (356.07 MiB)**. Every one was freshly read through an `O_NOFOLLOW` leaf descriptor, with matching opened metadata, and its full SHA-256 and size match the archive sidecar, saved upload receipt, saved integrity receipt and exact catalog entry. All are regular single-link files. Their complete paths, hashes, remote file identifiers and evidence hashes are in `receipt.json`.

`BASE` is `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104`. For each row, the exact saved records are `fdsa-control/provenance/checkpointNNNN-preparation/upload.json` and `integrity.json`; catalog source is `fdsa-control/checkpoints.json`. The 0083–0087 catalog entries use nested `metadata` fields and `checkpoint` names; the older schema is reconciled, not absent. These are exact uploaded local duplicates eligible for a later root decision, not a claim that they have been removed or that their space is already available.

| Checkpoint | Filename under `BASE/checkpoints` | Allocated bytes |
|---|---|---:|
| 0083 | `conaled-fdsa-0083-checked-quicksort-and-measured-merge.tar.gz` | 14,503,936 |
| 0084 | `conaled-fdsa-0084-checked-natural-runs-and-top-down-costs.tar.gz` | 14,594,048 |
| 0085 | `conaled-fdsa-0085-checked-sorting-values-and-measured-drafts.tar.gz` | 14,737,408 |
| 0086 | `conaled-fdsa-0086-measured-sorting-and-random-pivot-draft.tar.gz` | 14,917,632 |
| 0087 | `conaled-fdsa-0087-bottom-up-costs-and-natural-sort-draft.tar.gz` | 15,159,296 |
| 0088 | `conaled-fdsa-0088-checked-builders-and-random-pivot-laws.tar.gz` | 15,368,192 |
| 0089 | `conaled-fdsa-0089-probability-minima-and-mean-uniqueness-drafts.tar.gz` | 15,618,048 |
| 0090 | `conaled-fdsa-0090-checked-uniqueness-and-operational-mean-continuation.tar.gz` | 15,892,480 |
| 0091 | `conaled-fdsa-0091-mean-builds-and-rank-numerical-drafts.tar.gz` | 16,080,896 |
| 0092 | `conaled-fdsa-0092-actual-mean-drafts-and-preserved-compiler-findings.tar.gz` | 16,293,888 |
| 0093 | `conaled-fdsa-0093-complete-sorting-correspondence-and-independent-source-reviews.tar.gz` | 16,494,592 |
| 0094 | `conaled-fdsa-0094-integrated-sorting-source-and-complete-type-inventory.tar.gz` | 16,949,248 |
| 0095 | `conaled-fdsa-0095-reviewed-sorting-repairs-and-qualified-type-inventory.tar.gz` | 17,403,904 |
| 0096 | `conaled-fdsa-0096-checked-tail-boundary-and-preserved-review-continuations.tar.gz` | 17,698,816 |
| 0097 | `conaled-fdsa-0097-checked-tail-examples-and-uniform-repair-handoff.tar.gz` | 17,915,904 |
| 0098 | `conaled-fdsa-0098-checked-uniform-examples-and-secured-type-output.tar.gz` | 18,354,176 |
| 0099 | `conaled-fdsa-0099-complete-sorting-type-reviews.tar.gz` | 18,595,840 |
| 0100 | `conaled-fdsa-0100-checked-potential-accounting.tar.gz` | 19,070,976 |
| 0101 | `conaled-fdsa-0101-verified-output-retirement-preparation.tar.gz` | 19,185,664 |
| 0102 | `conaled-fdsa-0102-retired-cache-and-shared-acceptance-preparation.tar.gz` | 19,320,832 |
| 0103 | `conaled-fdsa-0103-reviewed-shared-source-and-idle-cache-plan.tar.gz` | 19,554,304 |
| 0104 | `conaled-fdsa-0104-persistent-idle-retirement-and-foundation-closure.tar.gz` | 19,660,800 |

## Recovery and exclusions

The 0105 archive was freshly hash-matched to its catalog/upload/integrity identity, and its embedded `RECOVER.md` was read completely: it expressly requires no earlier task checkpoint or conversation and preserves the full source/history/control/kit recovery payload. That file is 1,833 bytes, SHA-256 `1558d20c38659709e54ec12dc19fb4fb96167ec434e45cdca5d14d04cb204034`. The archive has no nested earlier checkpoint archive; the sole nested `.tar.gz` is the deliberately preserved AFP primary-source archive under `provenance/xd01-primary-source-20261104/`. Removing only these 22 local duplicate archive files would not introduce a dependency into current standalone recovery. Their durable copies and all local sidecars, upload/integrity records, catalog/history and unique control evidence must remain preserved. No remote re-download was performed in this survey.

Retain both 0082 originals (109,531,136 allocated bytes combined), current 0105 and newly exposed 0106. The original uploaded 0081 archive under `upload/` is also retained (13,955,072 allocated bytes). All 25 local completed archives through 0105 together allocate 502,706,176 bytes; the proposed inventory excludes 129,335,296 bytes for both 0082 originals and 0105. 0106 was excluded from all archive/output/staging inspection while active and remains excluded from payload inspection after release.

The bounded top-level workspace and `upload/` listing found only that original 0081 input, not another eligible generated archive copy. `library-transfer-current/` contained two transfer helper scripts, no checkpoint payload. The existing `recovery-input-0081` extraction, `recovery-run-20261104` restore evidence and previously retired 0082 test tree are excluded; no contents were traversed for cleanup. No active or uncertain staging directory was inspected. No broader absence claim is made.

This survey read no live F outputs, project caches, compiler/runtime payloads, source worktree state or outside-workspace files, and performed no compiler or process action. It changed only this new two-file control package after the 0106 write hold was released. The prior incorporation/cache-survey package was hash-verified unchanged. Any later root action needs its own immediate exact-path/no-follow/metadata checks and separate persistence observation; this inventory is not an executable mutation guard. The potential reclaim is limited and does not explain or predict backing-filesystem availability.

Root subsequently reported 3,509,891,072 available bytes at 13:12:29 UTC without new cleanup. This rebound does not establish a cause or sustained capacity; the live F run remains untouched.
