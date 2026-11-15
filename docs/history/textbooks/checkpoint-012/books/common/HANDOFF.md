# VFA, FDSA and PFDS: receiving handoff

This package delivers the current combined `conaled` source and its preserved
mathematical work for integration. **The source handoff is ready for receiving
work; final library acceptance remains conditional on the receiving build,
axiom audit and reviews.** No further local build retry is assigned to the
checkpoint-producing session. Current review outcomes are in `REVIEW.json`.

**After a wiped workspace or missing authoritative input, explicitly ask the
user for the latest checkpoint archive and wait for it before project work,
cleanup, setup or delegation.** Verify and restore the supplied archive first.
An old chat summary, process handle, patch alone or remembered source location
does not replace the archive. `docs/DURABILITY.md` owns this rule.

## What is being delivered

| Item | Purpose |
| --- | --- |
| `conaled-textbooks-012.tar.xz` | Complete source history, active candidate, useful deferred Lean and paper mathematics, local issues, review evidence, setup and recovery instructions. No earlier archive is required. |
| `conaled-textbooks-012.patch` | Convenient active-source delta against the exact upstream pin below. It can be regenerated from the checkpoint; it is not a separate recovery dependency. |
| `conaled-textbooks-012-handoff.md` | A convenient copy of this entrypoint. The copy inside the checkpoint is authoritative for this release. |

The patch is a byte-identical re-export of the earlier 009 patch. It contains
360 changed paths and is 3,544,383 bytes, SHA-256
`955c71b607aab9e217f1b0e4b9c1ef476f16a4596e9d47192052acc8f8a88498`.
A fresh private-index application reconstructed the exact candidate tree;
`evidence/patch-export-012.json` owns the recipe and result. Patch application
is a source check, not a Lean build or a proof audit.

Keep the complete checkpoint when receiving the patch. The patch contains the
active library delta; useful deferred work, alternate developments, provenance
and local review state also live in the preserved refs and checkpoint records.
The fresh preservation check found all 155 catalog refs and all 167 recorded
donor/draft identities intact. `evidence/handoff-source-check-012.json` records
the exact scope and limitations; no new large inventory was added.

## Exact source identities

| Role | Commit or tree |
| --- | --- |
| Pinned upstream incorporated by the patch | `04514fc144dcebdd2b6d4aea5faf2f9cbf229362` |
| Combined candidate | `18235331da1fe343d09080ca4c41173f9b4d9963` |
| Candidate tree | `63205d8a3ff27deb3680c613b70085163f289b83` |
| Fixed original full-spec review base | `9175737c2b14ef738cfb6c2cdc68d885c0805ddd` |

`source/integration.json` at the checkpoint root owns these identities and the
stored restore refs. All three nominated incoming textbook tips are ancestors
of the combined candidate. Its source is unchanged from 011. All 9,178 tracked
entry modes and object IDs match the retained complete R4 snapshot receipt;
`evidence/recovered-candidate-012.json` records the fresh recovery comparison.
The upstream pin is the last incorporated pin, not a claim about today's remote
HEAD. No new remote lookup or incorporation was performed during this packaging.

Do not move the original full-spec review base when incorporating later upstream
work. If receiving `master` has advanced, record its exact commit and assess
the change under its actual applicable instructions. Any conflict resolution,
source change, rebase or new receiving commit requires the corresponding
candidate capture, applicable validation and review in the same integration
loop. Retain all previous findings and the full original requirements.

## Start here in the receiving environment

1. Read the checkpoint root `README.md`, `AGENTS.md` and `docs/DURABILITY.md`.
   Follow their integrity and offline restoration procedure. The checkpoint
   tool restores source with Python and Git; Lean installation is not a
   prerequisite for source recovery. After a fresh restore, the default
   `worktrees/vfa` holds the **combined candidate**, while `fdsa` and `pfds`
   preserve the original input views. Select current work through
   `source/integration.json`, not by guessing from the directory name.

2. Read this directory's `REQUIREMENTS.md`, `STATUS.md`, `ISSUES.json` and
   `REVIEW.json`. These are the current task, evidence and local tracking owners.
   The original full requirements and historical review reports remain retained.
   Old absolute workspace paths identify historical observations; they are not
   instructions to recreate that machine layout or resume old process handles.

3. Read the restored candidate's actual `AGENTS.md`, development and build
   sections in `README.md`, `.agents/skills/implement/SKILL.md` and
   `docs/agents/review-loop.md`. Follow its domain/architecture guidance and
   applicable skills for any code changes, including statement review and
   example-driven development for changed mathematical claims. Continue the
   existing Standards/Spec review loop and stable finding record; replace
   unavailable agents by handing over their records, not by resetting findings.

4. Use a clean, isolated checkout of the actual receiving candidate. Retaining
   the recovered candidate/history is the most direct route. Applying the
   standalone patch to a clean checkout of the exact upstream pin is also
   possible, but committing it creates a new commit identity even if the tree
   is identical. Validate and review the actual receiving commit. Keep the
   full checkpoint for the deferred mathematics and original refs.

5. Read `EXECUTION.md` before any native setup/build example. It is the single
   owner of current resource settings and supersedes frozen one-thread and
   older two/four-thread examples. `docs/RESUME.md` owns setup, with that explicit
   override. Nix is optional under the user's instruction; the prescribed
   pinned compiler, dependencies and supporting inputs remain mandatory.
   Keep setup to the documented ten-minute budget, one route and at most one
   concrete retry. Setup must not consume the mathematical task.

6. Execute the exact receiving gate in `VALIDATION-HANDOFF.md`. It owns the
   full build/audit, final independent reviews, immediate verification and
   official snapshot comparison procedure. The receiver owns troubleshooting
   of any failed gate in its normal development environment. No publication,
   GitHub issue/comment operation or merge is authorized by this handoff alone.

The archive contains the Git objects needed to regenerate the patch offline.
In a restored checkout containing the recorded commits, use:

```sh
git diff --binary --full-index \
  04514fc144dcebdd2b6d4aea5faf2f9cbf229362 \
  18235331da1fe343d09080ca4c41173f9b4d9963 -- \
  > /absolute/output/conaled-textbooks-012.patch
```

Compare its byte count and SHA-256 with `evidence/patch-export-012.json`. The
output directory must be outside the source checkout and checkpoint payload.

## Integration and mathematical coverage

The public integration connects four concerns through existing library owners:
Potential accounting, sorting, sequence representations and OrderedMap
observations/validity. The clients `Examples.MappedPotentialAccounting`,
`Examples.TextbookSorting`, `Examples.TextbookSequences` and
`Examples.TextbookMaps` are publicly imported and compiled in the recorded first
full attempt. `STATUS.md` explains the actual proved relationships and their
boundaries. There is no blanket cost equivalence or stability claim beyond
those explicit contracts.

`COVERAGE.md` is the detailed coverage owner. Its principal boundaries are:

| Book | Established account | Remaining boundary |
| --- | --- | --- |
| FDSA | Chapters 1–3 have historical formalization/acceptance; Chapter 2 records 112/112 obligations and Chapter 3 83/83. | Chapter 4 streams and later chapter work remain explicitly staged or pending; the current whole-candidate gate is open. |
| VFA | Perm is implemented; five staged developments have historical focused-check evidence, and the table slice is partly received. | Staged work is not equivalent to accepted whole chapters; four other developments remain outside the active library. |
| PFDS | Chapter 2 code covers all six exercise headings; 35 distinct Lean paths support the B2 ledger. Eight formal scopes include later resource foundations. | Later exercise coverage remains partial; 77 later exercise headings are unproved in the recorded mapping. |

These are heterogeneous coverage facts, not percentages of each whole book.
Historical chapter acceptance, current source implementation, focused
compilation, paper development and integrated acceptance remain distinct.

For deferred mathematics, use `analysis/donor-dispositions.json` and the local
issues, then the exact preserved sources they identify. The proposed next
bounded slices are the weaker total-table contract, VFA sorting-specification
bridges, measured tree folds, and one finite tape-to-PMF selection step. Their
scope and architectural owners are in `analysis/consolidation-next-20261114.md`.
They are subsequent work, not missing premises secretly required by the current
public APIs. Do not expand them before receiving this coherent slice merely
to make whole-book coverage look larger.

## Validation evidence and open gates

The first unrestricted full attempt has complete retained terminal evidence:
checker exit 1 after 1h40m19s, eight compiler jobs exiting 137 and 3,174 successful
Built lines, including all four public integration clients. The exhaustive
axiom audit was not reached and no candidate verification record was produced.
`evidence/full-validation-r5-summary.json` and its linked original log/receipts
own those facts. This is useful compilation evidence, not whole-library success.

The one unchanged incremental retry started after durable 011. The last reported
observation showed 74 Built lines and five repeated 137 results; three previously
failing modules had compiled. The retry's raw files were lost with the workspace,
and no terminal result was recovered. The newly written
`evidence/retry-r5-reported-observations.json` is expressly a summary of retained
conversation/tool observations. It must never be presented as an original log
or terminal receipt. Neither run establishes an OOM, supervisor or timeout
diagnosis. The user's cited interruption experience occurred on their PC and
supports considering process/session lifetime, not a specifically cloud cause.

**INT-090 and INT-SP-001 remain open receiving gates.** Required completion is
the full guarded build and exhaustive allowed-axiom audit on the actual candidate,
the matching success record, both final review approvals, immediate candidate
verification, and the official snapshot comparison. Old review-helper retention
paths are historical: capture/validate receipts for the actual receiving
checkout before its final comparison. Reuse matching source analysis where the
review procedure permits; never relabel a blocked historical review as passed.

## Preserve these constraints in successors

- Keep useful deferred Lean, paper mathematics, counterexamples, evidence and
  exact source pointers. Do not delete a donor merely because it is not imported.
- Do not weaken mathematical statements, add admissions/application axioms,
  narrow integrated public coverage, alter proof policy or change dependency
  pins to make a check pass. Required source corrections return through the
  existing review loop.
- Keep the protected checkpoint contract, tools, frozen documentation and
  native kit intact. Mutable current instructions explicitly override dated
  operational examples where already authorized. Do not edit policy hashes to
  bypass packaging checks. Historical proposal patches are for reconstruction
  in a temporary directory, not current instructions.
- Keep issue/spec tracking local and checkpointed. Preserve serial numbering,
  self-contained recovery and one source of truth per concern. Do not package
  earlier checkpoint archives, download fragments, installed runtimes, caches
  or a fresh giant inventory for every serial. The source bundle owns history;
  the standalone patch is regenerable and is intentionally outside the archive.
- A checkpoint is complete only after its integrity/offline recovery checks
  **and an observed successful `create_library_file` upload to the owner's root
  with `directory_id` omitted**. Record the actual returned identity. A download
  link or successful local pack alone is insufficient. If this upload route is
  unavailable, fails or has an uncertain result, tell the user promptly and
  stop further project work. Do not claim durable delivery from a prepared file.

`docs/CHECKPOINTS.md` owns packaging and upload bookkeeping. The receipt for a
release follows the immutable archive; it need not be packed into itself. A
reattached verified archive is sufficient recovery input without an old sidecar.
