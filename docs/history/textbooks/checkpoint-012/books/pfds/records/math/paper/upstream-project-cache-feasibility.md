# Public upstream project-output feasibility

Prepared 2026-11-03 by `upstream_cache_feasibility`, with a separate read-only
GitHub access-documentation investigation by `artifact_access`. Public metadata
observations below are dated by the HTTP response `Date` header. This is a
bounded feasibility report, not candidate acceptance, a new implementation or
review loop, or a decision to alter an active validation run.

## Result

**No supported public upstream donor of complete ordinary project Lean output
groups was found.** At 03:31 UTC the public repository reported zero Actions
artifacts, zero Actions caches, and no releases. Its only workflow runs fresh
verification, removes its private project outputs, and has no project-output
publication step. The one recorded successful run at the exact upstream commit
therefore supplies useful run-status evidence but no reusable build archive.

There is no concrete archive whose content inventory, trace completeness,
provenance, or retrieval permissions can be validated. This finding provides
no basis to change the active gate or its scheduling. It does not claim that
the repository never had artifacts, or that inaccessible/deleted resources do
not exist; it establishes the absence of a donor on the inspected current
public CI/cache/release surfaces.

## Inputs and applicable local policy

The investigation read the candidate's `AGENTS.md`, README development and
verification sections, the only tracked workflow, `scripts/check.py`, pinned
configuration, `session/environment/README.md`, and
`session/research/build-cache-recovery-assessment.md`. It searched the saved
environment/research notes for earlier CI/release cache findings before making
the public queries. The saved environment note already establishes a successful
pinned dependency-cache bootstrap; obtaining that dependency cache again is
not a new project-output donor.

The investigated identities are:

| Item | Exact identity |
| --- | --- |
| Initial upstream | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| Active local candidate | `901f734161920a76f3b399a575805b9a1d31e971` |
| Candidate checkout | `/workspace/scratch/ca9a61d0bf30/import-correction-r3` |
| Toolchain | `leanprover/lean4:v4.35.0` |
| Package/library | `compilingWithSquares` 0.2.0 / `SquareApplications` |
| Mathlib input revision | `v4.35.0` |

The candidate's `lake-manifest.json` pins all nine Git dependencies:

| Package | Revision |
| --- | --- |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
| Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

Read-only Git comparisons between the two exact commits showed no differences
in `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, `.github/workflows/fresh-verification.yml`, `check.sh`,
`scripts/check.py`, `scripts/lake_integrity.py`, or
`scripts/lake-output-hashes.lean`. Matching these identities would be necessary
evidence for a donor; it does not make upstream outputs cover the changed local
source graph or establish acceptance of the local candidate.

The README's stock incremental gate rehashes inputs, disables Lake artifact
cache restore/write, checks ordinary outputs against saved traces before and
after the build, and runs the exhaustive audit every time. The candidate must
obtain its own successful full check and immediately matching final
`--verify-candidate` evidence. Its integrity guard provides local consistency,
not proof of artifact derivation or authentication. The existing recovery
assessment already describes private-copy group validation and why copying
from a live donor requires validating the fixed copy rather than relying on
mutable donor bytes.

## Workflow evidence

`git ls-tree` at the exact upstream commit and the candidate workflow inventory
both show only `.github/workflows/fresh-verification.yml`. Its relevant steps
are:

1. Check out the repository with credential persistence disabled.
2. Install Nix using the pinned action.
3. Run `nix develop --command lake exe cache get` for pinned dependencies.
4. Run `nix develop --command ./check.sh --fresh --jobs 2 --candidate HEAD`.
5. Run the verification-command and audit-root regression scripts.
6. Run `nix develop --command ./check.sh --verify-candidate HEAD`.

The workflow contains no `upload-artifact`, `actions/cache`, release creation,
or other project-output export step. It has a 60-minute job limit and runs on
`ubuntu-24.04`; these configuration facts are not predictions of this local
candidate's runtime.

The fresh branch in `scripts/check.py` uses a `TemporaryDirectory` beneath
`.lake`, compiles project modules and the audit there, and leaves that context
before saving the success record. The README explicitly says fresh mode
removes that directory and does not populate the normal incremental cache.
Thus even a successful run of this exact workflow is not a producer of the
ordinary `.lake/build` artifact/trace groups needed for the proposed reuse.

Permanent source references, inspected through the local exact Git objects:

- [Pinned workflow](https://github.com/VladimirMarko/conaled/blob/7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd/.github/workflows/fresh-verification.yml)
- [Pinned verification implementation](https://github.com/VladimirMarko/conaled/blob/7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd/scripts/check.py)
- [Pinned README](https://github.com/VladimirMarko/conaled/blob/7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd/README.md)
- [Pinned dependency manifest](https://github.com/VladimirMarko/conaled/blob/7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd/lake-manifest.json)

## Current public metadata observations

The web reader could not retrieve the repository API/HTML pages. A standard
library HTTPS client then performed only credential-free public metadata GETs,
using `Accept: application/vnd.github+json` and an identifying User-Agent.
The initial sandbox-denied network attempt was followed by an approved network
execution of those exact read-only requests. No authentication headers,
credential lookup, cookie/session reuse, archive request, or remote write was
used. Every successful response below had HTTP status 200 and no `Link`
pagination header.

| Public endpoint | Response date (UTC) | Observed result |
| --- | --- | --- |
| [Repository artifacts](https://api.github.com/repos/VladimirMarko/conaled/actions/artifacts?per_page=100) | 2026-11-03 03:31:19 | `{"total_count":0,"artifacts":[]}` |
| [Releases](https://api.github.com/repos/VladimirMarko/conaled/releases?per_page=100) | 2026-11-03 03:31:19 | `[]` |
| [Workflow runs](https://api.github.com/repos/VladimirMarko/conaled/actions/runs?per_page=5) | 2026-11-03 03:31:19 | `total_count: 1`; details below |
| [Workflows](https://api.github.com/repos/VladimirMarko/conaled/actions/workflows?per_page=100) | 2026-11-03 03:31:19 | `total_count: 1`; active `Fresh verification`, ID `400027308` |
| [Repository caches](https://api.github.com/repos/VladimirMarko/conaled/actions/caches?per_page=100) | 2026-11-03 03:31:35 | `{"total_count":0,"actions_caches":[]}` |

The sole listed run was
[41446124156](https://github.com/VladimirMarko/conaled/actions/runs/41446124156):

```json
{
  "name": "Fresh verification",
  "head_sha": "7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd",
  "path": ".github/workflows/fresh-verification.yml",
  "event": "schedule",
  "status": "completed",
  "conclusion": "success",
  "created_at": "2026-11-02T12:36:47Z",
  "updated_at": "2026-11-02T13:06:27Z"
}
```

This records GitHub's reported run conclusion. Logs were not downloaded, and
the run is not a full-gate result for candidate `901f734...`.

## Access boundaries

The current official GitHub artifact REST reference explicitly permits
unauthenticated public artifact metadata listing. Its archive-download
subsection separately specifies token permissions and a temporary redirect;
the download guide requires a signed-in user with repository read access.
Public metadata or a listed archive URL would not alone establish an authorized
anonymous download route.

The cache REST reference explicitly permits unauthenticated public cache
listing. Listed fields identify a cache, ref, key, version, timestamps and size;
they do not inventory its files or provide an archive URL. The inspected REST
reference has no documented cache-archive download endpoint. GitHub documents
cache restoration in workflows under branch/ref scope rules. This investigation
did not test authentication or seek another retrieval mechanism.

Official documentation read in this investigation:

- [Actions artifact REST reference](https://docs.github.com/en/rest/actions/artifacts?apiVersion=2022-11-28)
- [Downloading workflow artifacts](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/download-workflow-artifacts)
- [Actions cache REST reference](https://docs.github.com/en/rest/actions/cache?apiVersion=2022-11-28)
- [Dependency caching reference](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching)

## Consequence and prospective validation boundary

No acquisition or reuse step is supported by the observed upstream metadata.
There is consequently no archive to download, stage, or merge into an active
checkout. The existing dependency cache and previously captured local ordinary
outputs remain distinct from this unsuccessful search for an upstream donor.

If a separately published donor is identified later, it would require a new
bounded assessment of its lawful access route, exact source/configuration/
toolchain/dependency provenance, transport manifest, and complete ordinary
artifact/trace groups. A private stable stage and the unchanged pinned integrity
inspection would then be necessary before any proposed restoration. No copied
verification record, CI success label, or external cache would replace the
candidate's own stock full gate, exhaustive audit and final verification.
That is a prospective constraint, not an instruction to begin such work now.

Only this report was written. No project/source/configuration/cache/ref/index
mutation, compiler or Lake hash-helper execution, archive download, cancellation,
resource change, tracker action, or upload was performed. The report's own final
SHA256 is supplied to the parent at handoff after freezing; it is a durability
identity, not a project acceptance result.
