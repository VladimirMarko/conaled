# Lake reuse of inconsistent output artifacts

Investigation of the cache failure during #268, 2026-10-30. This is evidence
for [#222](https://github.com/VladimirMarko/conaled/issues/222), not completion
of its verified-reuse programme or an implementation of replacement tooling.
The owner subsequently clarified that #222 is the first step towards replacing
Lake infrastructure, with an upstream bug report to precede replacement work.

## What survived

The failed #268 incremental build used a separate copy of the main checkout's
`.lake` directory. Its `SquareKit.Internal.GraphEmission.olean` was identical
to the stale artifact preserved during #256: 1,652,536 bytes, SHA-256
`1706bc30e261488c78ece61d611928de6a4262f329ae4df4d5ea15b1ef2fdc0a`.
The trace named output `8e3cc7e2fd7486e2.olean`, whereas the adjacent hash
sidecar contained `83a9a9a995929b8b`. The trace's recorded build command referred
to an earlier `/tmp/conaled-233` checkout. Those historical path names establish
provenance clues, not a reproducible location or a cause.

The preserved binary, sidecar and trace, plus failed and fresh verification
logs, survived removal of the #268 worktree. The donor cache still contained
identical copies when this investigation began. Fresh #268 verification passed
all 947 modules including the exhaustive axiom audit without graph-emission
source changes. The durable incident details are also recorded in
[the #222 observation](https://github.com/VladimirMarko/conaled/issues/222#issuecomment-6530717664).

The historical evidence has limits. It is not a record of every filesystem
write, cache transfer or concurrent process. We have not established how the
original binary and metadata became mixed. Repeated encounters with this same
binary are not independent corruption events.

## Portable reproduction

Run from the repository's pinned development environment:

```sh
direnv exec . bash scripts/repro-lake-output-mismatch.sh
```

The [diagnostic fixture](../../scripts/repro-lake-output-mismatch.sh) creates a
private temporary package with two modules and no external dependencies. It
compiles `Leaf`, adds a declaration and rebuilds, then restores the old binary
and its hash sidecar while retaining the new input trace. A client refers to
the added declaration. This deliberately constructed inconsistent state
reproduces the acceptance failure; it does not reconstruct the historical
operation that produced our inconsistent cache.

Observed with the repository's Lean/Lake 4.35.0 pin:

| Probe | Result |
|---|---|
| Ordinary build, repeated | Reuses the old module; client fails with unknown `Leaf.newValue`. |
| Remove `.olean.hash` | Same failure. |
| `lake --rehash build` | Same failure. |
| `lake --no-cache build` | Same failure. |
| Remove the module's `.trace` | Rebuilds successfully; the client sees the new declaration. |

The script checks the specific missing-declaration diagnostic, not merely a
nonzero exit. It expects this diagnosed behavior and exits unsuccessfully if
it changes, so it is a diagnostic fixture rather than a permanent requirement
that Lake retain the behavior. It cleans up its private package and never
changes repository build artifacts. The original incident files are not needed.

## What explains acceptance

The pinned implementation makes a distinction between input freshness and
output integrity. In
[Lake/Build/Trace.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/Build/Trace.lean),
`BuildTrace.checkAgainstHash` compares the input hash and checks existence.
In [Lake/Build/Module.lean](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/Build/Module.lean),
`Module.checkArtifactsExist` checks the presence of expected output files.
The up-to-date branches in `Module.recBuildLean`'s `fetchCore` reuse existing
artifacts; they do not compare their actual bytes with the output identities
recorded in the saved trace before accepting that branch.

This explains why refreshing hashes does not by itself repair the fixture:
computing a hash of the old binary does not establish that it is the binary
produced for the current inputs. The `--no-cache` result also shows that remote
cache downloading is unnecessary for this reproduction. It does not prove
that no historical cache transfer contributed to the original incident.

The established failure is a limitation of reuse in the presence of externally
inconsistent outputs. Whether it violates an intended Lake guarantee, and
whether an upstream change is appropriate, require assessing that guarantee.
We have not shown that ordinary isolated Lake builds create inconsistent sets.

## Consequences for #222

Keep the original provenance question separate from the reproducible acceptance
mechanism. Use this fixture when evaluating an output-integrity check or cache
transfer discipline. Such a check must bind consumed output bytes to the
successful build of the claimed inputs; comparing a hash with an independently
replaceable sidecar alone is insufficient.

For agent worktrees, copying dependency caches while rebuilding project outputs
avoids importing this particular inconsistent project artifact set. Moving a
complete, verified artifact set could also be evaluated, with explicit atomicity
and provenance assumptions. These are candidates to compare, not implemented
changes to cache-transfer policy. Lake scheduling with the local guard described
below and periodic fresh verification is the current build policy. The owner’s
replacement direction is a project decision; this incident alone
does not establish that replacement is necessary. One fresh success does not
establish future cache integrity.

## Local mitigation

The [upstream report](https://github.com/leanprover/lean4/issues/16123) includes
a standalone reproduction and results on Lean 4.35.0 and
4.37.0-nightly-2026-10-30. The local guard in
[`scripts/lake_integrity.py`](../../scripts/lake_integrity.py) runs before and
after incremental compilation through `check.sh`. Its
[hashing helper](../../scripts/lake-output-hashes.lean) calls the pinned Lake
binary-file hash implementation directly; it does not trust `.hash` sidecars.
The helper is executable tooling, outside the integrated mathematical library
and its axiom audit, and is exercised by the command-level regression tests.

The guard checks each inventoried build target's `.olean`, `.ilean`, and C
output against its saved trace, including module-system parts and additional
outputs when described. Missing, malformed, or unrecognized trace evidence, a
missing artifact, or a hash mismatch invalidates that module's outputs,
sidecars, trace, and local archive. Lake then rebuilds the module. The guarded
invocation disables artifact-cache restoration/writes through its environment,
rejects an explicitly enabled project cache, passes `--no-cache`, and uses
`--rehash` so stale sidecars cannot supply dependency identities. Existing
dependency build directories remain reusable. A second integrity pass rejects
inconsistent outputs before the exhaustive audit; it does not retry indefinitely.

Paths for checking and removal come from inventoried source module names and
the supported build layout, not arbitrary paths from trace data. The adapter
rejects custom project build/source directories and `lakefile.lean`. Its trace
schema is pinned to `2025-09-10`; upgrades require reassessment. Lake's current
hash is noncryptographic, so this check is not protection against deliberate
hash collisions or coordinated replacement of traces and outputs.

This is a temporary consistency check with a narrower scope than #222:

- A trace and output can agree while both describe the wrong build. The guard
  trusts the recorded association between inputs and outputs; it does
  not establish source provenance or successful compilation of those inputs.
- Checking before and after a build does not prevent an artifact or source
  from changing before or during consumption. Stable isolated checkouts remain required;
  the guard does not make concurrent writers safe.
- The project-output scope leaves external dependency caches trusted. Fresh mode also reuses those caches, so neither check certifies
  their integrity.
- The guard in `check.sh` covers that command only. Direct Lake commands and
  editor consumers do not acquire its checks automatically. Native object and
  shared-library facets are outside this Lean-module-output check.
- The guard depends on the pinned Lake trace format and hash semantics.
  Missing or unrecognized evidence must trigger rebuilding or an explicit
  failure, never an assertion that reuse was verified.

The integration tests in `scripts/test-check.py` exercise automatic recovery
from an old output and sidecar paired with a current trace, unchanged-build
reuse, missing and unrecognized evidence, module-system artifact parts, and
cache-disabled recovery even when the caller enables the artifact cache.
They also check that an output changed during compilation is rejected before
the audit. This last case tests one detectable mutation, not general race freedom.

Keep the exhaustive axiom audit and cache-independent project rebuild as
separate checks. Neither successful recovery nor passing those checks completes
#222's conditional reuse contract, connected implementation, and remaining
trust analysis. The [session-log investigation](lake-session-failure-review.md)
records other observed failures and the limits of their provenance evidence.

### Measured guard cost

A local warm run on the 947-module checkout hashed 2,838 artifacts in each
pass: 0.31 seconds before Lake and 0.30 seconds afterward. Lake compilation
checking took 3.75 seconds, the audit 14.24 seconds, and the complete command
19.63 seconds. These are one-run wall-clock observations with warm filesystem
caches, not a portable performance guarantee or an isolated measurement of the
extra input hashing from `--rehash`.

The preceding run over a copied project cache invalidated 436 modules, mostly
because their traces were absent, and found output mismatches in GraphEmission
and the public entrypoint. It completed the full build and audit in 81.48
seconds. An unchanged second run invalidated no modules. The command-level
fixture also checks that an unchanged repaired output retains its modification
time; passing a full build alone would not demonstrate incremental reuse.
