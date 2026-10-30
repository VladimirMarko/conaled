# Lake reuse of inconsistent output artifacts

Investigation of the cache failure during #268, 2026-10-30. This is evidence
for [#222](https://github.com/VladimirMarko/conaled/issues/222), not completion
of its verified-reuse programme or a decision to replace Lake.

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
changes to repository build policy. Stock Lake plus periodic fresh verification
remains the current policy. The present evidence does not justify replacing
the build system, nor does one fresh success establish future cache integrity.
