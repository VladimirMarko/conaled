# Coordinator environment preparation

Before author dispatch, copied `/home/vlad/Code/conaled/.lake` into the isolated
trial checkout using `cp -a --reflink=auto`; no shared writable build directory.
Ran `direnv allow .` and `direnv exec . lake build
Applications.Sequences.OrderedSummary ProofAudit`. This tried the whole public
import closure through ProofAudit and failed in unrelated Examples.GraphEmission.
The first preparation output was tool-truncated, not retained in full. A focused
reproduction is preserved as `graph-cache-failure.log`.

The copied `SquareKit/Internal/GraphEmission.olean` was dated October 24 while
its trace was dated October 29. Its missing declarations matched the focused
failure. Preserved that binary outside the repository at
`/tmp/conaled-sequential/249-stale-GraphEmission.olean`, removed only that copied
cache file, and reran the same build; `rebuild.log` records success. Before
locating the correct namespace path, attempted copy/removal of nonexistent
`.lake/build/lib/lean/GraphEmission.olean`; both returned file-not-found and
changed nothing. A build rerun before the correct removal repeated the failure.
These setup errors are coordinator errors, not author proof failures.

No library, toolchain, manifest or task source changed. Authors were told:

> Environment update only: dependency preparation is complete, including ProofAudit. Copied cache had an unrelated stale SquareKit/Internal/GraphEmission.olean; coordinator preserved diagnostics and rebuilt it. No library source changes. You may run final audit when ready. Record this environment message as assistance metadata, not a mathematical hint.

Author timers overlapped this preparation and other host activity. Elapsed
intervals cannot isolate reasoning time. The parent integration workflow owns
candidate acceptance; these setup logs are not its verification receipt.
