# Broad-import investigation and candidate

Two original FRP modules directly imported the all-library Mathlib aggregate.
The candidate changes imports alone; definitions and proof bodies remain
byte-identical to70a1477. The first focused build of both modified modules passed
in the exact offline pinned Nix environment (3145 jobs; the final FRP.Spec and
FRP.Equivalence compiles were31s and32s). This is not a benchmark against a
matched baseline and not full project acceptance. Deprecated forwarding imports
are being replaced by their named current targets before candidate capture.

Environment recovery removed only completed clean, reachable review checkouts,
omitted unrelated archived Haskell history from new implementation worktrees,
and cleared already-extracted Mathlib download archives. All dependency sources
and compiled outputs, user attachments, code, checkpoints and session records
remain. The filesystem still has little unreserved headroom. Nix now uses its
installed locked closure offline with eval-cache disabled; versions unchanged.

The earlier full check never produced a success record and is not reused as
success. The import-only candidate must pass full source/import checks, stock
Lake compilation of every project module, exhaustive proof audit, a matching
verification.json, final verify and both review axes.
