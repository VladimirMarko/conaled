# Preface/Perm correction — explicit natural-size import

Fixed base and merge-base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Candidate: `4adc2f006677b9ac22bbdb4a60a36526632588b2`.
Prior candidate: `c988f183887896c00b09aaff9077a6ea7fb8d68f`.
Full enclosing scope: 26 files, +497/-17, no exclusions.

`validation/1038-candidate.json` records clean main, provisioning and isolated
validation checkouts, the unchanged merge-base, full diff stat, and exact
one-line delta. All previous task changes and findings remain in scope.

The completed direct-PTY fresh run on c988 returned actual exit 1 after 602
successful ordinary compilations. Module 603, `Examples.IndefiniteService`,
reported unknown `Nat.size_pow` and an unsolved goal. It produced no fresh
verification record and never reached the exhaustive audit. Its complete raw
kit start/output/result, actual terminal outcome and diagnostic are preserved
in `validation/1002-candidate-c988f18-unified-pty-fresh2/` and checkpoint071.
This is not a successful formal gate or an unexplained lost terminal result.

The failing source file is byte-identical to the fixed-base file. The exact
pinned Mathlib defines `Nat.size_pow` in `Mathlib.Data.Nat.Size`; the example
did not import that module. The correction adds only that explicit import.
All existing source body bytes, statements, proof terms and cases are retained.
The existing universal example remains `¬ ∃ bound : Nat, ∀ n : Nat, n.size ≤ bound`,
using `n = 2 ^ bound` and `Nat.size_pow` to obtain `bound + 1 ≤ bound`.
There is no mathematical weakening or new assumption.

Requirements and narrow correction scope: `specs/1038-nat-size-import.md`, in
addition to all existing authoritative requirements and chapter specs.
The current cache scope must be rederived because the old671-root/3931-module
inventory did not contain `Mathlib.Data.Nat.Size`.

The proposed focused fixture in `validation/1038-focused-size/Main.lean`
contains the exact source-extracted failing proposition/proof with its required
Mathlib import. It checks that dependency and proof only; it cannot establish
full-file or chapter completion. Actual focused and full-gate results will be
recorded separately. A new complete fresh run, unchanged collector, separate
guarded validation/audit, managed-audit prerequisite, four regressions and final
candidate verification remain required.

Both original independent axes continue in their existing threads and review
this full candidate, reusing prior unchanged-source analysis. At this brief's
creation both are Blocked; ST-001 remains fixed, ST-002 and SP-VAL-001 remain
open. No chapter acceptance or permission to begin Sort is asserted.

Standards subsequently assigned ST-003 to the missing import. The one-line
source correction is proposed at4adc2f0; actual corrected-file elaboration in
the new full fresh run can discharge it without an additional full-file compile.
The copied-proof fixture is scoped diagnostic evidence only.
