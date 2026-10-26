# ADWH reconstruction coverage and successor reconciliation

[#149](https://github.com/VladimirMarko/conaled/issues/149) owns the full textbook
reconstruction. The [source map](adwh-reconstruction-map.json) keeps every one of
the 1,240 main-library source modules visible. It is a routing and provenance
record, not a percentage of mathematical completion. GitHub Issues own task
specifications, acceptance and current status.

## Evidence and grouping

The generator checks the preserved ZIP digest and each actual source member
against [the original inventory](adwh-preview-233-inventory.json). Each record
retains its imports, immutable source identity, routing family and original
correspondence member/hash. All 1,239 nonaggregate modules have a correspondence
record. `ADWH` is the aggregate entrypoint. The map also identifies all 32
chapter scope/coverage ledgers by archive member and hash.

**266 correspondence records contain an embedded `source_sha256` that differs
from the preserved source bytes; 973 agree.** The map records both the historical
field and `source_hash_agreement`. The actual source member hash is authoritative
for reconstruction provenance. These mismatches do not alter the source hashes
or establish false theorems, but the correspondence cannot certify current-source
coverage without reconciliation. Inspect the current declaration and recorded
contract before adopting it. Source compilation and audit belong to
[#150](https://github.com/VladimirMarko/conaled/issues/150).

The [family definitions](adwh-reconstruction-families.json) group mathematical
observations and consumers. Their selectors are review routing rules, with the
first match taking precedence. They are not proposed Lean directories or
assertions that everything in a group shares one interface. The preserved
imports expose dependencies across groups. Each source correspondence supplies
more specific contracts, limitations and theorem references; a broad group does
not erase those distinctions.

| Routing families | Reconstruction direction and remaining scope |
|---|---|
| Finite list folds/scans/compression; partial lists | #152 covers reachable fusion and an inclusive scan bridge. #157 covers adjacent-run compression. Partiality, lazy demand, suffix scans and remaining list derivations still need separate contracts. |
| Asymptotic/recurrence/amortized reasoning; sequence representations | #154 starts instrumented composition. Growth proofs, array/tree indexing and allocation models remain to be selected against actual consumers. |
| Ordered search; sorting; rank/selection | Keep sortedness, permutation, stability, rank and query lower bounds distinct. Tree split/join clients may justify shared laws; naming overlap does not. |
| Coin choice; weighted tree construction | Compare enumeration, greedy and tabulated realizations against independent objective semantics. Canonical denominations and tree exchange hypotheses are local premises. |
| Connectivity; graph paths/forests/tours | #158 starts partition observations and list/array histories. Dijkstra, spanning-tree minima and jogger tours remain separate obligations. |
| Thinning; knapsack; layered paths | #151 covers a bounded dominance/optimization slice. Fractional boundaries, integer tables, other frontier variants and full cost recovery remain. Layered paths are not endpoint shortest paths. |
| Subsequences/edit distance; contiguous segments; ordered partitions | Reuse enumeration/optimization transport only after preserving embeddings, edit weights, empty segments, admissibility and tie direction. Bank and paragraph clients retain distinct objectives. |
| Numeric/shuttle recurrences; interval DP; alphabetic trees | #153 covers generalized-cost bracketing. Numeric tables, shuttle objectives, other interval optimizations and Garsia–Wachs reductions/AVL execution remain. |
| Finite numeral/floating arithmetic; arithmetic expression search | Keep finite arithmetic and error contracts explicit. Expression enumeration does not inherit a rounding theorem from output equality. |
| Constraint counting/queens; transition search/planning; concrete puzzle/geometric realizations | #155 covers bounded static heuristic search. #137 separately owns checker/CSP intake. Concrete encodings, certificate chunks and geometric safety remain attached to their own semantics. |
| Infrastructure | Preserve aggregate coverage and counterexample evidence while integrating selected modules through conaled's existing public entrypoint and audit. |

The two new bounded proposals are
[#157, adjacent-run compression](https://github.com/VladimirMarko/conaled/issues/157)
and [#158, connectivity refinement](https://github.com/VladimirMarko/conaled/issues/158).
Their specs name inspected source interfaces, independent semantics and checked
clients. Other rows remain owned by #149 as untouched reference, not silently
deferred. Further issue slices must name a public contract and actual clients
before assigning a shared abstraction.

## Dispositions and declaration coverage

[Scope records](adwh-reconstruction-scopes.json) link #151–#155, #157 and #158
and pin the #151/#152/#153 candidate destinations. Resolve candidate paths
at those exact commits until integration; they need not exist at the map's base
commit. Candidate evidence is partial reconstruction pending acceptance, never
a whole-module parity assertion. The pinned candidate commits are retained in the integration ancestry, so their
paths remain resolvable after cloning. GitHub acceptance records identify the
integrated result; any changed declaration needs a new record or explicit
supersession of the candidate evidence. #111, #137, #109 and #113
remain separate commitments.

Use these dispositions with an explicit source scope:

- **Untouched reference:** no reconstruction selected in this map.
- **Scoped task:** a linked issue owns a named slice; imports needed to prove it
  are not automatically migrated in full.
- **Partial reconstruction:** named candidate declarations exist. Other source
  declarations remain reference and acceptance stays with the issue.
- **Accepted retained/adapted result:** acceptance evidence identifies the exact
  declarations, destination commit, reviewed assumptions and checked uses.
- **Replaced with proved equivalence:** additionally name the equivalence theorem
  and its domain/observation. Merely using a similarly named Mathlib lemma is
  insufficient.
- **Explicit deferral:** link a recorded reason and follow-up owner. No initial
  family is assigned this disposition merely because it was not a pilot.

A replacement record identifies `(snapshot, archive_member, source_declaration,
member_sha256)` plus the destination file/declaration, immutable commit, issue,
disposition and exact scope. The scope file contains concrete #151/#152/#153 examples;
the linked candidate declaration maps supply the full pilot detail. This map
does not copy their entire acceptance history. Future records must preserve
source exceptions, failure behavior, ties and theorem assumptions.

In particular, retain the Chapter 6 groups-three qualification in
`project/docs/chapter06.md` and `GroupRecurrenceLimits.lean`: the recurrence
countermodel refutes an inference, not the actual selector's superlinear
worst-case claim. Do not turn its accepted research disposition into either a
new theorem or an alleged defect. The stock
`cqueens 16 = 14772512` proof and unfinished Installed/GroupChecked endpoints
remain open; historical execution records do not close them.

## Reproduction

From the development shell:

```sh
python3 scripts/build-adwh-reconstruction-map.py --check
python3 scripts/test-adwh-snapshot-diff.py
python3 scripts/adwh-snapshot-diff.py \
  docs/history/algorithm-design-haskell/checkpoint-233.zip \
  docs/history/algorithm-design-haskell/checkpoint-233.zip \
  --output /tmp/adwh-self-comparison.json
```

The generator without `--check` regenerates the map after a reviewed change to
the routing/scopes. It fails on missing correspondence, unassigned source
modules, unknown scoped modules or source hash drift. Embedded correspondence
hash disagreement is preserved as evidence, not silently repaired.

The archive self-comparison has 10,463 unchanged members and no additions,
removals or changes. Six CLI fixture tests cover changed/added/removed content,
build-control deltas, unchanged inputs, ambiguous relocation/copies, duplicate
members, nonrelative members and input-overwrite rejection. These tooling checks
introduce no Lean claims and do not replace the formal build/audit gates.

## A later snapshot

Preserve the successor as a new immutable snapshot using the
[historical intake procedure](../history/algorithm-design-haskell/README.md).
Never overwrite checkpoint 233. Then run:

```sh
python3 scripts/adwh-snapshot-diff.py \
  docs/history/algorithm-design-haskell/checkpoint-233.zip \
  /path/to/preserved-successor.zip --output /tmp/adwh-successor-diff.json
```

The report gives member hashes and added/removed/changed/unchanged paths.
`relocation_candidates` groups equal bytes among removed and added paths; copies
make the match ambiguous, so it does not invent a one-to-one rename.
`dependency_review` includes full textual changes to recognized toolchain,
Lake and Nix controls and lists all affected Lean files. This is byte-level
reconciliation, not a Lean import parser or a dependency resolver.

Review control diffs for changed dependency pins. Inspect affected Lean sources
for import changes, rebuild the source dependency inventory, then compare its
import edges with this map. Use both old and new edges to identify reverse
consumers: removal of an old dependency can matter even when no new edge exists.
Recheck the affected transitive closure with the successor's pinned toolchain
and the exhaustive audit. Changed controls or uncertain dependency resolution
require a fresh full check. Equal member bytes do not certify equal elaboration
under changed imports, dependencies or compiler versions.

For each migrated declaration, first match the old member/hash, then review its
successor declaration and assumptions. A changed path with identical bytes can
reuse the source identity link after relocation review; a changed declaration
needs semantic comparison and checked examples. Preserve old provenance and add
the new snapshot identity, equivalence/correction evidence and acceptance issue.
No real successor was available for this delivery. The fixtures and self-check
exercise reconciliation mechanics only.
