# Common PFDS integration scope matrix — checkpoint 045 preparation

**Status: continuation preparation only. Every formal scope remains unaccepted.**

Prepared on 2026-11-03T23:28:36.604143+00:00 by `/root/recovery_requirements`. This is a read-only Git/source-record investigation within the existing nine implementation/review loops. It is not a new independent Standards or Spec review, not a review dispatch, and not a compiler or acceptance result. The only written artifacts are this report and its companion JSON. No source, tracker, branch, index, runtime, dependency or build-output change was made. A read-only helper extracted the five later scopes’ retained findings.

The companion [validation/common-integration-scope-matrix-045.json](../validation/common-integration-scope-matrix-045.json) contains exact file changes and before/after Git blobs/modes, content hashes, complete commit lists/parents/subjects, requirement identities, the retained ticket snapshots, every finding and its observed historical occurrences, report/evidence identities, and per-axis coverage obligations. Its SHA-256 is `7b3d0be9656e87f77cd5fbac62b23475458d08c3f4d47ee4add0156c90947eec`. No scope or finding is replaced by an aggregate pass.

## 1. Common candidate and preserved bases

Selected candidate: `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5`; tree `d3dcf94916de5ccaf3df357e06192e69c4e0cf33`. Preserved branch: `pfds/signed-potential`. Planned isolated checkout: `validation-pfds-integration`. Restored main remains `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`. This report neither materializes nor accepts that candidate.

The following original full review bases are all actual ancestors and merge bases of C. Each old and new count below was recomputed from immutable Git objects. “Files” means the complete changed-path range, not only the mathematical owner’s new files. Exact enumerations are in `scopes[].historical_full_scope` and `scopes[].retargeted_full_scope` in the JSON.

| Ticket | Original full review base | Last retained candidate | Files old → C | Commits old → C |
| --- | --- | --- | ---: | ---: |
| 10013 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` | `901f734161920a76f3b399a575805b9a1d31e971` | 14 → 170 | 5 → 68 |
| 10018 | `70a1477d822efd4fdcec2007280f650bb4695eda` | `901f734161920a76f3b399a575805b9a1d31e971` | 6 → 164 | 3 → 66 |
| 10002 | `82501d108f33c62d21b5e0d0f7d2376b902d8d49` | `99a29dcd02eb529fbefbb675e244a8c47b78cdef` | 42 → 162 | 33 → 65 |
| 10014 | `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4` | `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` | 42 → 125 | 10 → 34 |
| 10019 | `b422800fb5b6dc1253823057c0ea71644274d77c` | `361f5f3f6bb3de1974510ce355883dac2bf25333` | 58 → 94 | 11 → 28 |
| 10020 | `ea8afa12706d30cdc69ece1a172d5f21a3ea1809` | `3dd930c3e3989f3e5530463f3ac937a629551335` | 14 → 39 | 4 → 18 |
| 10021 | `3dd930c3e3989f3e5530463f3ac937a629551335` | `577be121e074ddb5de6727a7481c115cb61b3b27` | 11 → 26 | 5 → 14 |
| 10022 | `577be121e074ddb5de6727a7481c115cb61b3b27` | `5e048f781aa04be9ce993f1e7455bdc82df22bff` | 11 → 16 | 4 → 9 |
| 10023 | `5e048f781aa04be9ce993f1e7455bdc82df22bff` | `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` | 6 → 6 | 5 → 5 |

The earliest full range is **170 paths / 68 commits** (29,068 additions and 52 deletions); the Chapter 2 range is **162 paths / 65 commits** (27,850 additions and 28 deletions). There are no exclusions. The earliest ranges include the already accepted Chapter 1 introductory-accounting commit `82501d1` and its three documentation paths. That context retains its existing narrow acceptance; it does not discharge its 16 forward complexity contracts. The nine mathematical ownership ranges plus that accounting context cover every one of the 170 paths.

**901 is not an ancestor of C.** Their common ancestor is `70a1477d822efd4fdcec2007280f650bb4695eda`. The two prerequisite scopes must therefore explicitly continue on C, retaining their original bases and requirements. Twelve of 10013’s fourteen formerly reviewed files match C; its public entrypoint and shared-persistence document changed. All six 10018 import files match C. A literal comparison against base 70a confirms that removing plain import-declaration lines leaves every other byte equal in those six files. This mechanical comparison is not compilation or elaboration evidence.

### Bounded ownership is not a reduced acceptance scope

The last incorporated ticket bases remain distinct from the original full bases for 10014 (99a29dc), 10019 (a3feaff) and 10020 (361f5f3). JSON retains both exact identities and both historical ranges. For attribution only, 10013’s own list development ends at 70a1477 before import repairs, and Chapter 2’s own implementation ends at main 76d77a1 before its incorporated import repairs. These attributions do not exclude any path from either independent full review.

| Ticket | Mathematical ownership range | Owned paths | Requirement / version |
| --- | --- | ---: | --- |
| 10013 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` → `70a1477d822efd4fdcec2007280f650bb4695eda` | 8 | [requirements/shared-persistence.md](../requirements/shared-persistence.md) v2 |
| 10018 | `70a1477d822efd4fdcec2007280f650bb4695eda` → `901f734161920a76f3b399a575805b9a1d31e971` | 6 | [requirements/import-footprint.md](../requirements/import-footprint.md) v1 |
| 10002 | `82501d108f33c62d21b5e0d0f7d2376b902d8d49` → `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` | 36 | [requirements/chapter02.md](../requirements/chapter02.md) v1 |
| 10014 | `99a29dcd02eb529fbefbb675e244a8c47b78cdef` → `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` | 38 | [requirements/suspension-foundation.md](../requirements/suspension-foundation.md) v1 |
| 10019 | `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` → `361f5f3f6bb3de1974510ce355883dac2bf25333` | 50 | [requirements/pure-recursive-forcing.md](../requirements/pure-recursive-forcing.md) v1 |
| 10020 | `361f5f3f6bb3de1974510ce355883dac2bf25333` → `3dd930c3e3989f3e5530463f3ac937a629551335` | 13 | [requirements/pure-cache-counts.md](../requirements/pure-cache-counts.md) v1 |
| 10021 | `3dd930c3e3989f3e5530463f3ac937a629551335` → `577be121e074ddb5de6727a7481c115cb61b3b27` | 11 | [requirements/persistent-debit-foundation.md](../requirements/persistent-debit-foundation.md) v1 |
| 10022 | `577be121e074ddb5de6727a7481c115cb61b3b27` → `5e048f781aa04be9ce993f1e7455bdc82df22bff` | 11 | [requirements/body-entry-counts.md](../requirements/body-entry-counts.md) v1 |
| 10023 | `5e048f781aa04be9ce993f1e7455bdc82df22bff` → `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` | 6 | [requirements/signed-potential.md](../requirements/signed-potential.md) v1 |

All complete original requests and later operational clarifications are retained by path and SHA-256 in the JSON. The current user selects the supplied unified Lean 4.35.0 kit and asks for small recovery checkpoints with the updated setup. Those instructions change the selected environment/checkpoint approach; they do not waive proof, source, review or stock acceptance obligations. Checkpoint 044’s serial compiler scheduling supersedes older “one full plus one focused” prose.

## 2. Full review coverage and ownership boundaries

Both independent axes must cover every file in each original-full-base-to-C range, the affected unchanged interfaces/consumers, the complete requirements and all retained findings. Earlier matching analyses may be reused only after checking source and context identities; no historical Blocked outcome transfers as approval. Each row retains its own requirement ownership and dependency disposition even when the reports and literal C validation record are shared.

| Ticket | Previously reviewed paths changed after its last candidate | Additional paths in full range |
| --- | --- | ---: |
| 10013 | `SquareApplications.lean`, `docs/research/pfds-shared-persistence.md` | 156 |
| 10018 | None | 158 |
| 10002 | `SquareApplications.lean` | 120 |
| 10014 | `Applications/Suspensions/Recursive.lean`, `SquareApplications.lean`, `docs/research/pfds-suspensions.md` | 83 |
| 10019 | `SquareApplications.lean`, `docs/research/pfds-pure-suspensions.md` | 36 |
| 10020 | `SquareApplications.lean` | 25 |
| 10021 | `SquareApplications.lean` | 15 |
| 10022 | `SquareApplications.lean` | 5 |
| 10023 | None | 0 |

### 10013 — Cross-cutting immutable cell and sharing foundation

Immutable shared lists and exact physical path copying: fresh allocation preserves old observations; actual append/update traversals, sufficient fuel and explicit failure; suffix tail-chain, closure, reachability and distinct-cell space; public relational/resource clients.

No chapter acceptance, Lean runtime, reclamation, arbitrary persistent amortization or crash-durability claim. Chapter 2 later owns integer indexing and trees.

Controlling record: [reviews/shared-persistence.md](../reviews/shared-persistence.md). Latest retained axes: [reviews/shared-persistence-standards-r5.md](../reviews/shared-persistence-standards-r5.md); [reviews/shared-persistence-spec-r5.md](../reviews/shared-persistence-spec-r5.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/shared-persistence-statement-check.md](../research/shared-persistence-statement-check.md), [research/book-full-inventory.md](../research/book-full-inventory.md). All associated historical review files and their identities are retained in the JSON.

### 10018 — Replace whole-Mathlib FRP imports with their actual dependencies

Only import declarations in the six preserved FRP/consumer files: narrow the two whole-Mathlib imports and add four actual direct providers while preserving all remaining bytes.

Other changes in the enlarged full scope belong to their named owners. No theorem/proof changes may be attributed to this import-only permission; no performance conclusion follows merely from narrower imports.

Controlling record: [reviews/import-footprint.md](../reviews/import-footprint.md). Latest retained axes: [reviews/import-footprint-standards-r3.md](../reviews/import-footprint-standards-r3.md); [reviews/import-footprint-spec-r3.md](../reviews/import-footprint-spec-r3.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/import-footprint.md](../research/import-footprint.md), [research/import-footprint-r2.md](../research/import-footprint-r2.md), [research/import-footprint-r3.md](../research/import-footprint-r3.md). All associated historical review files and their identities are retained in the JSON.

### 10002 — Persistence

Complete inspected book pp7-16 and Exercises 2.1-2.6: operation-only stacks and separate laws, List/custom correspondence, sufficient-fuel append and counts, source integer update, persistent root/cell sharing, ordered sets/maps, primitive comparisons, abort/combined duplicate insertion, complete/shared balanced constructors, and composed observers.

Equal-value DAG constructors are not strict search trees. Source integer negatives must traverse to failure. Finite-map values are arbitrary, key-only ordered and overwrite-on-bind. No Chapter 3 algorithm, full runtime model or blanket balanced-tree bound.

Controlling record: [reviews/chapter02.md](../reviews/chapter02.md). Latest retained axes: [reviews/chapter02-standards-r3.md](../reviews/chapter02-standards-r3.md); [reviews/chapter02-spec-r3.md](../reviews/chapter02-spec-r3.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/book-full-inventory.md](../research/book-full-inventory.md), [research/book-thesis-union.md](../research/book-thesis-union.md), [research/chapter02-preacceptance-gaps.md](../research/chapter02-preacceptance-gaps.md), [reviews/chapter02-native-continuation-preparation-043.md](../reviews/chapter02-native-continuation-preparation-043.md). All associated historical review files and their identities are retained in the JSON.

### 10014 — Thesis AppendixA suspension extension and evaluation correspondence

Book suspension mechanism, thesis Chapter 2 and Appendix A extension of the explicitly delimited 1990 SML core: syntax/static rules, source-rule/evaluator correspondence, mutable thunks and references, normal/raised/mismatch/fault/unknown distinctions, write-before-match, recursive environments, private-allocation transport and measured observation clients.

Preserve effectful reentry, overwrite, retained effects and SUSP-STAT-001. No blackholing, global type-preservation, unconditional at-most-once, arbitrary divergence/trace equivalence or full SML compiler claim. Pure self-forcing belongs to 10019; stream algorithms retain Chapter 4 ownership.

Controlling record: [reviews/suspension-foundation.md](../reviews/suspension-foundation.md). Latest retained axes: [reviews/suspension-foundation-standards-r1.md](../reviews/suspension-foundation-standards-r1.md); [reviews/suspension-foundation-spec-r1.md](../reviews/suspension-foundation-spec-r1.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/suspension-foundation-inventory.md](../research/suspension-foundation-inventory.md), [research/suspension-base-core.md](../research/suspension-base-core.md), [research/sml90-source-identity.json](../research/sml90-source-identity.json). All associated historical review files and their identities are retained in the JSON.

### 10019 — Pure recursive forcing and successful cache reuse

Finite pure source interpretation, actual recursive source expressiveness, raw pure self-reentry nontermination, successful cache certificates/reuse, raw value-constructor persistence and actual cached recursive-closure clients.

Maintain explicit primitive/domain restrictions and unrestricted effectful counterexamples. Exceptional current frames skip their own write but retain reached memory. General successful-write counts belong to 10020; body-entry uniqueness needs 10022 assumptions.

Controlling record: [reviews/pure-recursive-forcing.md](../reviews/pure-recursive-forcing.md). Latest retained axes: [reviews/pure-recursive-forcing-standards-r2.md](../reviews/pure-recursive-forcing-standards-r2.md); [reviews/pure-recursive-forcing-spec-r2.md](../reviews/pure-recursive-forcing-spec-r2.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/pure-recursive-forcing-preacceptance.md](../research/pure-recursive-forcing-preacceptance.md), [research/pure-recursive-forcing-cached-closure.md](../research/pure-recursive-forcing-cached-closure.md), [research/pure-recursive-forcing-compatibility.md](../research/pure-recursive-forcing-compatibility.md). All associated historical review files and their identities are retained in the JSON.

### 10020 — Finite pure cache-write accounting

Actual raw successful cache-write events, pending-frame provenance, finite admitted pure-source at-most-one write per address and ordered trace observation, with compatible/hereditarily preserving primitives and actual evaluation premises.

No general body-entry or arbitrary-work bound. Exceptional bodies can retry; equal code at distinct allocated addresses remains distinct. PREP-10019-02 records this separate ownership.

Controlling record: [reviews/pure-cache-counts.md](../reviews/pure-cache-counts.md). Latest retained axes: [reviews/pure-cache-counts-standards-r1.md](../reviews/pure-cache-counts-standards-r1.md); [reviews/pure-cache-counts-spec-r1.md](../reviews/pure-cache-counts-spec-r1.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/pure-cache-counts-source.md](../research/pure-cache-counts-source.md), [research/pure-cache-accounting.md](../research/pure-cache-accounting.md). All associated historical review files and their identities are retained in the JSON.

### 10021 — Persistent logical histories and finite debit accounting foundation

Ordinary quiver logical histories, source laws I-III, fresh debit allocation, support provenance, finite closed-scope and explicit-boundary cardinality bounds, injective renaming and an existing Resources.run interpreter of abstract debit observations.

Cycles, loops, parallel arrows, support versus multiplicity, initial-state terms and enumeration premises remain. Actual source incidence, chronological payment-before-force and arbitrary evaluator-work correspondence remain 10017.

Controlling record: [reviews/persistent-accounting.md](../reviews/persistent-accounting.md). Latest retained axes: [reviews/persistent-accounting-standards-r1.md](../reviews/persistent-accounting-standards-r1.md); [reviews/persistent-accounting-spec-r1.md](../reviews/persistent-accounting-spec-r1.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/persistent-trace-source-scope.md](../research/persistent-trace-source-scope.md), [research/persistent-trace-reuse.md](../research/persistent-trace-reuse.md), [research/persistent-history-implementation.md](../research/persistent-history-implementation.md), [research/persistent-debit-implementation.md](../research/persistent-debit-implementation.md), [research/persistent-realization-implementation.md](../research/persistent-realization-implementation.md). All associated historical review files and their identities are retained in the JSON.

### 10022 — Conditional bounds on actual suspension-body entries and their debit observation

Actual pending-address loss, conditional actual-body-entry bounds using FreshEntries and NoMemoizeUnwind, finite pure specialization retaining no-unwind, unfinished prefixes and same ordered body-address projection into distinct-identity debit observation.

Finite pure normal return alone does not imply no unwind or one body entry. Preserve the real handled retry with two entries and zero writes. These are body-event counts, not arbitrary internal work; full work/debit correspondence remains 10017.

Controlling record: [reviews/body-entry-counts.md](../reviews/body-entry-counts.md). Latest retained axes: [reviews/body-entry-counts-standards-r1.md](../reviews/body-entry-counts-standards-r1.md); [reviews/body-entry-counts-spec-r1.md](../reviews/body-entry-counts-spec-r1.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/body-entry-counts-design.md](../research/body-entry-counts-design.md), [research/pure-body-counts-source.md](../research/pure-body-counts-source.md), [research/suspension-body-realization-correction-r1.md](../research/suspension-body-realization-correction-r1.md). All associated historical review files and their identities are retained in the JSON.

### 10023 — Shared potential accounting over ordered and signed additive domains

Minimal generalization of existing budget/potential telescoping, ordered/signed savings and opposite-sign debt, actual state trajectory, terminal-potential conditions, Nat specialization and additive observation transport, with Int/fractional Real/negative-boundary/BinaryCounter clients.

Same-trajectory algebra alone does not prove shared consumable potential over persistent aliases, chronological debit payment, runtime cost or any later algorithm complexity. Existing Nat clients and the shared executor retain their meanings.

Controlling record: [reviews/signed-potential.md](../reviews/signed-potential.md). Latest retained axes: [reviews/signed-potential-standards-r3-042.md](../reviews/signed-potential-standards-r3-042.md); [reviews/signed-potential-spec-r3-042.md](../reviews/signed-potential-spec-r3-042.md). Both remain **Blocked**. The new common-candidate continuation for this scope is **pending**, not performed by this preparation.

Source/statement preparation: [research/signed-potential-implementation.md](../research/signed-potential-implementation.md), [research/signed-potential-proof-corrections-042.md](../research/signed-potential-proof-corrections-042.md), [research/potential-generalization-inventory.md](../research/potential-generalization-inventory.md), [research/potential-transport-client.md](../research/potential-transport-client.md). All associated historical review files and their identities are retained in the JSON.

### Cross-scope interactions requiring explicit coverage

- `SquareApplications.lean` grows across the combined scope. Each public-module closure and exhaustive-audit obligation must be assessed against C, not an earlier smaller entrypoint.
- 10014’s `Applications/Suspensions/Recursive.lean` and source map were later changed by pure-source work. Reassess these changes and the source-domain boundary; do not treat identical surrounding files as approval of a changed interface.
- The 10019 source map was later updated for 10020. Retain the separate ownership of nonreentry/cache reuse, successful cache writes, and conditional body entries.
- 10021’s debit support interpreter and 10022’s body-address observation connect on the same modeled events. Neither identifies arbitrary internal body work with debit support; 10017 retains that obligation.
- 10023 generalizes the existing `Resources.Potential` API. Its six-file diff must be assessed with existing Nat clients and the unchanged executor context; source identity of later or earlier consumers does not by itself prove compatibility.
- The full prerequisite ranges also contain accepted Chapter 1 accounting documentation. Preserve its narrow accounting status and the open forward costs; do not infer a stronger chapter or whole-union result.

## 3. Every retained finding and current disposition

The inventory contains **39 distinct IDs**, including preparatory findings, development diagnostics and explicit source/ownership boundaries. Compressed historical spellings such as `CH02-PRE001` and `IMPORT-VAL004` are preserved as aliases of the original hyphenated identifiers. The JSON records every observed occurrence in the retained session text/JSON files; no alias creates a new finding and no missing hyphen erases an old one. These are transcriptions of retained dispositions, not new reviewer closures.

| ID | Owner(s) | Latest retained disposition | Meaning / boundary |
| --- | --- | --- | --- |
| `PERSIST-VAL-001` | 10013 | fixed with retained focused compiler and independent review evidence | The redundant successful-update adapter tactic was removed without changing contracts or weakening the linter; historical failure remains. Full acceptance is still open. |
| `IMPORT-VAL-001` | 10018, 10013 | fixed with matched focused evidence; full gate pending | Direct Nat successor/order provider repairs Demand.pending_registered. |
| `IMPORT-VAL-002` | 10018, 10013 | fixed with matched focused evidence; full gate pending | Direct finite-set lattice provider repairs Finite.finiteHistory. |
| `IMPORT-VAL-003` | 10018, 10013 | fixed with matched focused evidence; full gate pending | Direct Real Archimedean provider repairs Examples.FRP.ticks_finiteHistory. |
| `IMPORT-VAL-004` | 10018, 10013 | unresolved pending genuine terminal compiler evidence | Direct natural-size provider supplies Nat.size_pow in Examples.IndefiniteService; genuine terminal successful checking remains required. |
| `CH02-PRE-001` | 10002 | static implementation closure retained; full acceptance pending | Actual duplicate matched subtree root and every descendant retain identity; only strict ancestors allocate. |
| `CH02-PRE-002` | 10002 | static implementation closure retained; full acceptance pending | Actual abort and combined insertions jointly prove original-state duplicate return, zero cells, absent correctness and the comparison bound for the same execution. |
| `CH02-PRE-003` | 10002 | static implementation closure retained; full acceptance pending | Physical finite-map overwrite preserves both endpoint children as well as ancestor off-path roots. |
| `CH02-PRE-004` | 10002 | static implementation closure retained; full acceptance pending | Physical implementations expose ordinary/relational observation adapters and meaningful composed clients. |
| `CH02-PRE-005` | 10002 | unresolved mandatory integrated validation gate | Exact whole Chapter 2 build, exhaustive audit, stock success record, both independent outcomes, immediate verify and delivered identity remain mandatory. |
| `SUSP-STAT-001` | 10014 | established scoped source counterexample boundary | Lean checked in focused Static r8: the exact cachedReference core AST has boolean type and finite execution returning integer0, with atomType(integer0) unequal boolean. This concerns the explicitly delimited1990+AppendixA effectful core. Source rules are retained; no blanket value-type preservation is claimed. |
| `SUSP-DEV-001` | 10014 | closed by retained focused development evidence | Closed in focused machine round3: helper renamed proceed, Finset supremum function explicit, trace projection equation corrected; Machine compiled. |
| `SUSP-DEV-002` | 10014 | closed by retained focused development evidence | Closed in focused machine round3: Rules example names relations explicitly; connected source-rule example compiled. |
| `SUSP-DEV-003` | 10014 | closed by retained focused development evidence | Closed by machine r5: Namespace example compiled after reserved binder correction. |
| `SUSP-DEV-004` | 10014 | closed by retained focused development evidence | Closed by machine r6: original runtime cases, unused-RHS typing corrections and actual mutual Rec/SRec case all compiled; expected runtime conclusions unchanged. |
| `SUSP-DEV-005` | 10014 | closed by retained focused development evidence | Closed by Static r7/r8: original syntax-index equations justify weakening termination; Static/Names/Grammar cores and all static/grammar clients now compile with unchanged statements/default limits. |
| `SUSP-DEV-006` | 10014 | closed by retained focused development evidence | Closed by Return r3 (module+examples): opaque symbolic tails and explicit constructor substitution, default limits and unchanged claims. |
| `SUSP-DEV-007` | 10014 | closed by retained focused development evidence | Closed by Observation r2 (module+examples): explicit definitional equality closure; exact measured search/count and relational clients compile. |
| `SUSP-DEV-008` | 10014 | closed by retained focused development evidence | Closed by Continuation r3: factored control cases with explicit constructor substitution; statements and limits unchanged. |
| `SUSP-STD-VAL-001` | 10014 | unresolved validation blocker | Exact complete suspension-candidate full build/audit/record/final verification absent. |
| `SUSP-SPEC-VAL-001` | 10014 | unresolved validation blocker | Same exact candidate evidence requirement on the independent Spec axis. |
| `PURE-STD-DOC-001` | 10019 | fixed with retained independent round-2 evidence | Exceptional-exit prose now concerns the current frame own-write omission and retained reached memory, including inner successful writes. |
| `PURE-STD-EVID-001` | 10019 | fixed with retained independent round-2 evidence | Compatibility r2 successful JSON/log preserved byte-identically and independently verified; this is evidence preservation, not whole-candidate validation. |
| `PURE-SPEC-DOC-001` | 10019 | fixed with retained independent round-2 evidence | No universal uncached/retry claim for raising bodies; distinguish the particular unchanged-thunk retry from possible inner writes. |
| `PURE-SPEC-DOC-002` | 10019 | fixed with retained independent round-2 evidence | Foundation prose identifies the implemented pure theorem/client while retaining its pending acceptance. |
| `PURE-STD-VAL-001` | 10019 | unresolved validation blocker | Own complete-candidate stock build, exhaustive audit, stock success record and immediate final verification remain missing. |
| `PURE-SPEC-VAL-001` | 10019 | unresolved validation blocker | Own complete-candidate stock build, exhaustive audit, stock success record and immediate final verification remain missing. |
| `PREP-10019-01` | 10019 | addressed at static/client and focused-evidence level | The recursive cached-closure client obtains its world/cache/capture from actual execution and consumes the certificate on a later cache hit; formal acceptance remains pending. |
| `PREP-10019-02` | 10019, 10020 | retained explicit ownership boundary | 10019 does not own the general at-most-one successful cache-write theorem. 10020 owns it; common integration must not retroactively attribute it to 10019 or erase the boundary. |
| `COUNT-STD-VAL-001` | 10020 | unresolved validation blocker | Own exact complete candidate full build/audit, matching stock record and immediate verification remain required. No static source correction was requested. |
| `COUNT-SPEC-VAL-001` | 10020 | unresolved validation blocker | Own exact complete candidate full build/audit, matching stock record and immediate verification remain required. No static source correction was requested. |
| `PERSIST-ACC-STD-VAL-001` | 10021 | unresolved validation blocker | Own exact complete candidate full build/audit, matching stock record and immediate verification remain required. No static source correction was requested. |
| `PERSIST-ACC-SPEC-VAL-001` | 10021 | unresolved validation blocker | Own exact complete candidate full build/audit, matching stock record and immediate verification remain required. No static source correction was requested. |
| `BODY-COUNT-STD-VAL-001` | 10022 | unresolved validation blocker | Own exact complete candidate full build/audit, matching stock record and immediate verification remain required. No static source correction was requested. |
| `BODY-COUNT-SPEC-VAL-001` | 10022 | unresolved validation blocker | Own exact complete candidate full build/audit, matching stock record and immediate verification remain required. No static source correction was requested. |
| `SIGNED-POT-STD-CODE-001` | 10023 | fixed with retained independent r3 and genuine matching focused evidence | Two narrow noncomputable annotations preserve statements/expected values; subsequent proof-name and Nat-budget coercion corrections are retained with earlier genuine failures. |
| `SIGNED-POT-SPEC-001` | 10023 | fixed with retained independent r3 and genuine matching focused evidence | The same narrow annotations and proof corrections preserve the independent mathematical expectations; focused checking succeeded at 3cf. |
| `SIGNED-POT-STD-VAL-001` | 10023 | unresolved validation blocker; focused portion established | The eleven-target focused success does not supply own full build/audit/record or immediate final verification. |
| `SIGNED-POT-SPEC-VAL-001` | 10023 | unresolved validation blocker; focused portion established | The eleven-target focused success does not supply own full build/audit/record or immediate final verification. |

The independent validation IDs for the two axes are retained separately even where they refer to the same missing evidence. Unnumbered full-validation blockers in the prerequisite records also remain mandatory; the matrix does not invent identifiers for them. No prerequisite/source correction is closed merely because a later candidate contains it or because its old finding has a fixed static disposition.

## 4. Actual evidence retained, and what it does not establish

- [validation/signed-3cf-native-r2.json](../validation/signed-3cf-native-r2.json) records genuine exit 0 for eleven focused targets on C with unchanged captured inputs. It is developmental evidence; it supplies no whole-candidate audit or acceptance record. Earlier d24 and 956 compiler failures remain failures.
- [validation/native-stock-regressions-r1-043.json](../validation/native-stock-regressions-r1-043.json) records the earlier native roots/checker regression passes on 901 (38 roots, 19 checker tests). Reuse under the new kit/C requires an explicit comparison of the relevant runtime, checker/auditor/fixture and dependency inputs. The negative-audit suite still has its own ordinary-output prerequisites and coverage.
- [validation/import-901-native-fresh-r2-disconnection-044.json](../validation/import-901-native-fresh-r2-disconnection-044.json) and the corresponding post-disconnection record preserve the last lost tool session. Its 227 completed module messages do not establish terminal success, a source failure or a cause. Never reuse that session handle or rewrite the original partial record.
- This preparation checked Git ancestry, complete scopes, file/commit identity, relevant guidance equality, literal import-only preservation and stable retained input identities. None of those checks compiles or audits Lean.

### Source availability

The supplied recovery inputs omit the published book, thesis and 1990 SML Definition by policy. Their exact identities and recovery locators remain in [research/union-source-identities.json](../research/union-source-identities.json) and [research/sml90-source-identity.json](../research/sml90-source-identity.json). The saved Chapter 2 continuation assessment explicitly permits reuse of completed chapter reading and independently reviewed source analysis on unchanged Chapter 2 mathematics. The book must be attached again when a new source question or later unread material requires it; a historical Library ID is provenance only. Public thesis/SML sources can be reacquired from the recorded locations. This report claims no new primary-source reading and no complete inspection of later chapters.

## 5. Required continuation and decision sequence

1. Record explicit continuation rounds and both axes’ coverage assignments in the existing nine loops, using this exact common candidate and preserved original bases. This matrix is preparatory and does not itself dispatch or complete those rounds.
2. Finish and independently review the operational integration selector/evidence route and updated environment adoption, preserving the old 901 default and all old records. Do not repoint a guarded controller ad hoc.
3. Materialize a clean private `validation-pfds-integration` at C; keep source, pins, dependencies, runtime and controller inputs stable. Schedule one compiler validation workload at a time.
4. Run the genuine stock fresh full check `./check.sh --candidate HEAD --fresh --jobs 1` through the approved route. Preserve actual terminal exit, complete module coverage, exhaustive audit and the matching `.lake/verification.json`. Do not substitute focused, partial or earlier-candidate evidence.
5. Preserve the fresh record before any later candidate check replaces it. Produce the required ordinary outputs and negative-audit regression through the approved route; reconcile any reusable historical regression evidence by its actual covered inputs.
6. Both independent axes assess the complete ranges, source statements, examples, interfaces, every retained finding and the new real validation evidence. Reconcile explicit dispositions for all nine scopes; no unqualified aggregate pass.
7. Accept prerequisites 10013/10018 before Chapter 2, then the foundation and later integration scopes in their retained dependency order. 10023 has integration gate predecessor 10022, not an invented mathematical dependence on body counts. A single genuine C full record may serve separate same-C decisions; it cannot accept historical tips.
8. Immediately before each actual acceptance/delivery action as required, run `./check.sh --verify-candidate HEAD` on C using its recorded mode; omit fresh/jobs flags. Confirm the delivered bytes are those jointly reviewed. Only actual Chapter 2 acceptance permits Chapter 3 algorithm implementation.
9. Preserve incomplete outcomes honestly and save the updated requirements, source scope, reviews, real evidence and environment recipe in the next small recovery checkpoint.

## 6. Preparation integrity and limitations

The restored repository remained at `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` with unchanged empty Git status during this preparation. All catalogued session input hashes were stable at capture; all nine original full bases matched their actual merge bases; all expected old/new scope counts matched; every global changed path has an ownership annotation; all 39 finding IDs are accounted for; and all six import-only comparisons preserved non-import bytes. These are document/source-identity checks only. Formal acceptance, independent review completion, compiler success and whole-book/thesis completion remain **false/pending**.
