# Textbook issue references

Bare `#N` means an issue or pull request in `VladimirMarko/conaled`, at every
number including the thousands. Historical book tickets use short prefixed IDs:

| Namespace | Example | Original tracker |
|---|---|---|
| GitHub | `#174`, `#1002` | This repository's GitHub tracker; no reserved numeric ranges |
| VFA | `VFA-2` | [VFA tickets](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) |
| PFDS | `PFDS-2` | [PFDS tickets](checkpoint-012/books/pfds/records/research/coverage/tickets.json) |
| FDSA | `FDSA-1` | [FDSA tickets](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/) |
| Combined intake | `INT-32` | [Integration tickets](checkpoint-012/books/common/ISSUES.json) |

New work uses GitHub as its single live tracker. New commit messages end with
the applicable real GitHub issue number; mention a book ticket with its short
prefix when needed, for example `fix(maps): recover VFA-19 laws (#559)`.
Prefixes preserve provenance; they do not create another live task tracker.

VFA and PFDS numbers omit the historical 1000 and 10000 offsets. FDSA IDs are
plain sequential numbers assigned once from its sorted checkpoint-012 ticket
IDs, so distinct chapter and shared-unit tickets do not collide. INT numbers
omit zero padding. The explicit crosswalk below is authoritative. Existing IDs
must never be renumbered; any additional historical tickets receive new IDs.

The imported commit messages in `master` use these short IDs in subjects and
bodies. Real GitHub references, including FDSA's `#174`, retain their meaning.
The [qualified commit history](commit-references.md) lists the rewritten IDs;
[issue-lineages.json](issue-lineages.json) records both original and rewritten
IDs. [commit-rewrite.json](commit-rewrite.json) preserves the original raw
commit objects, so historical proof receipts and donor ledgers remain usable.
See [source recovery](README.md#source-recovery) to restore those identities.
The mapping is scoped to recorded commits, never to a numeric interval.

The registry includes all preserved book/integration tickets and every imported
commit reachable from the preservation carrier but absent from the receiving
baseline. It was checked against the original tracker IDs and Git messages.
`GH-174` is its machine-readable key for the real GitHub reference. Current
owners route remaining work; they do not reproduce old status or assert that
one newer issue has discharged every historical requirement. Original tracker
contents remain immutable historical evidence.

## Crosswalk and current owners

| Reference | Original ID | Historical subject | Preserved record | Current GitHub owners |
|---|---|---|---|---|
| `VFA-0` | `VFA-1000` | Environment, provenance, local tracker, and recovery checkpoints | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-1` | `VFA-1001` | Formalize and harmonize VFA Preface | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-2` | `VFA-1002` | Formalize and harmonize VFA Perm | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-3` | `VFA-1003` | Formalize and harmonize VFA Sort | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#560](https://github.com/VladimirMarko/conaled/issues/560) |
| `VFA-4` | `VFA-1004` | Formalize and harmonize VFA Multiset | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-5` | `VFA-1005` | Formalize and harmonize VFA BagPerm | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-6` | `VFA-1006` | Formalize and harmonize VFA Selection | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-7` | `VFA-1007` | Formalize and harmonize VFA Merge | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-8` | `VFA-1008` | Formalize and harmonize VFA Maps | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#559](https://github.com/VladimirMarko/conaled/issues/559) |
| `VFA-9` | `VFA-1009` | Formalize and harmonize VFA SearchTree | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-10` | `VFA-1010` | Formalize and harmonize VFA ADT | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-11` | `VFA-1011` | Formalize and harmonize VFA Extract | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-12` | `VFA-1012` | Formalize and harmonize VFA Redblack | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-13` | `VFA-1013` | Formalize and harmonize VFA Trie | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-14` | `VFA-1014` | Formalize and harmonize VFA Priqueue | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-15` | `VFA-1015` | Formalize and harmonize VFA Binom | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-16` | `VFA-1016` | Formalize and harmonize VFA Decide | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-17` | `VFA-1017` | Formalize and harmonize VFA Color | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-18` | `VFA-1018` | Shared sortedness and multiplicity specification bridges | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#560](https://github.com/VladimirMarko/conaled/issues/560) |
| `VFA-19` | `VFA-1019` | Shared table observations and update laws | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#559](https://github.com/VladimirMarko/conaled/issues/559) |
| `VFA-20` | `VFA-1020` | Resource, extraction and execution source obligations | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#563](https://github.com/VladimirMarko/conaled/issues/563) |
| `VFA-21` | `VFA-1021` | Check narrow FRP imports for the required validation workload | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-22` | `VFA-1022` | Check narrow imports in the finite temporal foundation | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-23` | `VFA-1023` | Shared positive binary key representation adapters | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#563](https://github.com/VladimirMarko/conaled/issues/563) |
| `VFA-24` | `VFA-1024` | Make retention proof imports explicit | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-25` | `VFA-1025` | Identify unexpected recreation of cleaned workspace paths | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-26` | `VFA-1026` | Make remaining proof imports explicit | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-27` | `VFA-1027` | Preserve completed compilation in an optional reviewed recovery companion | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-28` | `VFA-1028` | Recover actual ENOSPC validation failure and establish sufficient local build capacity | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-29` | `VFA-1029` | Recover unavailable fresh-validation execution handles and retain durable outcomes | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-30` | `VFA-1030` | Recover checkpoint035 and restore the pinned execution environment | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-31` | `VFA-1031` | Acquire and verify the pinned toolchain without Nix under the user exception | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-32` | `VFA-1032` | Apply supplied QEMU toolchain setup and resume VFA validation | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-33` | `VFA-1033` | Evaluate a narrow native executable-path adapter to make pinned validation practical | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-34` | `VFA-1034` | Narrow unnecessary foundational Lean imports to reduce validation memory and I/O | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-35` | `VFA-1035` | Bounded native compacted-region random-access advice experiment | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-36` | `VFA-1036` | Restore checkpoint 042 with supplied unified native kit and compact latest-state durability | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-37` | `VFA-1037` | Resume checkpoint057 after workspace wipe with scoped dependency hydration | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-38` | `VFA-1038` | Declare the Nat.size theorem import required by the baseline indefinite-service example | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-39` | `VFA-1039` | Complete narrowed summation imports and isolate continuation after interrupted fresh check | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `VFA-40` | `VFA-1040` | Declare the order dependencies required by temporal Monitor and check remaining consumers | [record](checkpoint-012/books/vfa/records/evidence/tracker/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-0` | `PFDS-10000` | Bootstrap pinned development environment and recoverable checkpoints | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-1` | `PFDS-10001` | Introduction | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-2` | `PFDS-10002` | Persistence | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-3` | `PFDS-10003` | Some Familiar Data Structures in a Functional Setting | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-4` | `PFDS-10004` | Lazy Evaluation | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-5` | `PFDS-10005` | Fundamentals of Amortization | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-6` | `PFDS-10006` | Amortization and Persistence via Lazy Evaluation | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-7` | `PFDS-10007` | Eliminating Amortization | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-8` | `PFDS-10008` | Lazy Rebuilding | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-9` | `PFDS-10009` | Numerical Representations | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-10` | `PFDS-10010` | Data-Structural Bootstrapping | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-11` | `PFDS-10011` | Implicit Recursive Slowdown | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-12` | `PFDS-10012` | Both appendices, thesis conclusions and whole-union integration acceptance | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-13` | `PFDS-10013` | Cross-cutting immutable cell and sharing foundation | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-14` | `PFDS-10014` | Thesis AppendixA suspension extension and evaluation correspondence | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-15` | `PFDS-10015` | Thesis redundant digits1/2/3 and mixed increment/decrement variant | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-16` | `PFDS-10016` | Thesis segmented binomial collections using real-time deques | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-17` | `PFDS-10017` | Persistent execution traces and debit set/multiset accounting | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-18` | `PFDS-10018` | Replace whole-Mathlib FRP imports with their actual dependencies | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `PFDS-19` | `PFDS-10019` | Pure recursive forcing and successful cache reuse | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-20` | `PFDS-10020` | Finite pure cache-write accounting | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-21` | `PFDS-10021` | Persistent logical histories and finite debit accounting foundation | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-22` | `PFDS-10022` | Conditional bounds on actual suspension-body entries and their debit observation | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `PFDS-23` | `PFDS-10023` | Shared potential accounting over ordered and signed additive domains | [record](checkpoint-012/books/pfds/records/research/coverage/tickets.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#564](https://github.com/VladimirMarko/conaled/issues/564) |
| `FDSA-1` | `FDSA-000` | FDSA-000 — Complete pinned FDSA formalization | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-000.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-2` | `FDSA-001` | FDSA-001 — Chapter 1: Basics | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-001.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-3` | `FDSA-002` | FDSA-002 — Sorting | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-002.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-4` | `FDSA-003` | FDSA-003 — Selection | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-003.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-5` | `FDSA-004` | FDSA-004 — Binary Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-004.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-6` | `FDSA-005` | FDSA-005 — Binary Search Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-005.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-7` | `FDSA-006` | FDSA-006 — Abstract Data Types | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-006.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-8` | `FDSA-007` | FDSA-007 — 2-3 Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-007.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-9` | `FDSA-008` | FDSA-008 — Red-Black Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-008.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-10` | `FDSA-009` | FDSA-009 — AVL Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-009.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-11` | `FDSA-010` | FDSA-010 — Beyond Insert and Delete: Union, Intersection and Difference | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-010.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-12` | `FDSA-011` | FDSA-011 — Arrays via Braun Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-011.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-13` | `FDSA-012` | FDSA-012 — Tries | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-012.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-14` | `FDSA-013` | FDSA-013 — Region Quadtrees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-013.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-15` | `FDSA-014` | FDSA-014 — Priority Queues | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-014.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-16` | `FDSA-015` | FDSA-015 — Leftist Heaps | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-015.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-17` | `FDSA-016` | FDSA-016 — Priority Queues via Braun Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-016.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-18` | `FDSA-017` | FDSA-017 — Binomial Priority Queues | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-017.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-19` | `FDSA-018` | FDSA-018 — Dynamic Programming | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-018.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-20` | `FDSA-019` | FDSA-019 — Amortized Analysis | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-019.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-21` | `FDSA-020` | FDSA-020 — Queues | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-020.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-22` | `FDSA-021` | FDSA-021 — Splay Trees | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-021.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-23` | `FDSA-022` | FDSA-022 — Skew Heaps | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-022.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-24` | `FDSA-023` | FDSA-023 — Pairing Heaps | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-023.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-25` | `FDSA-024` | FDSA-024 — Graph Algorithms | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-024.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-26` | `FDSA-025` | FDSA-025 — Knuth-Morris-Pratt String Search | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-025.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-27` | `FDSA-026` | FDSA-026 — Huffman's Algorithm | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-026.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-28` | `FDSA-027` | FDSA-027 — Alpha-Beta Pruning | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-027.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-29` | `FDSA-APP-A` | FDSA-APP-A — List Library | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-APP-A.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-30` | `FDSA-APP-B` | FDSA-APP-B — Time Functions | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-APP-B.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-31` | `FDSA-APP-C` | FDSA-APP-C — Notation | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-APP-C.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-32` | `FDSA-SOURCE` | FDSA-SOURCE — Source inventory and provenance | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-SOURCE.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-33` | `FDSA-X002` | FDSA-X002 — Shared insertion-sort call-count results | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-X002.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-34` | `FDSA-XA01` | FDSA-XA01 — Shared Set/Map contracts and refinement | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XA01.md) | [#559](https://github.com/VladimirMarko/conaled/issues/559) |
| `FDSA-35` | `FDSA-XB01` | FDSA-XB01 — Shared list call counts from Appendix B.1 | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XB01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-36` | `FDSA-XD01` | FDSA-XD01 — Shared difference-list closure observations | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XD01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-37` | `FDSA-XH01` | FDSA-XH01 — Shared exact priority-queue observations and merge | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XH01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-38` | `FDSA-XI01` | FDSA-XI01 — Ordered insertion observation readiness | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XI01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-39` | `FDSA-XL01` | FDSA-XL01 — Shared logarithm bounds | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XL01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-40` | `FDSA-XM01` | FDSA-XM01 — Shared ordinary-list merge observations | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XM01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-41` | `FDSA-XP01` | FDSA-XP01 — Shared ordered and signed potential accounting | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XP01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-42` | `FDSA-XQ01` | FDSA-XQ01 — Shared three-way partition values and source execution | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XQ01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-43` | `FDSA-XR01` | FDSA-XR01 — Shared affine upper recurrence bound | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XR01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-44` | `FDSA-XS01` | FDSA-XS01 — Shared ordered-tree search paths | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XS01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-45` | `FDSA-XT01` | FDSA-XT01 — Shared binary-tree observations and cached folds | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-46` | `FDSA-XT02` | FDSA-XT02 — Shared binary-tree shape bounds | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT02.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-47` | `FDSA-XT03` | FDSA-XT03 — Shared measured whole-tree folds | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT03.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-48` | `FDSA-XT04` | FDSA-XT04 — Shared tree suffix invocation and measured construction | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT04.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-49` | `FDSA-XT05` | FDSA-XT05 — Shared shape-sensitive traversal work | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT05.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-50` | `FDSA-XT06` | FDSA-XT06 — Shared root rotations and cached rebuilding | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT06.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-51` | `FDSA-XT07` | FDSA-XT07 — Shared ordered-tree observations | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT07.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-52` | `FDSA-XT08` | FDSA-XT08 — Shared ordinary leftmost extraction | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT08.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-53` | `FDSA-XT09` | FDSA-XT09 — Braun shape commonality readiness | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XT09.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `FDSA-54` | `FDSA-XU01` | FDSA-XU01 — Shared uniform-permutation minimum law | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XU01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-55` | `FDSA-XU02` | FDSA-XU02 — Shared uniform relative order on a fixed subset | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XU02.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-56` | `FDSA-XU03` | FDSA-XU03 — Shared conditional remaining-order laws | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XU03.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-57` | `FDSA-XU04` | FDSA-XU04 — Shared preceding-count and ordinal-position means | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XU04.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-58` | `FDSA-XU05` | FDSA-XU05 — Shared joint relative orders on disjoint subsets | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XU05.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-59` | `FDSA-XU06` | FDSA-XU06 — Shared fixed-placement and internal-order independence | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XU06.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `FDSA-60` | `FDSA-XW01` | FDSA-XW01 — Shared bounds for accumulated random work | [record](checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/tickets/FDSA-XW01.md) | [#558](https://github.com/VladimirMarko/conaled/issues/558), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `INT-1` | `INT-001` | Cohesive textbook integration | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-2` | `INT-002` | Restore source, pin master, correct setup and save milestone | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-10` | `INT-010` | Combine coherent current VFA/FDSA/PFDS components | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-11` | `INT-011` | Unify shared potential accounting | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-12` | `INT-012` | Connect sorting specifications and implementations | [record](checkpoint-012/books/common/ISSUES.json) | [#560](https://github.com/VladimirMarko/conaled/issues/560) |
| `INT-13` | `INT-013` | Reconcile collection and sequence clients | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-20` | `INT-020` | Finish or integrate additional FDSA draft families | [record](checkpoint-012/books/common/ISSUES.json) | [#559](https://github.com/VladimirMarko/conaled/issues/559), [#561](https://github.com/VladimirMarko/conaled/issues/561) |
| `INT-21` | `INT-021` | Resolve five VFA standalone mathematical drafts | [record](checkpoint-012/books/common/ISSUES.json) | [#559](https://github.com/VladimirMarko/conaled/issues/559), [#560](https://github.com/VladimirMarko/conaled/issues/560), [#563](https://github.com/VladimirMarko/conaled/issues/563) |
| `INT-90` | `INT-090` | Validate exact coherent candidate | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-91` | `INT-091` | Independent whole-scope review | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-30` | `INT-030` | Update pinned upstream master and assess relevance | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-31` | `INT-031` | Account for all three books with honest coverage boundaries | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `INT-32` | `INT-032` | Recover map observations and lawful realizations through OrderedMap | [record](checkpoint-012/books/common/ISSUES.json) | [#559](https://github.com/VladimirMarko/conaled/issues/559) |
| `INT-33` | `INT-033` | Relate FDSA probabilistic runs to actual tape sampling | [record](checkpoint-012/books/common/ISSUES.json) | [#562](https://github.com/VladimirMarko/conaled/issues/562) |
| `INT-40` | `INT-040` | Consolidate current coherent patch for near-term integration | [record](checkpoint-012/books/common/ISSUES.json) | [#558](https://github.com/VladimirMarko/conaled/issues/558) |
| `GH-174` | `GH-174` | Develop compositional data-structure design and optimization toolkits across settings | [record](../../research/data-structure-target-capabilities.md) | [#174](https://github.com/VladimirMarko/conaled/issues/174) |
