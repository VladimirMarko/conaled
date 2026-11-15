# ADWH preview 233: intake and reconstruction assessment

Assessment for [#149](https://github.com/VladimirMarko/conaled/issues/149),
2026-10-26. **Preserve the mathematical development and reconstruct selected
interfaces, shared foundations, cost composition and integration tooling.** The
sampled source does not justify a wholesale rewrite. Several existing generic
results already have independent specifications, reusable proofs and checked
applications that meet important parts of conaled's standard.

The main library is ready for a staged ownership and integration effort. It is
not yet accepted as a conaled library. The checkpoint's kernel experiments
require a separate source selection and validation process. Completing the
sixteen-queens numeral is not a prerequisite for reconstructing the textbook
library.

## Artifact and assessment scope

The owner supplied the uncleaned archive
`/home/vlad/Downloads/adwh-lean-233-transposition-accepted-and-strong-csp-producer.zip`.
It is 67,920,919 bytes, SHA-256
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Its 10,463 entries contain 368,926,304 uncompressed bytes. The original archive
was not changed. Inspection used `/tmp/conaled-adwh-preview-233/`. The complete
artifact is now [preserved in the repository](../history/algorithm-design-haskell/README.md)
as `adwh-checkpoint-233`, with a per-file checksum manifest and successor-snapshot
procedure. Downloads and the temporary extraction are not restoration dependencies.

Source references below are **archive-relative**, bound to that digest.
`L/` abbreviates `project/adwh-lean/`; `E/` abbreviates `next-iteration/`.
Line numbers refer to this exact source. The archive is retained as a repository artifact. The [machine-readable inventory](adwh-preview-233-inventory.json)
records every main-library module, source hash, imports and source counts,
plus the conaled baseline and fresh sample results.

This assessment covers all main-library source files for inventory, import
coverage, static source guards and consistency with supplied records. It
samples actual statements and architecture in folds/scans, thinning, selection
costs, knapsack, bracketing, A*, and queens/checker infrastructure. It does not
review every declaration or independently reconcile the whole textbook. The
original book PDF and complete upstream kernel proof projects are not bundled
(`RESTORE.md:8–16`); preserved correspondence is evidence to retain, not an
independent re-review of those sources.

## What is present

| Area | Contents and disposition |
| --- | --- |
| Main library | `L/ADWH/`: 1,239 mathematical modules, plus `L/ADWH.lean`; 242,728 source lines including the aggregate. Keep this as the reference mathematical baseline. |
| Source correspondence | `project/docs/`, `L/correspondence/`, chapter ledgers and `L/reports/source_inventory.json`. Preserve source variants, corrections, domains and theorem references through migration. |
| Coverage | `project/BOOK-COVERAGE.md` and `L/CURRENT-STATUS.md` record completed scopes for chapters 1–14 and 16. Chapter 15's outstanding literal obligation is the stock Lean sixteen-queens numeral. Chapter 6 retains its accepted groups-three research disposition. |
| Validation machinery | `L/scripts/check.py`, `Audit.lean`, coverage validators and stored reports. There is real source guarding and declaration auditing, not only selected headline theorem checks. Adapt it to conaled's fresh-build and audit ownership. |
| Other project material | The whole `project/` tree contains 4,562 files and 118,626,790 bytes, including experiments outside the main library. Main-library acceptance must not automatically include these experiments. |
| Active and historical experiments | `next-iteration/` contains 5,889 files and 245,285,683 bytes. It mixes mathematical sources, generated/bundled source assemblies, accepted results, failed runs, review records and unfinished successors. Select canonical sources before import. |

The maintained mathematics spans all sixteen chapters: functional programming,
cost analysis, data structures, binary search, sorting, selection, greedy
algorithms, graphs, thinning, segments/subsequences, partitions, memoization,
bracketing and heuristic search. Chapter directories are useful source
coordinates; they are not the intended ownership of every reusable domain
interface. Cross-chapter imports already exist. A migration must preserve
those dependencies and the exact source variants they connect.

The core uses Std and the same Lean 4.35.0 compiler revision as conaled
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). Its optional Mathlib pin is recorded
as historical/not installed in `project/DEPENDENCY-PINS.json`; use conaled's
existing Mathlib manifest for integration. No top-level or original-project
license file was found in the archive filename inventory. Record the original
development's license and preserve the existing upstream notices as part of
provenance intake; the retained con-leche Apache license does not by itself
establish the license of original ADWH files.

## Validation performed here

Fresh static checks found that all **1,240 source hashes and five verification
control hashes** match the supplied successful gate. The supplied source guard
and import-coverage check passed and reproduced the recorded source inventory.
The stored audit contains 83,281 declaration records; reconciling the supplied
coverage against those records resolves all 17,846 selected theorem references.
This establishes consistency of the delivered records, not fresh kernel
acceptance of all those declarations.

A separate fresh build checked:

- `ADWH.Chapter16.HeuristicExamples`, including its search and queue dependencies.
- `ADWH.Chapter14.GeneralizedCost`, including its bracketing dependencies.

Their combined closure contains **20 modules**. Each compiled directly with
Lean 4.35.0, `-j1`, `autoImplicit=false` and `warningAsError=true`, into a new
isolated output directory. `LEAN_PATH` pointed to that directory; no supplied
ADWH objects were reused. The supplied exhaustive-environment audit was then
run with its aggregate import replaced by these two targets. It passed on
**1,953 owned declarations**, permitting only `propext`, `Quot.sound` and
`Classical.choice`. The combined build/audit took 19.734 seconds in this run;
this is a verification observation, not a performance comparison.

No fresh full-library build or kernel-experiment reproduction was run. The
sample establishes current local buildability of those interfaces and their
clients, not acceptance of the entire preview. No Lean source was modified or
imported into conaled during this assessment.

## Preserve, adapt and rebuild

### Generic thinning and optimization: preserve theory, adapt its interfaces

`L/ADWH/Chapter10/Thinning.lean:15–19` separates dominance coverage (`Covers`)
from order-preserving thinning (`IsThinning`). `thinning_map` at line 371,
`ExtensionCompatible` at 402 and `foldWithThinning_refinement` at 486 already
support generic transformations and arbitrary pruning implementations under
explicit laws. These are assets to retain.

The network client uses this theory in `NetworkThinning.lean:88–141`.
`CoinThinning.lean:52` deliberately proves subset-origin and coverage rather
than sublist preservation because merging changes order. A common interface
must preserve this distinction. Thinning's minimum theory is already generalized
to a preorder in `ThinningMinimum.lean:15`, beyond the Int-specific predicate
in `Thinning.lean:416`.

Adapt these contracts to conaled's
[`Optimization.minimizers`](../../Applications/Optimization/Basic.lean),
[`minimizer_transport`](../../Applications/Optimization/Transport.lean), and
[`selectionSquare`](../../Applications/Optimization/Relations.lean).
Dominance coverage can discharge an optimum-transport coverage obligation
when cost compatibility and candidate-origin/admissibility are proved. Coverage
alone is insufficient; representatives must remain admissible original candidates. Set-valued optimum membership must not
erase stronger source-order or tie guarantees. `Option` selectors need a
failure-aware relation or a proved feasible input domain; a total selector
cannot silently discard `none`.

**First cases:** a layered network with no feasible path and empty-input
knapsack, where the empty selection is optimal. General knapsack attainment
uses its finite nonempty candidate enumeration. Preserve maximization through an explicit order
dual or score interpretation. This is a bounded integration with two existing
clients, not a request for a universal optimizing compiler.

### Folds and scans: consolidate duplication without losing generality

`L/ADWH/Chapter01/Lists.lean:26–53` redefines standard list operations and proves
agreement with them. The standard-list equivalences at lines 259/263 also cover
scans. Use standard Lean/Mathlib operations for ordinary clients where exact
hypotheses agree; retain literal source definitions when a derivation or cost
model depends on their execution structure.

The reachable-state fold fusion at `Lists.lean:134` and the restricted fusion
and counterexample in `ScanFusion.lean` have useful generality. Do not replace
them with a stronger uniform homomorphism assumption just to fit an interface.

Conaled's [parallel scan](../../Applications/Parallel/Scan.lean) returns
exclusive prefixes and a final total over a monoid. ADWH's arbitrary-accumulator
scan returns all states including the initial state and requires no monoid.
These are different contracts. Prove a bridge for the monoid multiplication
specialization, then derive implementations through existing `ScanPlan`
correctness. Check both additive naturals and a noncommutative monoid such as
words. Keep the more general accumulator scan available independently.

### Dynamic programming: preserve exact refinement and independent optima

`L/ADWH/Chapter14/GeneralizedCost.lean:79–82` specifies the minimum over every
tree with the required fringe and proves it under coordinatewise monotonicity,
without requiring associativity. `parallel_optimum` at 126 specializes it to
`max`; the failures at 137/142 explain why monotonicity matters. Cached and array
implementations reuse the theorem in `GeneralizedCached.lean:118` and
`GeneralizedArray.lean:399`. This is existing proof transport to preserve.

Knapsack has independent feasibility and optimum predicates
(`Chapter13/Knapsack.lean:64–68`). Its array development already proves exact
recursive/list/array agreement and feasibility/optimality
(`KnapsackArray.lean:257–270`). Extract shared representation refinement and
connect it to exact squares plus an optimum relation. Replacing exact witness
agreement with merely equal optimal values would weaken these results.

The generic `ArrayBatch` mechanism at `KnapsackArray.lean:27–73` is a candidate
for shared reuse, but promote it only after finding a second checked client.
Its right-hand sides read the old row. An in-place implementation requires a
new dependency-order argument; it is not a cosmetic representation change.

### Resource analysis: rebuild repeated composition, retain each model

Thinning instruments relation calls and, separately, guards/constructors/visits
(`L/ADWH/Chapter10/ThinningCosts.lean:12–66`). Knapsack has multi-counter array
work and scalar-tariff executions with erasure proofs
(`Chapter13/KnapsackArray.lean:304`, `KnapsackWork.lean:24`). These are distinct
observations that already support useful mathematical bounds.

A shared instrumented-execution interface should compose results and events,
prove erasure for its combinators, and transport event weights through proved
homomorphisms. Recover both existing thinning and knapsack models as checked
specializations. Preserve branch-sensitive charges, immutable-copy costs and
workload assumptions. Do not replace these with one universal scalar cost or
claim that semantic equality transports complexity. Physical memory, runtime
speed and kernel checking costs require their own realization contracts.

### Search: keep the correctness core; incremental A* is still new work

`L/ADWH/Chapter16/HeuristicCore.lean:34–63` defines independent walks, route
witnesses and global minimum paths. `astar_correct` requires optimism and a
completed run; `mstar_correct` requires monotonicity and zero heuristic at goals
(`HeuristicOptimality.lean:105,252`). Finite-domain termination is separate
(`HeuristicTermination.lean:213`). Exhausted fuel and completed no-goal are
separate outcomes (`HeuristicCore.lean:131`).

The concrete `optimum4_global` and `optimum6_global` applications use those
public results after establishing the heuristic assumptions
(`HeuristicExamples.lean:59–105`). Retain the nonmonotonic failure, cyclic
no-goal case, queue ties and heuristic-only counterexample. This is useful
example-driven evidence already present in the preview.

[#111](https://github.com/VladimirMarko/conaled/issues/111) asks for retained-state
repair after graph updates. Static A* correctness does not deliver that.
Moreover, these source interfaces use Nat costs while #111 specifies positive
rational costs or infinity. The derivation needs an explicit cost/graph adapter
or a justified generalization, update invariants, termination and resource
contracts. Coordinate that work with #109 and #113 without imposing them as
blanket prerequisites for importing static search.

### Checked examples and statement review: repair connections selectively

The examples above already exercise public theorems and meaningful failure
cases. There is no basis for declaring that the preview lacks checked examples.
There are specific connections to improve:

- `Chapter02/BuildEquality.lean:23,127` has an independent `RunCompression`
  relation and `build_equality_iff`. Concrete cases at 158–160 use reduction
  rather than that theorem. Retain their expected lists and connect the
  repeated, separated-repeat and empty cases through the public equivalence.
- `Chapter06/GroupSelectionWork.lean:215` connects measured values to sorted
  rank, but its concrete rank cases at 219–220 use direct decision. Add the
  connection through `complete_work_value` during migration.
- The Garsia–Wachs concrete optimum in
  `Chapter14/SourceExamplesCounterexamples.lean:107–115` has an independent
  optimum proof; also exercise the generic optimized correctness result when
  migrating it. Preserve the independent check.

No false or vacuous theorem was identified in these selected statement reviews.
That is a finding about the reviewed sample, not an exhaustive assurance.
Review each changed statement's domains, quantifiers, assumptions, observation
and public examples during migration. There is no per-declaration example quota.

Keep the Chapter 6 groups-three qualification: actual linear lower and
n-log-n upper bounds do not prove superlinear worst-case behavior. The recurrence
countermodel in `GroupRecurrenceLimits.lean:30–35` refutes an inference, not the
claim about the actual selector. Its accepted research disposition is recorded
in `project/docs/chapter06.md`; it must not become either a claimed theorem or
an invented defect in the completed scope.

## Queens and kernel work: separate reusable mathematics from acceptance status

| Material | Evidence in the preview | Required reconstruction |
| --- | --- | --- |
| Certified numerical endpoint | `E/restricted-nat-checker/source/CertifiedNatChecker.lean:29–32,107–111`: executable endpoint, universal source agreement, parser acceptance soundness. | Preserve the small interface; adapt exact realization to shared contracts and demonstrate a non-queens client. Test protocol behavior separately. |
| Reflection optimization | `E/reflection-proof-corrections/source/FirstRowReflection.lean:21–114` and `E/first-row-reflection/source/FirstRowReflectionSource.lean:50–91`: reflection/permutation laws, first-row sums for `n ≤ 16`, original-source fallback outside the range. | Extract a reusable finite involution/sum argument where justified; preserve Word16 semantics, odd/zero cases and range premises. An all-input fallback does not prove arbitrary-width n-queens correctness. |
| External n16 acceptance | `E/reflection-proof-corrections/RESULTS.md:3–17`: recorded external acceptance, 24 fresh experimental modules and 154 selected reports. Seven original modules supplied 21 prepared objects. | Reproduce the exact source/serialization/execution connection separately. The reported 23.3645 seconds is not a fresh full dependency build and is not a stock Lean numeral proof. |
| CSP normalization and propagation | `E/kernel-strong-csp-source-endpoint/source/SourceBridge.lean:148–199` and `E/kernel-strong-csp-quotient/source/KernelStrongCSPQuotient.lean:19–109`: finite normalization, certificate data/checker/soundness, branch multiplicity and earlier-entry obligations. | Select canonical generic sources, build/audit them and exercise a second finite constraint problem before accepting queens-specific adapters. Preserve duplicate and multiplicity conditions. |
| Latest strong-CSP producer | `E/checkpoint233-current-state.md:41–57`; fixed n8 target in `E/kernel-strong-csp-producer/source/StrongCSPFirstTarget.lean`. Source reviewed, selected closure uncompiled, generated import not supplied. | Treat it as unfinished producer work. Generate and check a small complete certificate before considering n16 scaling. No resource-fit conclusion follows from source review. |
| Installed/GroupChecked integration | Latest checkpoint retains failures in the complete word112 and Interpreter185 selections. `E/kernel-nat-only-installed-guards/bundled/source/KernelNatOnlyInstalledGuards.lean:223–232` explicitly limits the recognizer theorem. | Discharge actual source/export/annotation correspondence, installation/environment invariants and complete checker-success obligations. Accepted prefixes do not accept a failed complete selection. |

The stock theorem
`ADWH.Chapter15.Queens.BitRepresentation.cqueens 16 = 14772512`
and the original Installed/GroupChecked endpoints remain open
(`E/checkpoint233-current-state.md:3–9`). Keep this distinction in #137 and #149.
Generic soundness plus a native process exit is not a kernel proof of the
concrete acceptance premise.

The retained Lean release manifest pins con-leche
`67f04630d88718e81aa4d07ab64501f68f105398` and con-ron
`dd8d8218892c871276b1e569d3decbb368bba1b6`
(`E/lean435-migration/release-CMakeLists.txt:1080–1103`). Compare their exact
contracts with conaled's existing experiments before selecting reuse. Explicit
`SetTheory` premises, successful-run refinements and compiled-binary trust
must remain visible. The historical 30-second/one-core/1-GiB experiments are
recorded conditions, not automatically conaled-wide build constraints.

## Integration tooling and source organization

The preview's audit selects declarations by module origin, including private
names, and checks transitive axioms (`L/scripts/Audit.lean:10–38`). Its Python
gate checks source coverage, forbidden constructs and controls, and fails its
reports on errors (`L/scripts/check.py:120–190,260–367`). Preserve that intent.

The build uses `lake build`, with sequential preparation available, and can
reuse unchanged project objects. Conaled's accepted full check deliberately
recompiles every project module from source into an isolated output directory.
Integration must route the selected ADWH closure through that fresh check,
public-entrypoint coverage and conaled's exhaustive ownership audit. Exercise
existing forbidden-axiom, private/generated declaration and freshness fixtures
against the integrated ownership rules. Agreement of stored reports is not an
alternative to this acceptance gate.

Keep one immutable source baseline and a declaration-level migration map.
Do not copy 245 MB of experiment history into normal library imports or choose
sources by the latest directory name. Separate canonical selected mathematics,
source correspondence, reproducible experiment inputs and historical evidence.
No deletion of supplied evidence is needed to achieve that separation.

Use the current ADR 0001 layout for initial slices: shared constructions in
`SquareKit`, reusable domain libraries in `Applications`, and composition
clients in `Examples`, where appropriate. A workstream label does not establish
a package boundary. Any broader layout change needs its own import/build/audit
migration design. Retain ordinary Lean use without compulsory categorical or
internal-language wrappers.

## Reconstruction sequence and acceptance gates

These are proposed work packages under #149, not claims of completed migration.
They are sized around reusable interfaces and their clients, not chapter counts.

| Order | Work package | Concrete acceptance evidence |
| --- | --- | --- |
| 1 | Preserve and validate the reference source | Record provenance/license and source selection; fresh full main-library build and exhaustive audit; retain chapter scopes, corrections and source hashes. Preserve experiment evidence independently. |
| 2 | Thinning and optimization integration pilot | Recover generic thinning, order-changing coverage and minimum transport through shared interfaces; retain network and knapsack clients, infeasible-network/empty-input/tie cases, and ordinary Lean callers. |
| 3 | Folds/scans and standard-foundation consolidation | Replace only demonstrated duplication; prove the sequential/parallel monoid scan bridge with additive and noncommutative clients; retain reachable-state fusion and its counterexample. Can proceed alongside 2. |
| 4 | DP representation refinement | Connect recursive/list/array optima through exact squares and independent optimization contracts; preserve empty-input behavior, cache invariants, source ties and old-row semantics. Promote common array machinery only with a second client. |
| 5 | Shared resource composition | Derive erasure, event composition and reweighting, recovering thinning and knapsack cost theorems under their original models. Keep semantic, complexity and runtime claims separate. |
| 6 | Static search integration and #111 derivation | Preserve A* minimum/termination clients; reconcile Nat versus rational/infinity costs; then derive retained-state repair with independent update and cost obligations. Do not count static search as incremental A*. |
| Parallel | #137 checker/CSP intake | Select and audit accepted generic sources, preserve unfinished selections separately, add non-queens applications and reproduce the chosen external execution scope. Track stock n16 and validating-kernel completion independently. |
| Expansion | Cover the remaining source families | Use the inventory and chapter ledgers to assign each source result a retained, adapted, replaced-with-equivalence or deferred disposition. Apply statement review and connected examples to each migrated family. No silent loss of coverage. |

**Recommended first implementation:** the thinning/optimization pilot after
reference validation. It offers existing generic theory, multiple clients,
explicit ordering/failure distinctions and a direct bridge to #112. It can
show whether reconstruction improves caller effort and reuse before imposing
one design on the entire book.

Each implementation slice must pass conaled's fresh build and exhaustive axiom
audit and demonstrate reuse through public results. The assessment introduces
no new formal claims. It establishes a source inventory, concrete reconstruction
opportunities and an implementation order; full-library certification and the
migration itself remain work under #149.

## Restricted natural-number checker reproduction

The bounded [checker reproduction and independent client](certified-nat-checker-preview.md)
select the parser/source-agreement route and its complete original prerequisites.
The portable runner preserves original bytes, verifies scoped inverse edits,
rebuilds the isolated closure and audits every safe declaration. This is one
selected route; the report retains `EXT-137-001` and the other experimental
inspection/reproduction obligations explicitly.
