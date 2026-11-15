# FDSA architecture and reuse assessment

Assessed 2026-11-02 against conaled `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
This is read-only research for the assigned formalization effort, not an acceptance
review. No build or proof audit was run by this assessment.

## Governing decisions

The user has selected whole-book coverage and local tickets/checkpoints. Those
choices override issue 174's earlier statement that whole-book coverage is not
required and its GitHub-tracker convention. They do not waive the architectural,
statement-review, example, independent-review, or validation requirements.

Keep the existing single domain context and library layout (ADR 0001): reusable
mathematics under `SquareKit`, domain implementations and proofs under
`Applications/<domain>`, checked specializations and compositions under `Examples`.
Book chapters should be an explicit provenance/coverage map, not necessarily the
software module decomposition. There is no reason to add a Lake package or a
mandatory all-purpose container interface.

Current `lakefile.toml` already includes `Applications.+`, `SquareKit.+`, and
`Examples.+`. Each new module must also be reachable from `SquareApplications.lean`.
No new library glob is needed. ADR 0010 and README permit routine candidate
incremental compilation plus exhaustive proof audit; fresh validation is required
for build-tooling/pin changes or cache concerns and is also valuable periodically.
Do not turn historical reports of fresh builds into a fresh-every-chapter rule.

ADR 0001 and `docs/SOURCES.md` exclude downloaded manuscripts and dependency caches
from the deliverable, while requiring source plus a Git bundle. Record manuscript
URLs, dates and content hashes in checkpoints; keep fetched reading copies outside
the conaled deliverable unless a later explicit user decision changes this rule.

## Immediate chapter 1 reuse

The source is the official book PDF dated July 27, 2026. The complete first chapter
is a foundations chapter: types/notation, append associativity, a gcd computation
induction schema, cost-translation conventions, and naive/accumulator reversal.

| Need | Existing interface | Consequence |
|---|---|---|
| List append and algebra | Standard `List`, `List.append_assoc`, length/map/reverse laws | Reuse the standard type and theorem, with checked correspondence; do not create a second list datatype. |
| Accumulator reversal | `Resources.SymmetricCosts.reverseRun`, `reverseRun_value`, `reverseRun_work` in `Applications/Resources/SymmetricCosts.lean` | This already has exactly the book's `itrev` recurrence, returns `xs.reverse ++ acc`, and counts `xs.length + 1`. Reuse it directly; a new copy is unnecessary. |
| Append instrumentation | `Resources.TreeFlattening.appendWithCost`, `appendWithCost_exact` | This existing count is copied cells, `xs.length`, while FDSA counts calls, `xs.length + 1`. Preserve both meanings; an explicit extra-entry-charge adapter and recurrence theorem can connect them. Never silently identify the costs. |
| Value/cost composition | `Resources.Measured`, `pure`, `bind`, `bind_assoc`, `bind_erases`, `reweight_bind`, `erasureSquare` | Values and observations are already separate, and observations need only the algebra required by each theorem. Use these rather than a new writer framework. |
| Asymptotic consequences | `Resources.isBigO_of_nat_bound` in `Applications/Resources/Growth.lean` | Explicit chapter bounds can have standard asymptotic corollaries without another Big-O definition. |
| Euclid induction | Pinned Lean/Mathlib natural-number gcd API must be checked after setup | The book's schema is conditional on the recursive branch and decreases the second argument. Verify exact upstream theorem arguments; do not assume a name or reversed orientation. |

A useful new chapter 1 slice is naive reverse instrumentation in
`Applications/Resources/ListReversal.lean` (or a similarly domain-named module),
with the exact recurrence, erasure to `List.reverse`, exact triangular call count,
quadratic bound, and a connected comparison with the existing accumulator
reversal. A companion `Examples/ListReversal.lean` can retain empty, singleton,
duplicates, arbitrary nonempty accumulator and ordered payload cases. An ordinary
semantic equality proves the two return the same value; a separate cost theorem
must establish the bound and comparison.

For the cost-translation discussion, the source explicitly describes E and T as
metalanguage rather than functions in its logic. A correspondence table and
checked `Measured` composition laws can cover each stated rule without claiming
a full source-language interpreter/compiler proof. If a formal syntax translator
is chosen, scope and validate that as a separate cross-cutting deliverable. Preserve
the zero cost for primitive operations, selected-branch behavior for conditionals
and cases, sequencing for lets, and the call-entry charge. Nonrecursive-call
inlining and the zero-time corner case must not disappear from the coverage map.

Types/notation can be mapped to standard Lean/Mathlib constructions and checked
examples; they need not be reimplemented. Include `Function.update`, `Option`,
products, natural/integer/real coercions, and `Multiset` multiplicity explicitly.
Natural subtraction and coercion to a ring do not commute in general. Avoid
turning the book's discussion of conditional physical running time into a theorem
about actual Lean allocation, stack use or wall-clock time.

## Reuse as later chapters arrive

| Area | Actual current declarations | Caution |
|---|---|---|
| Fold/scan refinement | `SquareKit.ListFusion.foldr_reachable`, `foldr_iff`, `scanl_reachable`, `foldl_reachable`, `scanl_prefix_values` | Validity need only hold on reachable states. Changing accumulator types alone is not a change of mathematical setting. |
| Recursive cross-setting proof | `SquareKit.ListInitial.fusion`; `Types.initial`, `Types.run_eq`, `Types.foldl_reachable`; `Presheaves.initial`, `Presheaves.run_eq`, `Presheaves.foldl_fusion` | #252 already implements the same categorical fusion proof in types and nonconstant presheaves. Earlier research that calls this missing is superseded by `docs/research/recursive-fusion-implementation.md`. It does not transport arbitrary dependent induction. |
| Sequence summaries | `Sequences.OrderedSummary.summary`, `summary_append`, `Valid`, `append_valid`, `batch_summary`, `batch_decode`, List/DList instances | Summary equality is weaker than full ordered sequence equality. No commutativity or inverse is generally available. |
| Sorting semantics | `Applications.Sorting.StableSort`, `StableSort.unique`, `StableSort.map`, `sortOn_spec`, `insertionOn_spec`, `sortOn_eq_insertionOn` | Existing specification separates payloads from keys, retains multiplicity and ties, and avoids ordering the payload. Source recurrence adapters should connect to this contract. |
| Literal merge recurrence | `Applications.Sorting.sourceMerge`, `sourceMerge_eq_merge`, `mergeBy_source` | Shows the existing convention: retain a small source adapter but make public algorithms use standard List operations. |
| Exact and relational refinement | `Squares.Rep`, `Square`, `compose`, `Rep.after`; `Relational.RelRep`, `RelSquare`, composition | No decoder injectivity should be assumed. Invariants and possibly partial relational observations stay explicit. |
| Linear workloads | `Resources.run`, `run_append`, `run_invariant`, `run_value_fusion`, `reweight_run` | Actual state trajectory, not independent per-operation costs at a fixed original state. |
| Amortization | `Resources.run_potential`, `run_potential_exact`, `run_cost_le`, `run_constant_charge`, `initial_potential_matters` | These cover a single trajectory. Branching reuse of old states introduces extra boundary potentials. |
| Queues | `Sequences.AbstractFIFO.Ops`, `Simulation`, `Simulation.run_preserves`, `Simulation.client_eq`, `Simulation.comp`, List/symmetric realizations | Operations and simulation laws are separate; empty queries stay `Option`. Use native interface for ordinary clients. |
| Priority queues | `Search.LeftistQueue.PQ`, `Ranked`, `Heap`, `Valid`, `combineQ_valid`, `insertQ_entries`, `deleteQ_spec`, `rank_size`, `rank_log`; `Search.PriorityInterface.Operations`, `Laws`, `Queue` | Existing priority contract serves a particular search client with keyed coverage. FDSA multiset/meld contracts may require a separate extension; inspect before forcing fit. |
| Random-access trees | `RandomAccess.Tree`, `Perfect`, `Valid`, `fromT_eq_fringe`, `fromRA_toRA`, other access/representation modules | Cached size is not structural size; shallow `invRA` is insufficient for full validity. This leaf-labelled cached tree is not automatically the right representation for chapter 3 binary search trees. |
| Shared ordered binary trees | `Bracketing.Tree`, `fringeSpec`; measured flattening modules | This has leaf labels and binary forks, unlike empty-leaf/node-labelled search trees. Reuse applicable traversals/laws but do not erase structural distinctions to avoid adding a justified datatype. |

## Review pitfalls

1. A source item is covered only when its intended statement and assumptions are
   mapped to a checked declaration (or explicitly classified as notation/prose).
   Existing related theorems do not automatically discharge the source item.
2. Do not report a chapter accepted while required candidate build/audit or either
   independent Standards/Spec review remains open. The local ticket ledger should
   distinguish implementation, checked, review-pending and accepted.
3. Preserve counts versus lists versus multisets versus sets. A set equality loses
   multiplicity and cannot establish permutation or stable sorting.
4. Function-value correctness and source cost equations are distinct obligations.
   Neither implies execution-time claims about a specific compiler/runtime.
5. Do not impose heap, unbounded dynamic allocation, sharing, or retained state on
   every target. A concrete realization may require them under a local contract.
6. For cross-setting claims, cite the actual transported argument and model
   comparisons. A type parameter, monoid parameter, or two encodings in Set does
   not itself reinterpret the logic or recursion.
7. Preserve ordinary Lean interfaces. A chapter client should not need categorical
   syntax unless it requests the corresponding interpreted result.
8. The older #175/#176 assessment tables are useful provenance, not authoritative
   current gap inventories: subsequent accepted modules implement many entries.

## Read-only evidence inspected

`AGENTS.md`, `README.md`, `GLOSSARY.md`, `docs/agents/architectural-quality.md`,
`docs/agents/domain.md`, `docs/language-direction.md`, `docs/SOURCES.md`, ADR index
and ADRs 0001/0010, `docs/research/functional-data-structures.md`,
`data-structure-architecture.md`, `recursive-argument-transport.md`,
`recursive-fusion-implementation.md`, and the Lean modules named above.

The first-chapter reading was supplied by the parallel book-source investigation
at `book-source/chapter01.txt`. No new Lean source or source-policy changes were
made. All implementation suggestions above remain subject to checked elaboration,
statement review, repository validation and the independent review loop.
