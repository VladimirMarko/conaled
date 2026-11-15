# Architecture investigation for textbook integration

Date: 2026-11-13. Read-only source investigation; no Lean execution, source edits,
new proof acceptance or remote writes. This report is planning evidence and must
travel with the coordinator's next durable checkpoint.

## Authority and inspected identities

The governing master is `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`.
Its `AGENTS.md`, README environment/build/parallel-development sections,
`docs/agents/architectural-quality.md`, `docs/agents/domain.md`, `GLOSSARY.md`,
ADR 0001/0002/0010, language direction and preservation-contract inventory were
consulted. The user's exception is local issue/spec tracking persisted in the
checkpoint. Existing source/book review outcomes are historical; this report
does not promote them.

Incoming candidates inspected from recovered worktrees:

- VFA: `eae9e110adc7ba1cc28386448a6deef23e406c13`.
- FDSA: `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe`.
- PFDS: `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5`.

These candidates do not exhaust the incoming evidence: FDSA chapter 4 and XT03
have additional retained streams, and VFA has paper/prototype scopes. The
separate preservation report owns their complete accounting.

## The actual architecture to reuse

The master README expressly permits multiple implementations in distinct modules
and namespaces under explicit contracts. Its language direction rejects both a
universal forced pipeline and treating native Lean propositions as a universal
foreign-foundation interface. Ordinary direct clients must stay usable.

| Need | Existing owner and concrete API | Consequential boundary |
|---|---|---|
| Exact implementation/specification connection | `Squares.lean`: `Rep`, `Square`, `compose`, `Rep.after`, `vertical` | A `Square` retains both implementation and specification. `vertical` allows an explicitly proved extensionally equal middle computation. A total decoder is an assumption, not a default for malformed states. |
| Independent implementations with the same observation | `SquareKit/Combinators.lean`: `synchronized`, `synchronize`, `synchronize_agrees`; `SquareKit/CommaAgreement.lean`: `Exact.agreement`, `agree`, `agree_comp`, `outputs_agree` | Both implementations remain available. Agreement is a subtype with an equality witness; neither decoder must be injective. It proves agreement for selected observations, not state isomorphism or equal costs. |
| More general settings and equivalence | `SquareKit/Comma.lean`: `Obj`, `Hom`, `ops`, `equiv`, `laws`, `fst_laws`, `snd_laws` | Raw operations, hom equivalence, congruence and laws are separate; source laws are required only where used. Do not rebuild an all-purpose container framework to expose this existing capability. |
| Partial/redundant representations | `SquareKit/Relations.lean`: `RelRep`, `RelSquare`, `compose`, `ofSquare`, `witnessSquare`, `witness_compose` | Relations can retain invariants and selected semantic witnesses. A witness presentation is not a license to erase witness data, failure or cost. |
| Representation-independent stateful clients | `Applications/Sequences/AbstractFIFO.lean`: `Ops`, separate `Simulation`, `Simulation.comp`, `reverse`, `client_eq`, `representation_independent`, `runSquare_append` | Operations need no global container class. The simulation preserves each public operation and head observation. Reversal does not supply an inverse on states. |
| Optional compiled surface and extensible operations | `AbstractFIFOSyntax.lean`: `compile_preserves`, `observe_program`; `FIFOExtension.lean`: `old_target`, `old_compile`, `old_observe`, `observe` | Direct clients need not import syntax. New operations require compatibility; old clients are recovered under their old premises. |
| Ordered full sequence and optional summaries/caches | `Applications/Sequences/OrderedSummary.lean`: `summary`, `Valid`, `representation`, `summarySquare`, `batch_decode`, `batch_summary`, List/DList specializations | Arbitrary monoids retain multiplication order. Full decode remains separate from a lossy summary. Invalid caches and summary-only observers must not be confused with full sequence equivalence. |
| Reachable state/representation transport | `SquareKit/ListFusion.lean`: `foldl_reachable`, `foldr_reachable`, `scanl_reachable`; `Applications/Resources/Workload.lean`: `run_invariant`, `run_value_fusion` | Prove invariant closure and the local observation law; reuse the existing induction. Claims are over the actual intermediate trajectory. |
| Resources independent of extensional values | `Applications/Resources/Measured.lean`: `Measured`, `bind`, `reweight_bind`, `erasureSquare`; `Workload.lean`: `run_append`, `reweight_run` | Observations form an additive monoid and need not commute. Value erasure establishes no equality of observations. Tariffs, source primitive counts and machine costs remain distinct. |
| Public amortized FIFO contracts | `Applications/Resources/FIFOContracts.lean`: `Instrumentation.erases`, `Accounting`, `client_bound`, `sequential_bound`, `reobserved_bound` | The accounting potential is existential implementation evidence. Head is explicitly uncharged. Initialization credit cannot be independently spent by two branches. |
| Sorting specifications with retained records | `Applications/Sorting/Stable.lean`: `KeySorted`, `Stable`, `StableSort`, `StableSort.unique`, `StableSort.map` | Key antisymmetry suffices for stable-sort uniqueness, because equal-key occurrence order is retained. Ordinary sortedness plus permutation on noninjective keys does not give this guarantee. |
| Cost-aware realization choice | `Applications/Optimization/Basic.lean`: `minimizers`, `pareto`, `Attained`; `Transport.lean`: `minimizer_image`, `minimizer_transport`, `minimizer_reflect` | Cost agreement, monotonicity, admissibility and target coverage are separate premises. Semantic equality alone does not transport optimality. |

The newer `SquareKit/Institutions/Capabilities.lean` also supplies `Setting`,
evidence-carrying `Connection`, optional `Reflects`, `ProofMap`, exact and
relational `RealizationMap`, and composition laws. Its direct `ofRep`/`ofSquare`
specializations recover ordinary squares. This is relevant if a genuine change
of source judgment/evidence setting is needed; wrapping every textbook theorem
in that layer would not establish Coq/HOL/Lean adequacy and is not justified by
the current clients.

Primary source links for the current architecture:
[master README](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/README.md),
[architectural standard](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/docs/agents/architectural-quality.md),
[language direction](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/docs/language-direction.md).

## Incoming work already follows useful parts of this design

FDSA `Sorting/TopDown.lean` already proves `sortFloorOn_spec` using master's
`StableSort` and proves `sortFloorOn_eq_sortOn` through `StableSort.unique`.
Preserve this connection; do not create a duplicate specification bridge.
FDSA `Sorting/Uniqueness.lean` supplies `sorters_eq_at`, `sorters_eq` and
`sorters_eq_of_multiset`. Its constant-key counterexample explicitly prevents
confusing ordinary key sorting with stable record sorting.

FDSA `Resources/DifferenceListCosts.lean` separates callback creation from
application and already proves `toDList_compose` and `toDList_pushRun` as value
bridges. Its `Rep` quantifies over every supplied suffix, not only `[]`.

PFDS `Sequences/AbstractStack.lean` separates operations and relational laws,
preserves optional head/tail failure, instruments actual primitive invocations,
and composes `appendSquare` with `headSquare`. `SharedList/Observation.lean`
connects shared-cell append/update to list semantics using relational squares;
malformed heaps are not assigned arbitrary total decodings.

PFDS `Search/AbstractSet.lean` reuses reachable fold fusion. Its incoming
`Search/OrderedMap/Interface.lean` supplies the minimal `Ops`/`Laws` map interface,
`bindSquare`, `lookupSquare`, `bindAll_correct`, and `lookup_bindAll`.
I found no preexisting master `AbstractMap` owner to replace: the PFDS map is an
incoming domain extension. Preserve `none` versus `some none`, arbitrary payload
types, and last-write-wins ordering when connecting future tree realizations.

PFDS generalizes `Resources/Potential.lean` instead of adding a parallel
amortized framework. It keeps the old Nat `run_cost_le`, `run_zero_potential`
and constant-budget specializations, adds generic `budget_map` and
`budget_congr_state`, and exposes the final nonnegativity premise for discarding
a signed terminal potential. `SignedPotential.lean` supplies exact savings/debt
identities. Existing `Examples/PotentialTransport.lean` uses the original binary
counter, real reweighting, and ordered noncommutative word observations. These
are important regression clients for the shared generalization.

## Three highest-value integration opportunities

### 1. VFA first-pair preprocessing and FDSA ordinary/stable sorting

VFA `compareSwap_perm` preserves occurrences for an arbitrary Boolean comparator;
it does not require an ordering law. FDSA `sorters_eq_at` makes a complete
ordinary sorter unique under antisymmetry of the relation on the actual records.
Together they should prove that preprocessing by `compareSwap` cannot change
the result of any such complete sorter. A new cross-application theorem can
reuse both public results without inventing another sorting carrier.

Suggested statement, not compiler-checked in this investigation:

```lean
theorem sort_after_compareSwap (r : α → α → Prop) [Std.Antisymm r]
    (f : List α → List α)
    (hf : ∀ xs, (f xs).Pairwise r ∧ (f xs).Perm xs)
    (swap : α → α → Bool) (xs : List α) :
    f (compareSwap swap xs) = f xs :=
  sorters_eq_at r (fun ys => f (compareSwap swap ys)) f xs
    ⟨(hf _).1, (hf _).2.trans (compareSwap_perm swap xs).symm⟩ (hf xs)
```

Retain connected uses with at least the existing first-pivot and floor-split
sorters, mixed duplicates, and the VFA `[3,2,1]` counterexample to whole-list
sortedness after one comparison. This provides interchangeable ordinary
observations only. Preprocessing may change the execution cost, and swapping
equal-key distinct records may change a stable sort's result. The latter is an
essential negative case, not a missing proof to bypass.

### 2. Ordered clients across charged DLists and persistent sequences

Connect FDSA `DifferenceListCosts.toList_toDList`/`build_rep` to master's
`OrderedSummary.summary` and cache laws. A client should obtain the same full
ordered sequence and arbitrary monoid summary through either the measured
builder's existing DList bridge or the established List/DList realization.
Use `summarySquare` or direct shared laws as appropriate; preserve the native
builder theorem over arbitrary suffixes and initial seeds.

Then connect the same independently specified append-and-observe client to PFDS
`AbstractStack.appendRun_correct` and `SharedList.appendHead_correct`/their
relational squares. The optional outputs, representation validity and fuel
bound belong in the relation. A full-summary client on shared heaps needs its
own traversal/observation square; it cannot assume a hidden total decoder.
Keep empty input, duplicate payloads, noncommutative word summaries, an invalid
cache, and a failed operation as discriminating cases.

This is a real common-client integration, not a claim that the three algorithms
have the same primitive count. FDSA creation/application entries, PFDS stack
primitive calls, and shared-cell visits describe different observations.
Retain all of them. Compare or transport costs only after supplying a common
tariff or an explicit bound between the instrumented observations.

### 3. Shared accounting across PFDS and existing/FDSA executors

Integrate the PFDS generalized Potential module with the current master owner,
retaining existing Nat clients and the incoming real/word/signed clients.
Use `run_value_fusion`, `reweight_run`, `budget_map`, and
`budget_congr_state` for common trajectory and observation transport. A concrete
FDSA measured workload can then consume the same local balance theorem; avoid
re-proving the telescope for each textbook.

Preserve exact local/global balances before weakening to cost bounds. State
initial credit and terminal potential, and explicitly prove terminal
nonnegativity when dropping it. PFDS `Persistent/Realization.lean` separately
tracks seen debit support, and `Persistent/Observation.lean` has explicit
boundary/seen variants. Their shared-work allocation and forcing correspondence
must not be replaced by the algebraic signed debt identity. A lazy/persistent
performance claim requires the actual machine/trace connection; finite value
agreement and eager Lean evaluation do not establish that connection.

## Placement, review and limits

Keep implementation-specific mathematics under the existing domain owners;
place universal cross-domain clients in `Examples` as ADR 0010 permits.
Add shared machinery only when these concrete clients expose a repeated missing
obligation. Preserve public entrypoint imports and the full integrated audit.
The pinned code, not dated future-tense research notes, determines what already
exists: e.g. ordered summary laws are implemented despite older planning text.

This investigation does not certify every upstream agent's process or every
statement. The coordinator must reconcile original requirements/findings and
source scopes, review all changes from the fixed current-master baseline, and
obtain exact-candidate build/audit plus independent Standards and Spec review.
Uncompiled integration work remains a draft with validation blocked. Preserve
all excluded/draft mathematics in the source bundle and give it an explicit
local issue owner; preservation in history alone is not completion of useful
library integration.
