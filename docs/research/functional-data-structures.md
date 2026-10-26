# Functional data structures: design techniques and proof coverage

Assessment for [#175](https://github.com/VladimirMarko/conaled/issues/175),
2026-10-26, under the [toolkit workstream #174](https://github.com/VladimirMarko/conaled/issues/174).

Use ADWH for derivation, Okasaki for persistent representation design, and
Nipkow and collaborators for verification with explicit running-time functions.
The next local work should reuse accepted sequence, fusion, resource and
optimization interfaces. The most immediate missing evidence concerns costs
of alternative realizations and preservation of their assumptions. A new queue
or finger tree is not itself the missing toolkit.

This is a declaration-level audit of selected interfaces relevant to that
choice, not a census of every theorem in conaled, Std, Mathlib or the archived
book. The selected slices cover sequence construction/observation, indexed
update, fusion, amortization, finite maps, algebraic measurement and choice
between realizations. References below distinguish inspected source statements,
existing checked clients and recorded acceptance. No new Lean claims or runtime
measurements are added. Recommendations are research judgments, not accepted
architecture decisions or a finger-tree fit decision.

## Sources and techniques

| Source and inspected version | Reusable technique and why consult it | Proof/evaluation boundary |
| --- | --- | --- |
| Bird and Gibbons, *Algorithm Design with Haskell* (2020), publisher contents/preface | Derive algorithms by equations; §2.4 amortization, chapter 3 sequences/arrays, §§4.3–4.4 trees/dynamic sets, §8.3 priority queues, §9.3 disjoint sets. Its preface directs readers to Okasaki for broader data-structure treatment. | The textbook and supplied Lean reconstruction are separate evidence. The original full book was not re-audited here. [Publisher source][adwh]. |
| Okasaki, *Purely Functional Data Structures*: 1996 thesis, with the expanded 1998 book distinguished | Thesis chapter 3 treats branching persistence and lazy amortization; chapter 4 schedules deferred work; chapter 6 derives structures from numerical representations; chapter 7 uses data-structural bootstrapping; chapter 8 develops recursive slowdown. | These are design methods and mathematical analyses, not Lean proofs. Suspension sharing and memoization matter. The thesis is the inspected primary text, not a claim to have checked every expanded-book chapter. [Thesis][okasaki]; [author's book/thesis comparison][finger]. |
| Nipkow and collaborators, *Functional Data Structures and Algorithms: A Proof Assistant Approach*, PDF version July 27, 2026 | Separate operations, abstraction and invariants; prove correctness and running-time recurrences. Chapters 19–20 distinguish potential bounds from worst-case queue scheduling. | Isabelle/HOL mechanizations accompany the book. §1.5 counts nonprimitive calls with stated simplifications; §1.5.2 explicitly stops short of compiler/runtime/hardware validation. Chapter 19's basic amortization excludes reuse of old versions. [Book][fdsa]. |
| Appel, *Verified Functional Algorithms*, version 2.1 (2026), Preface and ADT chapter | Hide representation invariants behind operation specifications. The table interface and implementations illustrate abstract client proofs. | Rocq/Coq development and exercises; do not count uncompleted exercises as delivered proofs. The table example uses natural-number keys and a default-valued total observation, which differs from optional finite-map lookup. [Preface][vfa], [ADT][adt]. |
| Hinze and Paterson, *Finger trees* (2006), author page and correction | Algebraic augmentation: cached monoidal summaries support sequence splitting. A nested representation combines end operations with concatenation. | The author correction avoids forcing a recursive measured subtree, because that would invalidate the lazy analysis. A Lean value proof would not establish those costs. Full fit, mechanization and license assessment belongs to #178. [Paper and correction][finger]. |
| Piróg, *FizzBuzz in Haskell by Embedding a Domain-Specific Language* (April 23, 2014) | A command representation and interpreter become a fold; representation elimination and higher-order composition connect DSL design to algorithms. | An equational derivation in Haskell, not a machine-checked resource theorem. Finite fold fusion has local reusable counterparts below. [Article][fizzbuzz]. |

Two mechanization patterns are useful without importing a textbook. Isabelle's
`Set_Specs.Set_by_Ordered` derives the `Set` locale from ordered-list observations
and invariant laws. This separates representation-specific proofs from reusable
set laws, while retaining linear-order assumptions. [Theory][setspec]. The AFP
finger-tree entry supplies a verified annotated sequence and monotone splitting;
its landing page lists a BSD license and dated release downloads. Its abstract
is evidence for a mechanization to inspect, not evidence that its correctness
proof establishes the Haskell performance argument. [AFP entry][afp].

Numerical representations therefore already overlap #171; basic potential
accounting overlaps #173. Scheduling and bootstrapping offer additional design
methods, but selecting them requires a consumer and an evaluation model.
Algebraic augmentation and fusion can often be investigated using existing
realizations before introducing a nested balanced tree.

## Revisions and acceptance evidence

The conaled audit baseline is
`f0436a64400aef68ed3ae202e9087acce9a365df`. Local links refer to paths inspected
at that commit. [lean-toolchain](../../lean-toolchain) pins Lean/Std 4.35.0;
the inspected compiler commit is
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. [lake-manifest.json](../../lake-manifest.json)
pins Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679` and Batteries
to `66e469188fe07963e5cf666c7d4433f45b8131c5`. Dependency links below name exact source revisions.

The preserved reference is `adwh-checkpoint-233`, archive SHA-256
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Member hashes below were checked against actual ZIP bytes and the checked-in
manifest. Follow the [archive guide](../history/algorithm-design-haskell/README.md)
and [reconstruction map](adwh-reconstruction-map.json) to locate full source
and migration ledgers. Reading source is not fresh kernel validation.

- [#170](https://github.com/VladimirMarko/conaled/issues/170) and
  [#171](https://github.com/VladimirMarko/conaled/issues/171) are closed. Their
  acceptance comments name `28f312979e6a703bb28d981324d1e669d79bec12`, independent
  reviews, and a fresh 727-module build with exhaustive audit. The symmetric
  ledger selects finite semantics and defers lazy/demand-cost claims; the
  random-access ledger covers its finite semantic module, not its cost modules.
- [#173](https://github.com/VladimirMarko/conaled/issues/173) is closed. Its
  acceptance comment names `dccf3b52645fac2a3bc7261980b6453b27f5f048`, a fresh
  745-module build and exhaustive audit, and all 107 declarations of the
  selected accounting closure. Those commits are ancestors of the audit base.
- These are recorded acceptance results, not builds rerun by this survey.
  The [intake assessment](adwh-preview-233-assessment.md) separately records
  preserved audit reports and a fresh 20-module reference sample. Neither
  accepts every archived chapter. A compiled reference, a supplied report and
  an accepted public reconstruction must not share one coverage label.

## Current contracts and checked clients

Names in each row are qualified by the stated namespace. The tables form one
coverage matrix: this table identifies semantic contracts and reuse; the next
records termination, resource and setting limitations for the same row IDs.

| ID and source | Operations, independent meaning and invariants | Construction/correctness law and existing client | Coverage judgment |
| --- | --- | --- | --- |
| A. [`SquareKit.ListFusion`](../../SquareKit/ListFusion.lean) | Finite foldr/foldl/scanl with arbitrary accumulator types; invariant on reachable states. | `foldr_reachable`, `foldl_reachable`, `scanl_reachable`, `foldr_iff`; [`Sequences.Symmetric.scanl_snocSL_refinement`](../../Applications/Sequences/Symmetric/Prefixes.lean) and `Resources.run_value_fusion` use them. | Reusable representation-change principle, already public. The local commuting law need only hold on reachable states. |
| B. [`Sequences.Symmetric`](../../Applications/Sequences/Symmetric/Core.lean) | End insertion/deletion, head/last, reversal; `fromSL (front,rear) = front ++ rear.reverse`. `Inv` constrains an empty side, not general balance. | `fromSL_toSL`, `fromSL_initsSL`; [`editHead`, `prefixLengths`](../../Applications/Sequences/Symmetric/Observation.lean) compose existing relational squares. [`Examples/SymmetricLists`](../../Examples/SymmetricLists.lean) checks duplicates, malformed pairs and rebalance boundaries. | Accepted realization and reusable semantic consumers (#170); do not infer costs from the weak invariant. |
| C. [`RandomAccess`](../../Applications/Sequences/RandomAccess/Basic.lean) | Cached binary digits, cons/uncons, lookup/update. `Perfect` validates every cache and rank; `Valid` also excludes trailing zero digits; `Inv` starts at rank zero. Meaning is ordered List, with optional indexing and `List.set`. | [`decode_encode`, `encode_decode`, `updateQuery_refinement`, `pushPop_exact`](../../Applications/Sequences/RandomAccess/Representation.lean); [`Examples/RandomAccessLists`](../../Examples/RandomAccessLists.lean) checks malformed caches, carry/borrow and indices. | Accepted finite realization (#171). Shallow `invRA` is insufficient; `Cached` alone does not imply `Perfect`. A proof by decoding alone cannot replace invariant preservation. |
| D. [`Resources`](../../Applications/Resources/Workload.lean) | `run` feeds each operation the preceding actual state; `Measured` carries value plus observation. | `run_append`, `reweight_run`, `run_invariant`, `run_value_fusion`; [`run_potential`, `run_potential_exact`, `run_constant_charge`](../../Applications/Resources/Potential.lean). [`Examples/PotentialAccounting`](../../Examples/PotentialAccounting.lean) includes ordered noncommutative observations and actual counter/symmetric clients. | Accepted reusable accounting (#173), not a queue-specific framework. |
| E. [`Resources.SymmetricCosts`](../../Applications/Resources/SymmetricWorkload.lean) and [`Resources.BinaryCounter`](../../Applications/Resources/BinaryCounter.lean) | Six symmetric operations, with mutation/query observations distinguished; binary increment with positional numeric meaning. State validity is propagated for symmetric semantic refinement. | `measuredRun_abstraction`, `measuredRun_bounds`, `observedWorkload_value`, `observedWorkload_resources`; counter `flipCost_potential`, `totalCost_potential`. Same checked client file as D. | Accepted concrete evidence for D. Another linear-history queue telescoping example would add little by itself. |
| F. [`Optimization`](../../Applications/Optimization/Basic.lean) | Admissible candidates, objective, least-cost choices, Pareto choices, attainment, workload pullback. | [`minimizer_image`, `minimizer_transport`, `minimizer_reflect`, `value_transport`](../../Applications/Optimization/Transport.lean); [`Examples.Optimization.work_optimum`, `storage_optimum`, `positive_not_attained`, `semantic_only_not_optimal`](../../Examples/Optimization.lean). | Reusable assessment/transport laws. Different objectives already choose different matrix plans; equality of values does not certify an optimization. |
| G. [`Resources.Thinning`](../../Applications/Resources/Thinning.lean), [`Resources.Knapsack`](../../Applications/Resources/Knapsack.lean) | Instrument actual relation tests, structural work, array reads/writes/copying. Thinning requires a decidable relation; knapsack supplies its own row semantics. | `thinMeasured_value`, `thinMeasured_calls`, `thinMeasured_work`; `stepMeasured_value`, `stepMeasured_exact`; [`Examples.Resources.row_tariffs`, `copy_charged_without_fits`, `value_equality_does_not_transport_cost`](../../Examples/Resources.lean). | Existing multi-observation and conversion-cost precedents; a new generic cost interpreter should justify why these do not suffice. |

| ID | Termination and cost evidence | Workload/history and setting boundary |
| --- | --- | --- |
| A | Structural induction on finite lists; no allocation or time bound follows from fusion equality. | Ordinary Lean types/functions and equality. Changing accumulators is representation variation; internal transport of induction remains a separate obligation. |
| B | Finite recursion; `dropWhileSL` uses raw represented length descent. Cost evidence for selected operations is E. | Finite lists only; lazy/infinite prefixes, continuity and productivity remain archived. Exact sequence order and multiplicity are retained. |
| C | Structural cached-tree/digit recursion; canonicality uses decoded-length induction. No accepted lookup/end cost theorem in #171. | Persistent values are available semantically, but no arbitrary branching-history amortization follows. Set-based parametric element types are not transport to another mathematical setting. |
| D | `run` recurses on the operation list. Composition/reweighting uses additive monoids, without commutativity; potential laws use natural-valued costs/potentials and explicit local inequalities. | A single state trajectory. Reusing old states creates extra runs and extra boundary potentials. A homomorphic observation map preserves composition; a bound additionally needs monotonicity. |
| E | Counter counts changed bits; symmetric source charge and instrumented structural visits are separate. `rebalanceRun_work` is `2 * xs.length + 3`, before outer deletion dispatch. | Finite sequential histories. Structural visits do not establish machine time, allocation, sharing, parallel depth or retained memory. |
| F | Specification-level results; selection is noncomputable where choice is used, not a terminating search algorithm. | Preorders suffice for minimizers; full transport requires admissibility, cost agreement, monotonicity and dominating coverage. Infimum transport needs stronger preservation. These are explicit maps between ordinary mathematical models, not an internal-language transport of arbitrary proofs. |
| G | Finite recursive instrumented executors with value erasure and count/bound proofs. | Unit relation calls and tariff-weighted observations differ; primitive implementation cost must be supplied. Copy charges are modeled, not measured allocator behavior. |

Existing [`Squares.Rep`/`Square`](../../Squares.lean) and
[`Relational.RelRep`/`RelSquare`](../../SquareKit/Relations.lean) provide the
composition seams used above. Their equality and relational contracts preserve
different information; neither supplies cost improvement by itself. This follows
[ADR 0002](../adr/0002-relations-and-synchronization.md) and
[ADR 0007](../adr/0007-incremental-and-enclosure.md). The
[language direction](../language-direction.md) requires explicit support for
reasoning in distinct settings, beyond parameterizing a representation in Set.
The audit does not establish that the finite-list proofs above already transport
to, for example, a sheaf-internal language with its own recursion principles.

## Preserved claims worth adapting, not recreating

All paths in this table are under `project/adwh-lean/ADWH/` in checkpoint 233.
Namespaces are `ADWH.Chapter02.Amortized` or `ADWH.Chapter03.<filename>`.
The cited [manifest](../history/algorithm-design-haskell/checkpoint-233.files.sha256)
and [module map](adwh-reconstruction-map.json) provide full provenance.

| Source member and exact SHA-256 | Inspected declaration and assumptions | Relation to accepted code / remaining obligation |
| --- | --- | --- |
| `Chapter02/Amortized.lean`, `1c4a6678ac6d8dcca48a6978a1d3bf3b87adc27744dd3fa365fa5801bd556cb8` | `run_potential` sums a local natural-valued potential inequality along actual transitions; `initial_potential_matters` prevents dropping the initial boundary. | Reconstructed by D and E; [107-entry ledger](adwh-potential-accounting-ledger.json) takes precedence over the map's coarse “partial reconstruction” module label. No new accounting framework needed. |
| `Chapter03/RandomAccessLookupCosts.lean`, `c1df20833c4dd42ce1ae64a584a4b63596b29e3202e24fd14c10104d5e3e0568` | `fetchRARun_refinement`, `fetchRARun_log_bound` under `Inv`; bound is `2 * (fromRA ds).length.log2 + 3`. `sparse_fetch_cost` exposes long zero-digit prefixes at index zero. | Untouched reference, not covered by #171. Reuse C semantics and D instrumentation. Preserve the distinction between a bound in total length and an invalid uniform bound solely in query index. The archived correspondence hash disagrees with these actual source bytes; inspect current member statements, not that stale correspondence. |
| `Chapter03/RandomAccessEndCosts.lean`, `26bdb3a5f21959ffa672adf502b020d20f05d1a9449a2904ca26b710e016fb7c` | `bits_consT` links carrying to binary increment; `pushManyRun_potential`, `full_drain_linear_bounds` handle separate histories. `mixed_fullDigits_exact` charges `n * (2 * p + 2)` for repeated push/pop cycles; `no_uniform_mixed_charge` quantifies any natural-valued potential and constant charge. | Untouched reference. Separate push and drain bounds must not become a mixed-operation constant bound. This is a useful counterexample even for linear histories, independent of branching persistence. |
| `Chapter03/Arrays.lean`, `6bd6f2b7e674814271f1e9dcf5bbed9486d59cc06bcbb8e6239a76c5c47310fb` | `lookup_write`, `accum_lookup`, `accum_append` retain ordered repeated updates to bounded `Vector` storage; `IndexRange`/`checkedAccum` represent invalid indices explicitly. `bulkRun_exact`, `separateRun_exact`, `initialization_is_not_free` count modeled copy/update work. | Untouched reference. Reuse upstream Vector laws and G's measured copying. Generic array reconstruction is not already supplied merely because an accepted knapsack client uses arrays. A cost bound needs a stated copying model, not extensional `copy_value`. |

The [symmetric-list ledger](adwh-symmetric-lists-ledger.json) and
[random-access ledger](adwh-random-access-lists-provenance.tsv) already map
individual accepted semantic declarations. Their source hashes and selected
claims need not be duplicated into another migration ledger. Wider archived
AVL, priority-queue, disjoint-set and lazy-domain families remain discoverable
through the module map; they were not declaration-audited by this focused study.
An absence from this table is not evidence that no such theorem exists.

## Pinned Lean, Std, Batteries and Mathlib reuse

These are inspected upstream declarations, not new public conaled adapters.
The links pin source rather than relying on current online API names. Local
consumers are identified only where actually inspected.

| Interface and pinned source | Exact reusable contract | What it does not supply |
| --- | --- | --- |
| Lean `Vector.getElem_set`, `Vector.toList_set`, [Init/Data/Vector/Lemmas.lean][vector] | Bounds-indexed updates agree with ordinary indexed observations and List updates. No element equality is needed merely to update by a natural index. | Physical in-place mutation, constant runtime, copy-on-write behavior and branching-retention bounds. The archived Arrays slice uses Vector; this is not itself a public reconstruction. |
| Std `TreeMap.getElem?_insert`, [Std/Data/TreeMap/Lemmas.lean][treemap] | Under `TransCmp cmp`, lookup after insertion branches on `cmp k a = .eq`. | Equality of keys in the host type unless comparator assumptions justify it; a cost proof for a chosen workload. Do not silently replace comparator equivalence by Lean equality. |
| Std `HashMap.getElem?_insert`, [Std/Data/HashMap/Lemmas.lean][hashmap] | Under `EquivBEq` and `LawfulHashable`, lookup branches on Boolean key equality. | Worst-case constant lookup or a hash-distribution model. No new conaled map client is claimed here. These maps are candidate reusable realizations once a finite-map consumer is selected. |
| Batteries `DList.invariant`, `DList.append`, `DList.toList_append`, [Basic][dlist-basic] and [Lemmas][dlist-lemmas] | Functions constrained to append a fixed prefix; composition implements append and observation preserves it. | The source's complexity comments are not resource proofs. Repeated materialization and closure evaluation need their own workload model. |
| Mathlib `Batteries.DList.listEquivDList`, [Data/DList/Instances.lean][dlist-equiv] | List/DList equivalence transports the traversable structure and laws. | A verified speedup, or changing the ambient mathematical setting. This is a concrete example of already available law transport across representations. |
| Mathlib `FreeMonoid.lift`, `FreeMonoid.lift_ofList`, [Algebra/FreeMonoid/Basic.lean][free] | Maps from generators extend to monoid homomorphisms; observation is the ordered product of mapped elements. A monoid suffices, with no commutativity. | Cached-summary maintenance, split-predicate monotonicity, balancing, or summary-computation costs. `Examples/PotentialAccounting.lean` already uses free-monoid observations to check order sensitivity. |

These interfaces support using existing structures before designing new ones.
Neither a common lookup signature nor a shared monoid erases the different
validity/equality/resource premises. A map adapter should discharge those
premises once and expose its semantic relation to ordinary clients.

## Ranked studies and follow-up scopes

The ranking weighs available checked consumers, reusable mathematics and
proof obligations. It is an implementation-planning judgment, not a timing
estimate or a choice of canonical representation.

| Priority | Study and existing consumer | New reusable result / approach | Effort and assumptions |
| --- | --- | --- | --- |
| 1 | **Compare indexed-update realizations.** Start with C's `updateQuery` and standard List semantics; adapt preserved lookup/end-cost evidence. | Reuse C and D; compare List versus cached digits under explicit query/update traces, charge conversion, and connect the objective to F. Preserve sparse-index and mixed push/pop counterexamples. | Bounded adaptation with existing semantic clients, but instrumented recursion and state simulation still need proofs. Fixed total length simplifies updates; end operations change the workload invariant. This stays within #149 reconstruction ownership. |
| 2 | **Extract ordered-summary/fusion obligations using existing realizations.** B's prefix-length and endpoint consumers supply actual observations; DList provides another representation for append-heavy variants. | Reuse A and `FreeMonoid.lift`; isolate summary correctness and homomorphism laws before deciding whether caches are useful. Use a noncommutative summary as well as length; retain order. | Moderate semantic work; cached maintenance and resource claims are additional work. Prefix materialization cannot be declared cheap because a final summary is cheap. #176 should decide which variation justifies a shared interface. |
| 3 | **A scheduling or branching-history study, only for a demonstrated requirement.** E supplies a linear-history baseline. | A plain queue/potential proof mostly repeats #173. A worst-case schedule or explicit shared evaluation graph could add a new proof principle, with a counterexample to spending a potential repeatedly across branches. | Larger evaluation-model obligation. No inspected compiler client currently demands real-time queue latency; select one before implementation. Prefer extending D, rather than hiding a second executor in a queue module. |
| 4 | **Finger-tree fit assessment, then an optional realization only if justified.** Use ranked studies 1–2 as simpler comparators; no confirmed finger-tree consumer is claimed. | Candidate reusable pieces are measured sequence laws and search qualifications, not a mandatory central container. | Nested recursion/termination, balancing, cached measurements, predicate domains and lazy cost arguments add obligations. #178 must apply accepted #176/#177 findings before recommending implementation. |

A finite-map adapter is a reserve study: Std already supplies ordered and hashed
realizations, so it may expose useful comparator/equality differences at lower
implementation cost than a new map. This audit did not identify a checked
client that needs both. Do not invent a compiler requirement to elevate it above
the connected sequence clients.

Concrete handoff to [#176](https://github.com/VladimirMarko/conaled/issues/176):
compare two approaches, ordinary representation contracts plus reachable fusion,
and an explicitly interpreted construction in the existing internal-language
machinery. Start from A–C and the ordered-summary proposal. List which induction,
recursion, equality, decidability and product assumptions the argument actually
uses. Produce a bounded cross-setting example or state the missing interpretation
obligation. Require replaceability without importing a chosen tree's internals;
List/DList equivalence alone does not satisfy this cross-setting test.

Concrete handoff to [#177](https://github.com/VladimirMarko/conaled/issues/177):
reuse D–G for two explicitly instrumented indexed-update realizations; define
workloads and conversion costs, retain reachable-state conditions, and distinguish
ordered observations from numeric bounds. Investigate how differing query/update
patterns change the comparison without asserting a winner in advance. Keep
branching reuse, sharing, primitive arithmetic costs and retained memory as
separate obligations; preserve the archived mixed-operation counterexample.
Any eventual bounded reconstruction belongs under #149 as well as this workstream.

Concrete handoff to [#178](https://github.com/VladimirMarko/conaled/issues/178):
after those assessments are accepted, compare measured sequences against the
simpler realization meeting the same operations. Inspect dated mechanizations,
licenses and actual correctness/cost theorem scope; account for the author
correction and the cost of computing summaries. A justified narrow, defer or
reject decision remains valid. This survey supplies inputs, not that decision.

[adwh]: https://assets.cambridge.org/97811084/91617/frontmatter/9781108491617_frontmatter.pdf
[okasaki]: https://www.cs.cmu.edu/~rwh/students/okasaki.pdf
[fdsa]: https://fdsa-book.net/functional_data_structures_algorithms.pdf
[vfa]: https://softwarefoundations.cis.upenn.edu/vfa-current/Preface.html
[adt]: https://softwarefoundations.cis.upenn.edu/vfa-current/ADT.html
[finger]: https://www.staff.city.ac.uk/~ross/papers/FingerTree.html
[fizzbuzz]: https://themonadreader.wordpress.com/wp-content/uploads/2014/04/fizzbuzz.pdf
[setspec]: https://isabelle.in.tum.de/library/HOL/HOL-Data_Structures/Set_Specs.html
[afp]: https://isa-afp.org/entries/Finger-Trees.html
[vector]: https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Data/Vector/Lemmas.lean
[treemap]: https://github.com/leanprover/lean4/blob/v4.35.0/src/Std/Data/TreeMap/Lemmas.lean
[hashmap]: https://github.com/leanprover/lean4/blob/v4.35.0/src/Std/Data/HashMap/Lemmas.lean
[dlist-equiv]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/DList/Instances.lean
[free]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/FreeMonoid/Basic.lean
[dlist-basic]: https://github.com/leanprover-community/batteries/blob/66e469188fe07963e5cf666c7d4433f45b8131c5/Batteries/Data/DList/Basic.lean
[dlist-lemmas]: https://github.com/leanprover-community/batteries/blob/66e469188fe07963e5cf666c7d4433f45b8131c5/Batteries/Data/DList/Lemmas.lean
