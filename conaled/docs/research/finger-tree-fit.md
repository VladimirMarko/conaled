# Finger trees as an optional realization

Assessment for [#178](https://github.com/VladimirMarko/conaled/issues/178),
2026-10-29. **Defer a finger-tree implementation commitment.** Use
[#239](https://github.com/VladimirMarko/conaled/issues/239)'s bounded plain/cached
append-query comparison first. Reconsider a tree when a client needs repeated
concatenation and position-based splitting, with an explicit evaluation model.
This decision does not reject finger trees or require #239 to become a universal
container interface.

The accepted [architecture assessment](data-structure-architecture.md),
[resource assessment](data-structure-resource-contracts.md) and
[target comparison](data-structure-target-capabilities.md) supply the relevant
seams. The present source inspection used local baseline
`23c64fc05cc37e5707c5bc371c736ea3e254fab1`. No Lean declaration, upstream proof
rebuild, runtime benchmark or new cost theorem is claimed here.

## Paper, correction and mechanizations

Hinze and Paterson's [2006 paper][paper], §§3–4, combines nested 2–3 structure,
ordered monoidal annotations and predicate-guided splitting. Its persistent
amortized deque argument relies on lazy evaluation; concatenation and splitting
have logarithmic bounds relative to the smaller side, under its model.
Measurement-operation counts are not arbitrary monoid runtime costs.
The [author correction][correction] changes measured construction: using `deep`
on a recursive result forces that result to obtain its annotation. The corrected
left insertion computes the new annotation from the inserted measure and old
cached total; corrected `deepL` similarly avoids forcing the new recursive tail
merely to measure it. Value equality alone does not validate the forcing schedule.

The following are inspected sources, not imported dependencies. Source identity
and licensing metadata are recorded to make later reuse reviewable; no code was
copied into this repository.

| Mechanization and source identity | Inspected correctness scope | Evaluation, cost and reuse limits |
| --- | --- | --- |
| Nordhoff, Körner and Lammich, [AFP Finger Trees][afp], Isabelle2025-2 archive dated 2026-02-06; [archive][afp-release] SHA-256 `920741b4abd3e2e1bd9f595a2399fef3d6ff9976e2e13069c4aefd1361828e6a`; entry declares BSD license | `FingerTree.thy`: raw nodes/tree, separate level/cache invariant, invariant-hidden wrapper, sequence refinement, append, folds and qualified split. `splitTree_correct` requires right-extension monotonicity, false initial predicate and true total predicate. Annotation type requires `monoid_add`, not commutativity. | Complexity appears in documentation, not an instrumented execution or amortization proof found in the inspected theory. `Test.thy` exports Haskell, OCaml and SML. `nlcons` calls `deep` on its recursive result, and `deep` reads that result's measure: the author's correction therefore remains an evaluation obligation. Generated value-correct code alone does not establish the paper's persistent bounds. |
| Sozeau, [Dependent Finger Trees][coq], tag `v8.10.0`, commit `5906d88f7096c6c6d421b81336fb344a4e2ec688`; `description` and `extraction/ml/README` declare LGPL without a version there | `DependentFingerTree.v` indexes trees by their measurement, with polymorphically recursive insertion, mutually recursive concatenation and boundary-qualified split results. The archive has sequence, priority-queue and rope wrappers. | `FingerTree.v` contains active `Admitted` proofs for `view_right_size` and `split_size`; the module wrapper has corresponding admissions. `DependentSequence.v` declares `subsetT_eq_compat` as an axiom. These observations prevent treating the entire archive as an admission-free proof dependency. Extraction files target OCaml and Haskell; no operational cost/debit theorem was found in the inspected core and extraction files. |

The AFP evidence is useful for separating a regular raw representation from
its invariant; the Coq evidence shows obligations associated with indexed nested
recursion. Neither inspection establishes an exhaustive axiom audit, build
compatibility with today's tools, or compiler/runtime cost preservation. A later
port must inspect the exact dependency closure of each reused claim. Local
proof-audit policy still applies; upstream admissions are not an exception.

## Separate the reusable laws from the tree

| Concern | Reusable part and existing owner | Finger-tree-specific obligation |
| --- | --- | --- |
| Meaning | Ordered sequence observation; empty/append laws; independent client replies. #185 owns ordinary ordered-summary/cache semantics. | Flatten nested nodes without changing order or multiplicity. |
| Measurement | Ordered fold into a monoid; cache validity and homomorphism laws. No commutativity or inverses required. | Every digit, node and spine cache must agree with the flattened content. |
| Shape | A representation may expose an invariant rather than encode all proofs in values. | Digit bounds, equal subtree levels, rebuilding after views, and concatenation's node packing. |
| Search | An independently specified partition/crossing relation and explicit predicate domain. | Skipping cached subtrees must preserve that relation; balancing alone proves nothing about predicate behavior. |
| Execution | `Resources` measured transitions, erasure, workload composition and qualified optimization. | Actual forcing, allocation, sharing and reconstruction costs for the selected implementation. |

An order-sensitive diagnostic is the free monoid of Boolean words, with
`measure a = [a]`. The summaries of `[false,true]` and `[true,false]` differ.
It detects reversed concatenation or cache updates that a length-only example
would miss. Its summaries grow with the history, so this example is for semantic
coverage, not a constant-space cache claim. Parity is finite but does not support
a first-crossing search merely because it is a monoid.

A useful future *first-crossing* contract, stated independently of any tree,
would return `l, x, r` with `xs = l ++ [x] ++ r`, false predicate on the
accumulated left summary and true predicate after `x`. Require false initial
and true final predicate, plus monotonicity under the reachable right
extensions when the client needs the earliest crossing. A global condition
`p u → p (u * v)` is sufficient, but a workload invariant may justify a weaker
reachable condition. Empty/no-crossing input needs an explicit result policy.

The paper's weaker crossing contract does not require a unique or earliest
crossing; its total wrapper has endpoint exceptions. Do not replace that contract
with unconditional first-match semantics. For a negative example, unit measures
and predicate “the accumulated length is odd” yield false, true, false, true
along three elements. Multiple crossings exist. A tree may skip an earlier one;
a client asking for the first cannot reuse mere crossing evidence.
For positive positional search, `p k := i < k` on natural accumulated lengths is
right-extension monotone; selection additionally requires `i < xs.length`.
These are proposed specification cases, not added formal results.

## Mathematical setting and ordinary clients

The immediate construction is ordinary Lean mathematics over finite inductive
values: products, sums, lists, a monoid, Boolean predicate evaluation, and
induction/recursion with termination evidence. A monoid parameter changes the
annotation interpretation within that setting. It does not transport the nested
datatype, induction principle or evaluation semantics into another setting.

[The architecture assessment](data-structure-architecture.md#assumptions-that-cannot-be-hidden)
identifies a separate recursive-interpretation gap. A cross-setting tree would
need the relevant datatype/initial-algebra construction, admissible recursive
reasoning, and preservation of the cache and observation relations. #185's
Set/presheaf reassociation example does not supply those proofs. Any demonstrated
shared-preservation mismatch belongs to #235; a universal tree or capability
signature is not justified by this assessment.

Actual local consumers include
[`Symmetric.prefixLengths`](../../Applications/Sequences/Symmetric/Observation.lean)
and [`AbstractFIFO.client`](../../Applications/Sequences/AbstractFIFO.lean).
The former can observe length without retaining all prefixes; the latter already
runs against List and valid symmetric lists. Neither needs general split or
concatenation. #239 adds explicit append/summary/full-history clients, also
without those operations. #227's durable queries may eventually motivate indexed
search, but that is an assessed requirement, not an existing tree consumer.

For these clients, a future finger-tree adapter should provide ordinary
operations and observation/invariant preservation premises. Client proofs reuse
[`run_value_fusion`](../../Applications/Resources/Workload.lean), relational
composition, and #185 summary laws; they need not mention digits or nested nodes.
Only clients that actually use split need a split contract. If changing a
representation makes the client redo structural induction, the adapter has not
yet delivered the intended reusable proof boundary.

## Targets and comparisons under the same requirements

| Target | Finger-tree feasibility | Simpler realization of the selected append/query contract |
| --- | --- | --- |
| Growing retained memory | Allocate/rebuild nodes, read ordered fields and cached measures. Persistent bounds additionally require an appropriate suspension/shared-evaluation model; retention/reclamation needs its own accounting. | Plain or cached sequence with the same full-history observation; existing symmetric lists suffice for FIFO use. |
| Fixed slots without allocation | Dynamic unbounded nodes are unavailable. A bounded arena could be another implementation, but must prove capacity, index validity, temporary workspace and failure behavior. | #239's bounded Boolean buffer and optional parity cache, admitting only capacity-safe histories. |
| No state between interactive calls | Cannot preserve arbitrary earlier appended values without an external witness, independently of representation. | No realization of the unchanged full-history service. A pure batch supplied the complete history is a different contract. |

The last two boundaries reuse #238's arguments. No payload equality is needed
for append/fold. Predicate evaluation is needed for split; deduplication in a
durable service separately needs identity equality. An allocator, lazy thunk or
persistent host value is not a durability primitive; #226 owns crash behavior.

Compare explicit workloads, not names of containers:

- For `n` appends followed by `q` summaries, retain the same ordered history in
  both candidates. #177's model gives plain query work as a sum over queried
  lengths; caching exchanges that work for per-append maintenance and reads.
  A tree has no established advantage over the simpler cached candidate for
  this workload. Full-history export still needs output work. Charge conversion
  from an already-built sequence before claiming a benefit.
- For a FIFO word using enqueue/delete and a final head, reuse the actual
  [FIFO comparisons](../../Examples/FIFOContracts.lean). Do not replace a
  measured symmetric-list bound with an unproved finger-tree bound. A queue-only
  client cannot justify paying for split/search proof obligations by itself.
- A discriminating *future* workload would repeatedly concatenate existing
  chunks and split near varying positions while preserving full ordered output.
  A List adapter implements the same contract using append and take/drop;
  its traversals form the baseline. The tree may reduce structural visits, but
  the comparison must include conversion, measurements, predicate evaluations,
  rebuilding and output. This workload is not currently an accepted consumer
  requirement, so it is a reopening criterion, not a new implementation ticket.

Different resource objectives can leave candidates incomparable: a retained
index or cached measure may trade storage for query work. Follow #177's restricted
candidate and Pareto distinctions. No measured runtime result ranks the choices
here, and no candidate is asserted universally best.

## Why the small implementation is not a small proof commitment

The source-based work divides into three deliverables:

1. **Semantic realization.** Choose indexed nested types or regular raw trees
   with a level invariant. Prove rebuilding, both-end views, concatenation,
   cache consistency and independent sequence refinement. Recursion changes
   element level; concatenation and split need explicit decreasing arguments
   and associated induction principles. Existing mechanizations are examples
   of different proof organizations, not automatic Lean translations.
2. **Abstract resource development.** Instrument the actual recursion and
   compute measurement/predicate costs. For eager execution, prove the bound
   that model supports. To claim persistent amortized bounds, model suspended
   computation, forcing and shared payment; #177's linear potential theorem
   cannot spend one credit across multiple branches. A function-valued thunk
   alone does not specify memoization. A bounded-cost monoid operation and a
   growing word summary must remain distinct interpretations.
3. **Runtime realization.** Relate the semantic/cost model to target allocation,
   evaluation, sharing and numeric representations, then measure if performance
   is claimed. Neither Lean termination nor extracted functional correctness
   certifies this boundary.

This is an obligation inventory rather than a time estimate. The corrected
forcing dependency and absent accepted branching-cost model are concrete reasons
not to schedule a full semantic-plus-performance port as a small task.

## Decision and reopening criteria

Defer the tree and proceed with the already-scoped #239 experiment after #185's
relevant ordinary laws. That case tests client proof reuse, capacity restrictions,
cache costs, conversion and negative observations without nested balancing.
No new finger-tree formalization issue is justified now.

Reopen when an identified client requires concatenation/splitting beyond the
simpler interface and its workloads support a useful comparison. The new issue
must then name two realizations under one independent contract, retain ordered
and noncommutative examples, state split/search premises, choose eager or modeled
lazy execution, and separate semantic acceptance from cost and runtime claims.
It must require statement review and connected checked applications for every
formal claim, independent Standards/Spec review, a fresh build and exhaustive
proof audit. Cross-setting recursive interpretation, persistent sharing costs
and physical backends remain explicit open work. Finger trees stay optional;
no library, compiler or internal-language client should be required to use them.

[paper]: https://www.staff.city.ac.uk/~ross/papers/FingerTree.pdf
[correction]: https://www.staff.city.ac.uk/~ross/papers/FingerTree.html
[afp]: https://isa-afp.org/entries/Finger-Trees.html
[afp-release]: https://isa-afp.org/release/afp-Finger-Trees-2026-02-06.tar.gz
[coq]: https://github.com/rocq-archive/finger-tree/tree/5906d88f7096c6c6d421b81336fb344a4e2ec688
