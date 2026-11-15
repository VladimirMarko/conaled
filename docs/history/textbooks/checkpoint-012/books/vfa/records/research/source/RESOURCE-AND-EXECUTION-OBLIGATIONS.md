# VFA resource, representation, and execution obligations

Read-only source audit, 2026-11-02. This supplements `SOURCE-COVERAGE.md` and
the declaration inventories; it neither implements algorithms nor accepts or
closes chapters. All optional/advanced exercises remain in scope. References
below are exact lines in the pinned release under `reference/vfa/vfa/`, unless
a conaled path is given. The release identity and per-file hashes are in the
existing inventories; preserve those inventories unchanged.

## Evidence required

- **T — checked theorem:** mathematical semantics, representation bridges,
  termination measures, structural counts, bounds, and counterexamples. A
  measured algorithm must erase to the actual source algorithm; an unrelated
  cost recurrence is insufficient. State input size, primitive costs, invariants,
  initial state, and whether a bound is worst-case, amortized, or expected.
- **E — executable evidence:** run the requested executable workloads and
  preserve commands, compiler/runtime/target, seeds, inputs, correctness checks,
  timing boundaries, repetitions, results, and failures. Measurements establish
  observations about that setup, not a universal complexity theorem.
- **L — language adaptation:** explain and demonstrate the Lean counterpart of
  extraction, module abstraction, transparency, decisions, and proof erasure.
  A language-mechanics explanation is not a compiler-correctness theorem.
- **Q — qualification/correction:** do not translate an overstatement into a
  false theorem. Retain the source pointer, prove the meaningful conditional
  claim or counterexample where applicable, and state the corrected scope.

An executable test or native evaluation must not become an axiom shortcut in
the proof audit. Keep kernel-checked examples and measurements separate. The
book's statements that Coq has no cost model mean that these chapters did not
provide one; they do not prevent an explicit measured model in Lean/conaled.

## Chapter coverage beyond named declarations

| Chapter and exact source pointer | Required treatment |
|---|---|
| **Preface**, `Preface.v:6–15,31–36` | **L/Q:** explain the Lean prove/compile/run path and its trust boundary. The introductory description of a machine-checked book does not certify informal cost prose, exercise admissions, compiler behavior, or every empirical statement. No separate performance exercise occurs here. |
| **Perm**, `Perm.v:31–39,157–220` | **L/T:** preserve executable Boolean comparisons and checked reflection into propositions; adapt arithmetic/reflection tactics. No runtime bound is requested for the tactics. Do not infer native Lean arithmetic costs from Coq's unary mathematical presentation. |
| **Sort**, `Sort.v:3–7,30–40,47–78` | **T/Q:** instrument the actual recursive insertion/sort, charging comparisons separately from constructor visits. Quadratic worst-case comparison bounds require the chosen model; small-input superiority needs a workload and **E**, not a universal ordering of algorithms. Treat the illustrative `insert 7` sharing/allocation/GC account as conditional; see below. |
| **Multiset**, `Multiset.v:102–107` | **L/Q:** preserve the distinction between a specification's multiplicity function and an executable data structure. Function extensionality and equality of contents do not assert efficient enumeration, finite support, or efficient execution. No new benchmark is demanded. |
| **BagPerm**, `BagPerm.v:21–34,96–110` | **T/L:** list-based counts and extensional bag equivalence remain distinct from representation equality. Its proof-preference exercise needs a reasoned comparison, not a fabricated efficiency theorem. Sorting performance is inherited only through the actual Sort algorithm/bridge. |
| **Selection**, `Selection.v:13–25,77–103,175–185,259–285,310–340` | **T:** retain fuel exhaustion, sufficient/excess-fuel behavior, and the well-founded alternative. Fuel bounds recursion depth, not the whole execution cost. Count every `select` traversal and comparison for the quadratic bound. **Q:** input-dependent preferences and expensive-swap remarks concern a selected model, not all functional implementations; the bubble-sort aside is advice, not a theorem. |
| **Merge**, `Merge.v:7–32,38–54` | **T:** account for alternating split and merge work, balanced subproblem lengths, and the actual well-founded recursion to obtain an explicit `n log n` work bound. **Q:** the opening `O(n)` auxiliary-space statement is about the usual array algorithm; a list realization needs its own reachability/peak-space model. Include splitting work, and do not silently replace alternating split with the existing stable contiguous split. |
| **Maps**, `Maps.v:18–44` | **T/L:** functions model total-map observations. If comparing update chains with trees, retain an explicit history or executable representation and prove its decoder law. Extensional equality alone erases history length. Building one update closure does not traverse prior bindings; lookup through that closure chain can. |
| **SearchTree**, `SearchTree.v:3–13,805–838,1274–1323` | **T:** relate lookup/insert visits to height with comparator costs explicit. For enumeration, prove the accumulator equation, then count append copies versus accumulator traversal; show the relevant balanced and worst-case families. **Q:** some skew trees are cheap for left-append enumeration, so “unbalanced is quadratic” is a worst-case statement, not every-tree equality. The nested right call in `fast_elements_tr` does not imply constant stack merely because the text calls it tail-recursive. Qualify unary comparison and extraction claims below. |
| **ADT**, `ADT.v:994–999,1072–1120,1478–1486` | **T:** implement/verify `list_queue`, `two_list_queue`, and `ListsETable`; add explicit append/reversal/update counts for their performance prose. Retain initial potential and a sequential history for amortization. **Q:** arbitrary charged peeks defeat the stated two-list constant-amortized interpretation; see below. Its “sharing constraint” at `ADT.v:622–623` concerns module type identity, not physical heap sharing. |
| **Extract**, `Extract.v:38–105,110–156,247–273,347–391` | **T/L:** retain natural, integer, and finite-word realization bridges and checked sort/tree contracts; supply actual runnable Lean counterparts of the extraction demonstrations. The prose request to justify `sortZ` at `:88–89` needs a correctness bridge even without a named theorem starter. **E:** reproduce the BST workload experiment with accurate timing/labels. Fixed-width overflow and source benchmark defects are detailed below. |
| **Redblack**, `Redblack.v:606–625,759–787,795–836` | **T:** `redblack_bound` requires height/minimum-depth definitions and `RB → height ≤ 2*mindepth+1`; preserve the possible red root. To justify logarithmic structural work, additionally prove node-count/black-height and measured operation bounds, including balance work and comparison costs. Use `log(N+1)` or explicit small-size cases, not the literal `2 log N` at `N=0,1`. **E/Q:** port the random/consecutive comparison; published relative speeds are observations, not all-workload guarantees. |
| **Trie**, `Trie.v:6–65,79–114,131–222,262–272,280–313,350–386,491–526` | **T:** preserve explicit positive-bit representation and decoder, actual successor/add-with-carry/comparison recursions, and their bit-cost bounds. For the collision-program comparison, use separate sequence length `n`, maximum key/bit length, number of distinct bindings, and counted primitives; specialize to the book's bounded-key domain only after proving that bound. `successor_of_Z_constant_time` remains an obligation even though only a grading stub is present; see below. **Q:** map-operation and arithmetic qualifications below are necessary. |
| **Priqueue**, `Priqueue.v:26–62` | **T:** unsorted-list empty/insert/delete-max/merge costs require their actual recursions, occurrence-preserving maximum semantics, and charged comparison costs. Append merge costs the first list's length, hence is bounded by total size. **Q:** the described `N log N` heap/BST merge is a particular repeated-insertion strategy, not a lower bound on every heap/tree merge algorithm. |
| **Binom**, `Binom.v:3–8,36–38,56–66,80–136,162–170,391–396` | **T:** connect power-of-two heap rank to size and instrument carry/join/delete/max search. First bound work by forest slots and relevant ranks; a logarithm of current element count needs additional representation conditions, detailed below. **E/L:** the optional five-star `binom_measurement` explicitly requires machine-integer adaptation and randomized comparison against Priqueue; a theorem-only port does not complete it. |
| **Decide**, `Decide.v:294–325,328–411,445–504` | **T/L:** preserve Boolean reflection and computable proof-carrying decisions, opaque/parameter-based examples, list equality and `list_nat_in` execution. Distinguish propositional excluded middle from executable `Decidable` evidence and logical proof from reduction. Translate `Qed`/`Defined` behavior accurately rather than importing it as a Lean rule. **Q:** “Prop disjunction is not inductive” at `:337–339` is inaccurate; the relevant restrictions concern elimination/computation. The suggestion that one interface may be faster is not a universal benchmark result. |
| **Color**, `Color.v:11–57,485–540,549–570,577–599` | **T:** preserve cardinality decrease, chosen finite-map/set semantics, and partial-coloring correctness under the stated graph hypotheses. If efficiency is claimed, charge every map fold, adjacency-set removal, cardinality operation, and coloring lookup; decreasing vertex count bounds iteration count only. **E/T:** retain the concrete graph execution and a checked correctness instance; an exact source output also needs the source key-order/choice convention. **Q:** NP-completeness, spilling, and the palette scope require the qualifications below. |

## Critical qualifications and follow-up claims

### Sharing, allocation, and space

`Sort.v:59–78` assumes a heap representation, sharing, root liveness, an
allocator, and reclamation policy. The literal branch at `:33` constructs
`i :: h :: t`; the displayed count of four fresh cells in the `insert 7`
example presupposes reuse of the matched `h :: t` cell. A model charging each
literal constructor would instead count five. Choose and justify the model;
do not equate syntactic cons counts with backend allocation. Prove unchanged
suffix values first. A physical sharing claim additionally needs heap identity
and a realization relation. GC eligibility is conditional on all remaining
roots; cumulative allocations, net retained cells, and peak live bytes are
different quantities. Neither the source example nor a `List` equality proves
an unconditional one-node space increase in the running Lean program.

### Unary costs and closure-chain maps

`Extract.v:65–66` and `SearchTree.v:1290–1292` describe comparison cost using
the difference between operands. For the usual lockstep unary recursion, the
number of recursive steps depends on the smaller operand; equal large values
already refute a difference-only account. `Trie.v:106–111` displays the analogous
equality recursion explicitly. Retain a checked counterexample and the correct
count recurrence in a source unary model, separately from Lean's implementation
of `Nat`. `Trie.v:93–104` also overstates update work: `Maps.t_update` allocates
an equality-testing closure; it does not itself perform all prior comparisons.
Lookup through a long chain supplies the relevant worst-case work.

### FIFO amortization includes the actual observations

`ADT.v:1111–1120` computes `rev b` for a peek at `([], b)` and leaves the queue
unchanged. Repeating that peek pays for reversal repeatedly even along one
sequential history. Thus the general constant-amortized reading of
`ADT.v:1074–1076` cannot include arbitrary charged peeks. Prove a repeated-peek
counterexample and the valid bound for a specified enqueue/dequeue workload,
or present a separately named normalized/caching realization and its bridge.
Persistent branching also cannot spend the same initial credit twice. The
existing FIFO contract explicitly leaves endpoint head observation uncharged;
reusing it does not resolve this gap automatically.

The [Rocq 9.0 standard-library definition](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Lists.List.html)
of `rev` recurses on the tail and appends a singleton. It separately defines the
accumulator-based `rev_append` and proves equality of values. An instrumented
source model must therefore charge the recursive append work too; the existing
linear `SymmetricCosts.reverseRun_work` is a different implementation. The
repeated-peek obstruction requires only a reversal-work lower bound and survives
either implementation. Neither model alone establishes compiler/runtime timing.

### Extraction and finite integers

Replace `Extract.v:113–132`'s global `int`, `Abs`, and comparison axioms with
an explicit interface whose law fields have proved realizations. A finite signed
word's decoder is injective into `Int`, not surjective onto all integers.
Choose the exact width and signed order; an unsigned `UInt64` comparison is not
automatically the OCaml signed-int behavior. State bounds for every conversion.
`Extract.v:139–154` requires an overflow counterexample and either modular
arithmetic laws or range-guarded integer-addition correspondence. Do not assume
unbounded `Nat`/`Int` arithmetic transports to words. Checked semantic theorems
and runnable Lean code do not by themselves verify the Lean compiler, runtime,
FFI, or machine-instruction costs.

### Positive numbers and collision complexity

For `Trie.v:262–272,312–313`, use a defined bit length (including the terminal
one), not an ambiguous rounded logarithm. Account for `succ` calls nested in
`addc`. A comparison implementation supplied for the open exercise must have
its own measured recursion; structural termination alone does not count all
work in a body. Tries follow key bits, so cost depends on key bit length even
when only one binding is stored. The book's sequence of `n^3`, `n^2 log n`,
`n(log n)^2`, and `n log n` comparisons uses bounded key magnitude and a
particular primitive model; state these hypotheses and distinguish upper
bounds from tight lower-bound families. The imperative example at `:12–23`
also needs a precise interval: initializing indices below `2n` does not
initialize index `2n` if that endpoint is admitted.

For `successor_of_Z_constant_time` (`Trie.v:515–526`), select the permitted
sequential route or the finite uniform distribution on `1..N`, with `N>0` for
an average. Prove a constant total-cost-per-step bound or expected bit-write
bound and the bridge to this chapter's positive successor; retain initial
potential. The existing binary-counter proof is a useful base, but its Bool-list
encoding and bit-write convention require an explicit source correspondence.
The assertion that pure functional programs categorically cannot have constant
indexed updates (`Trie.v:6–49`) is a model-dependent comparison, not a universal
impossibility theorem; any lower bound needs its machine/persistence model.

### Binomial forest length

`Binom.v:162–170` permits arbitrarily many trailing `Leaf` slots: `priq` holds
for every all-Leaf list, regardless of its length. `find_max` at `:104–116`
scans those slots, even though the queue has zero stored elements. Deletion
also leaves empty slots, so reachability alone must not be assumed to imply
canonical trimming. Prove the elementary padded-forest counterexample. Use
forest-length bounds, a proved historical maximum-rank bound, or an explicit
canonicality/normalization contract before deriving a logarithm of live size.
Preserve the source algorithm while separately identifying any trimming variant.

### Benchmark fidelity

`test_searchtree.ml:2–11` constructs the tree before starting `Sys.time`; the
source labels at `:15–17` therefore misleadingly say “Insert and lookup”. The
timed region is only the lookup loop. `:19` draws new random keys when querying,
and `:13–17` discards the returned successful-lookup count. A Lean reproduction
must record this source behavior and label phases accurately; add checks for
the expected lookup answers and preserve seeds and generated workloads.
Separate any improved same-key/build-plus-query benchmark from the faithful
source experiment. This affects both Extract and Redblack's quoted timings.

For `binom_measurement`, use identical stored workloads and identical bounded
key representations for list and binomial queues; include random and relevant
adversarial cases, merge workloads, correctness checks, and setup/timing
boundaries. Preserve raw results and repetitions. Do not assume the binomial
implementation wins every small workload or reuse the book's timings as new
observations.

### Coloring scope

`Color.v:14–15` is not a valid unconditional deduction: NP-completeness does
not establish absence of polynomial algorithms without a separation assumption,
and the decision problem must be specified (fixed `k≥3`, or variable `k`);
two-colorability is different. Record the corrected conditional background;
do not introduce `P≠NP` or complexity axioms into the library.

`Color.v:29–41` explicitly leaves spill minimization unspecified. Correctness
does not mean total coloring, chromatic optimality, minimal spilling, verified
register allocation, or verified coalescing. In addition, `coloring_ok` at
`:549–552` guards palette membership by an incident edge. It does not constrain
an isolated vertex's color in an arbitrary candidate coloring. Preserve that
source theorem and, if stating that every produced color belongs to the
palette, separately prove the stronger implementation property.

## Directly inspected conaled reuse points

| Existing API | Applicable reuse and remaining bridge |
|---|---|
| `Applications/Resources/Measured.lean`: `Measured`, `bind`, `bind_erases`, `erasureSquare`, `reweight_bind`, `reweight_bound` | Compose actual instrumented algorithms and prove value erasure; vectors of counts can retain visits/comparisons/allocations separately. Additivity transports sums; monotonicity separately transports inequalities. Equal values do not imply equal costs (`same_value_different_cost`). |
| `Applications/Resources/Workload.lean`: `run`, `run_append`, `run_invariant`, `run_value_fusion`, `reweight_run` | Execute finite command words over actual successive states; reuse for FIFO, collision clients, and queue measurements. Branching, shared lazy evaluation, heap reclamation, and parallel span need additional models. |
| `Applications/Resources/Potential.lean`: `run_potential`, `run_potential_exact`, `run_constant_charge`, `initial_potential_matters` | Telescope per-step inequalities on the same trajectory with both boundary potentials. Appropriate for the corrected FIFO and repeated-successor claims; not a license to discard initial credit or reuse it on branches. |
| `Applications/Resources/BinaryCounter.lean`: `incWithCost_eq`, `flipCost_eq_leadingOnes_add_one`, `flipCost_potential`, `counter_potential`, `totalCost_le`, `totalCost_from_zero` | Existing exact bit-write accounting and sequence bounds. Bridge the VFA positive datatype/successor to canonical Bool digits and align terminal-bit charges before reuse. |
| `Applications/Resources/FIFOContracts.lean`: `Instrumentation.erases`, `Accounting`, `client_bound`, `sequential_bound`, `appendRun_exact` | Public representation-independent FIFO budgets and exact list enqueue visits. Commands cover enqueue/delete and explicitly leave endpoint head observation uncharged. The symmetric implementation is a different source algorithm from VFA's two-list queue. |
| `Applications/Resources/SymmetricCosts.lean`: `reverseRun_value`, `reverseRun_work` | Reusable measured accumulator reversal gives value `xs.reverse ++ acc` and work `xs.length+1`; state this model when comparing to source reversal. Do not infer physical allocation or GC from it. |
| `Applications/Resources/TreeFlattening/Core.lean`: `appendWithCost_exact`, `fromTWithCost_count`, `fromTsWithCost_exact`; `TreeFlattening/Growth.lean`: perfect-tree counts and `recursive_flatten_theta`/`stack_flatten_theta` | Reuse append-copy accounting and the demonstrated separation of recursive versus explicit-stack traversal. Existing trees carry leaf payloads; VFA BST inorder enumeration needs an explicit representation/observation bridge or its own actual instrumentation. Perfect-tree family theorems are not automatically every balanced-tree bound. |
| `Applications/Resources/Growth.lean`: `isBigO_of_nat_bound` | Convert a proved eventual natural-number bound into standard real-cast `Asymptotics.IsBigO`. The size family, constants, and primitive count must already be supplied. |

## Completion evidence to attach to local tickets

Each relevant chapter needs source-pointer mappings for the T/E/L/Q items,
including open prose exercises, statement review, meaningful checked cases,
and the applicable integrated build/audit and independent reviews. Retain
benchmark scripts/results and exact runtime provenance in checkpoints. Record
unresolved resource models and source corrections as local follow-up obligations;
neither a declaration-only ledger nor this audit closes those obligations.
