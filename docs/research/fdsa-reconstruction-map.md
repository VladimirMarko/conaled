# FDSA reconstruction and coverage

This local workstream reconstructs *Functional Data Structures and Algorithms:
A Proof Assistant Approach* in Lean while retaining conaled's architectural and
proof standards. The owner requested whole-book coverage on 2026-11-02, with
local tickets and recovery checkpoints instead of GitHub writes. This extends
the earlier source-selection scope of issue #174; it does not replace that
issue's requirements on reusable constructions, observations and resource models.

## Pinned reference

- [Author-maintained book site](https://fdsa-book.net/).
- [Official PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
  **version of July 27, 2026**, retrieved 2026-11-02; original ACM Books edition
  September 2025.
- PDF SHA-256:
  `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
- Isabelle source mirror used for source correspondence:
  `f86f290225eebcc52c1ae7dba2e098f405f51c21` at
  [mirror-isabelle](https://github.com/isabelle-prover/mirror-isabelle/tree/f86f290225eebcc52c1ae7dba2e098f405f51c21).
  Chapter 1 has no direct theory hyperlink. The first direct theory link occurs
  in Chapter 2. Later AFP sources require their own version and license records.

Manuscript downloads and extracted book text are research inputs, excluded from
the source deliverable. The checkpoint's companion `fdsa-control` directory
contains the complete user request, source-link inventory, local chapter
tickets, independent review records and candidate validation evidence. That
tracker is the authority for acceptance; the presence of a source mapping below
does not by itself mean that its chapter has passed all gates.

## Chapter order and scope

The full scope is all 27 chapters and appendices A–C. Mathematical definitions,
theorems and exercises need checked witnesses. Notation and explanatory material
need explicit correspondence and scope accounting. Existing results count only
when their statements, assumptions and algorithms actually match the source.
Chapter organization is a coverage index; modules follow reusable domain concepts.

| Chapter | Topic | Current implementation scope |
| --- | --- | --- |
| 1 | Basics | Detailed witnesses below; acceptance is tracked separately |
| 2 | Sorting | Queued |
| 3 | Selection | Queued |
| 4 | Binary Trees | Queued |
| 5 | Binary Search Trees | Queued |
| 6 | Abstract Data Types | Queued |
| 7 | 2–3 Trees | Queued |
| 8 | Red–Black Trees | Queued |
| 9 | AVL Trees | Queued |
| 10 | Union, Intersection and Difference | Queued |
| 11 | Arrays via Braun Trees | Queued |
| 12 | Tries | Queued |
| 13 | Region Quadtrees | Queued |
| 14 | Priority Queues | Queued |
| 15 | Leftist Heaps | Queued |
| 16 | Priority Queues via Braun Trees | Queued |
| 17 | Binomial Priority Queues | Queued |
| 18 | Dynamic Programming | Queued |
| 19 | Amortized Analysis | Queued |
| 20 | Queues | Queued |
| 21 | Splay Trees | Queued |
| 22 | Skew Heaps | Queued |
| 23 | Pairing Heaps | Queued |
| 24 | Graph Algorithms | Queued |
| 25 | Knuth–Morris–Pratt String Search | Queued |
| 26 | Huffman's Algorithm | Queued |
| 27 | Alpha–Beta Pruning | Queued |
| A | List Library | Matched as used; final complete inventory pending |
| B | Time Functions | Matched as used; final complete inventory pending |
| C | Notation | Matched as used; final complete inventory pending |

## Chapter 1: Basics, printed pages 1–10

### Standard language, types and notation (§§1.1–1.3)

Lean supplies terminating inductive types and definitions, pattern matching,
`let`, `if` and `match`. Its termination checker and well-founded induction
provide the required logical discipline; no alternative language or compiler
is introduced. Isabelle's Boolean propositions are represented by `Prop` for
theorems and `Bool` for executable discriminators, with explicit decidability
where computation needs it. This is a correspondence, not an identification
of the two proof assistants' logics.

| Source item | Lean correspondence and checked use |
| --- | --- |
| Booleans, function types | `Bool`, `α → β`; the selected-branch examples in `Examples.ListReversal` |
| Natural, integer and real numbers | `Nat`, `Int`, `Real`; mathematical unbounded types, not fixed-width machine words |
| Natural inclusions and subtraction | `Examples.FunctionalBasics.real_cast_add`, `real_cast_sub`, `truncated_subtraction_matters`; subtraction transport retains `n ≤ m` |
| Integer-to-natural conversion | `Int.toNat`; `integer_to_nat_boundary` checks negative truncation and a positive value |
| Sets and comprehension | `Set α`, standard union/intersection/complement/difference; `set_comprehension` checks membership interpretation |
| Lists and constructors | `List α`, `[]`, `(::)`, `++`, `.length`; `append_equations` and `append_associative` |
| Option, pair and unit | `Option α`, `none`, `some`, `Prod`, `.1`, `.2`, `Unit`; `option_pair_and_unit` |
| Pointwise function update | `Function.update`; `update_at_key` and `update_away` |
| Empty multiset, insertion, membership, sum, cardinality | `0`, `(::ₘ)`, `∈`, `(+)`, `Multiset.card`; `multiset_observations`, `multiset_append`, `multiset_membership` |
| List conversion and underlying set | `(xs : Multiset α)`; the set `{x | x ∈ s}` for `s : Multiset α`, without silently discarding multiplicity in multiset claims |
| Multiset map, filter and value sum | `Multiset.map`, `filter`, `sum`; `multiset_map_filter` and `multiset_observations` retain duplicate contributions |
| Mathematical typography | Lean implication `→`, conjunction `∧`, length, multiplication and exponentiation, successors and set comprehension have their standard meanings |

The Fibonacci recurrence and named subpattern on page 3 illustrate syntax;
they do not specify new algorithms in this chapter (the recurrence gives no
base cases). They are accounted for by Lean's recursive equations and alias
patterns, not by inventing an extra Fibonacci specification. Ordinary pair
projection and standard set operations are reused directly. Foundational
libraries are not reimplemented merely to mirror a notation table.

### Induction (§1.4)

The append proof maps to `List.append_assoc`, exercised through
`Examples.FunctionalBasics.append_associative`; its recursive equations are
checked in `append_equations`. `Arithmetic.Euclid.induction` supplies exactly
the displayed computation-induction schema for Euclid's recursive call
`(m,n) ↦ (n,m % n)`. Its hypothesis is conditional on `n ≠ 0`, and its proof
uses strict decrease of the second argument. `gcd_equation` connects that
orientation to standard `Nat.gcd`.

`Examples.FunctionalBasics.gcd_common_divisor` derives a divisibility property
through the new induction rule, using the modulo divisibility law. The concrete
`gcd_divisor_example` discharges its hypotheses; `gcd_zero_boundary` checks the
zero case. This is a useful application rather than an induction theorem
whose premise already assumes the result.

The general discussion of computation induction is implemented by Lean's
existing well-founded induction and termination machinery. No theorem is
claimed about all external source syntax or every unspecified programming
language.

### Call-count conventions (§1.5)

The source's E/T translation is explicitly a metalanguage presentation.
`Resources.CallCount` checks its compositional algebra using the existing
`Resources.Measured`, `pure` and `bind`; it does not claim an automatic or
verified source-to-cost compiler.

| Rule | Checked witness | Model interpretation |
| --- | --- | --- |
| Variables, constructors and designated primitives | `primitive_rule`, existing `pure` | No extra charge beyond evaluating arguments |
| Function arguments and application | `arguments_rule`, existing `bind_assoc` | Argument observations precede the function's observation; repeated binding handles more arguments |
| Recursive function entry | `tick`, `tick_value`, `tick_cost` | Add exactly one to the natural call count |
| Let binding | `let_rule` | Evaluate the body at the bound expression's actual value |
| Conditional | `if_rule` | Count the Boolean computation and only its selected branch |
| Pattern match | `case_rule` | Count the scrutinee and selected sum arm; ordinary constructor matches use the same binding principle |
| Nonrecursive entry omission | `CallCount.tick`, `tick_cost_comparison`, `add_entry_isBigO` | Qualified comparison through the cost-model repair below; positivity is explicit |

Checked cases `primitive_has_no_extra_charge`, `call_entry_charged_once`,
`let_uses_bound_value`, `arguments_add_costs`, `inactive_branch_uncharged` and
`selected_case_only` exercise these laws, including an expensive unselected
branch. Control and argument laws work over an arbitrary additive observation
type with only their stated assumptions. The concrete entry count uses `Nat`.

On page 7 an intermediate worked translation appears to assign an extra unit
inside T even though constructor costs are stated to be zero. The final
append equations are consistent and unambiguous: one charge per recursive
invocation, including the empty case. Those equations are the formal target;
the apparent intermediate typographical error is not made into an axiom.

### Append and reversal (§1.5.1 and Appendix A's reverse equations)

All names in the following table are under `Resources.ListReversal` unless
qualified otherwise. Cost functions are the second projections of the
corresponding measured computations.

| Source construction or claim | Checked witness |
| --- | --- |
| Append, including the final empty call | `appendRun`, `appendRun_nil`, `appendRun_cons` |
| Exact append cost `length xs + 1` | `appendRun_exact` |
| Naive reverse with recursive tail reversal followed by append | `naiveRun` and its defining equations |
| Naive reverse result and empty case | `naiveRun_value`, `naiveRun_nil` |
| Naive reverse cost recurrence | `naiveRun_cons_cost` |
| Exact-count exercise | `naiveRun_double_cost`, `naiveRun_cost`: `(n+1)*(n+2)/2`, including `n=0` |
| Quadratic upper bound | `naiveRun_cost_le`: at most `(n+1)^2` |
| Accumulator reverse equations | Existing `Resources.SymmetricCosts.reverseRun` defining equations |
| Arbitrary-accumulator result and linear cost | Existing `reverseRun_value`, `reverseRun_work`, combined by `accumulator_exact` |
| Empty-accumulator agreement | `realizations_agree`, using `List.append_nil` |
| Resource improvement for equal outputs | `accumulator_cost_le`, `accumulator_cost_lt` (strict when input is nonempty) |
| Existing semantic interface | `naiveSquare`, `accumulatorSquare`, using `Resources.erasureSquare` |

`appendRun` adapts the existing `TreeFlattening.appendWithCost`, whose cost
counts copied cells, by adding the one final call. Its recurrence is proved,
so the two cost meanings are not identified silently. The accumulator algorithm
is reused unchanged from symmetric-list work. The naive algorithm is explicitly
defined; its cost is not attributed to the standard library's optimized reverse
implementation merely because the output equals `List.reverse`.

The examples include empty inputs, a singleton, repeated values, distinguishable
ordered values, and a nonempty accumulator. Length three has independently
calculated naive count `1+2+3+4 = 10` and accumulator count `4`.
`Examples.ListReversal.accumulatorAfter` supplies a continuation square whose
implementation preserves the accumulated observation. `composed_square` pastes
that square with `naiveSquare`, and `composed_run` uses the ordinary `bind`
interface; both prove that two reversals recover every input list.

### Resource and interpretation boundary (§§1.5.2–1.5.3)

The observations are nonprimitive call counts under the specified equations.
They do not establish allocation, stack depth, garbage-collection cost, Lean
execution time or a physical RAM bound. The source's implementation discussion
is conditional on a suitable compiler, runtime, representation and target.
No such end-to-end stack is postulated here.

The cost-comparison mathematics on pp7–9 is a separate required part of the
chapter. Its earlier blanket classification as explanatory scope was incorrect.
The [cost-model repair](fdsa-call-models.md) supplies the precise statement
review and intended connections for three currently unvalidated additions:

- Uniform fine/coarse tariff bounds from a fixed finite local-case catalogue,
  with an exact append-branch client and both asymptotic directions.
- Omission of one nonrecursive entry under pointwise/eventual positivity,
  with zero and intermittently-zero counterexamples. Merely being
  non-identically-zero is insufficient.
- Actual shared-demand cache transitions, demanded-value agreement and a work
  bound against a finite eager catalogue, with external-program correspondence
  explicit and unshared duplication treated separately.

These source repairs remain subject to compilation, full candidate gates and
independent final review; their presence does not close the chapter. Section
1.5.3's preference for explicit bounds remains explanatory. Higher-order time
conventions refer forward to Appendix B.1 and stay on that appendix's list.

## Architecture and statement review

Operations, returned values and observations remain separate. Exact agreement
uses ordered lists, so duplicates and order are preserved. Costs require their
own recurrence proofs and are not transported from semantic equality. The
realizations are optional and do not impose an allocation or storage capability
on other targets. These are ordinary Lean/Type results; no cross-setting
interpretation of these new induction proofs is claimed.

The only existing public-interface adjustment is the universe signature of
`Resources.erasureSquare`. Its value carriers may now live above the cost type;
this permits natural costs for lists of arbitrary-universe payloads. Its
implementation, semantic contract, old equal-universe specializations and
assumptions are unchanged. The new squares and universal composition example
check the previously rejected use. No preservation family is added.

Statement review checked the following points for every declaration group:

- Call rules quantify over actual measured values and selected bodies; no
  expensive inactive branch contributes to the observation. Additive laws
  impose no commutativity where none is used.
- Euclid's quantifiers cover all natural inputs, including `(0,0)`. The
  recursive premise is used only after proving the second argument nonzero;
  modulo then strictly decreases it.
- Append and reversal quantify over all finite lists and arbitrary payload
  types. The fast result retains every element of an arbitrary accumulator.
  There are no validity premises that could make these results vacuous.
- The exact triangular count is obtained from a proved doubled identity, so
  natural division cannot round an unproved rational formula. Empty and
  singleton cases are retained.
- Strict resource improvement requires a nonempty input; non-strict comparison
  covers the empty case. These are model comparisons, not global optimality.
- Update-away retains inequality of the queried key. Natural subtraction
  transport retains its order premise. Multiset cases count repeated elements;
  set membership is not substituted for permutation or multiplicity.
- Semantic square composition has matching represented boundaries and retains
  observations through `bind`; it does not feed a measured pair to an operation
  expecting a plain list.

Focused builds check these declarations and examples. Chapter acceptance still
requires the project's immutable-candidate verification and exhaustive proof
audit, both independent review axes, and final candidate-identity verification.
Their exact outcomes are kept in the local checkpoint's review record rather
than inferred from this narrative.

## Shared binary-tree observations and cached folds (FDSA-XT01)

This bounded cross-cutting **uncompiled draft** supports common observations
and cache mathematics used by Chapters 4, 5 and 9, with a later representation
bridge for Chapter 15. It activates or accepts none of those chapters. Exact
source distinctions, examples and statement assessment are in
[fdsa-tree-cache.md](fdsa-tree-cache.md).

| Common source obligation | Draft declarations / intended connection |
| --- | --- |
| Ordinary explicit-zero, ternary branching fold | `Trees.fold`, constructor equations, `fold_map`, `fold_fusion`; no new carrier or algebra class. |
| Canonical size/height and node-labelled inorder observations | `fold_numNodes`, `fold_height`, `inorder`, `inorder_length`, `inorder_map` and the three shape-map laws. |
| Generic cached fold and all-node validity, C04-062–072 common mathematics | `Trees.Cached.read`, `smartNode`, `Valid`, `smartNode_valid_iff`, `read_eq_fold`; independent erasure/inorder/shape laws. |
| Actual bottom-up annotation | `annotate`, `annotate_valid`, `erase_annotate`, `read_annotate`, as an ordinary fold client. |
| Conditional local overhead component of C04-073 | `Resources.TreeCache.readRun`, `nodeRun`, reached-argument value refinement, exact callback-cost-plus-three equation and local bound. This is a separately declared tariff. |
| Reuse and composition | General size/height and pair-fusion clients, existing ordered-summary composition, noncommutative word, empty/repeated labels, malformed descendants and actual measured-append callback in `TreeCacheExamples`. |

The source leftist helper tariff is zero; it has not been equated with the
positive local-access observation. The actual append callback gives growing
work even on valid cached trees, so no constant bound is attributed to an
arbitrary fold operation. Full traversal costs, balance/search algorithms,
maximum representation issues and the existing-leftist adapter remain in
their chapter inventories. All shared-unit and chapter acceptance gates remain
pending; no previously recorded review or validation result covers this draft.

## Shared root rotations and cached rebuilding (FDSA-XT06)

This bounded cross-cutting **uncompiled draft** builds on XT01 and supports
ordinary single root rearrangements used by Chapters 5, 9 and 21. It does not
activate or accept those chapters, and it does not change the initial Chapter 2
foundation prefix. The exact partial-source correspondence, independent
expected cases and statement assessment are in
[fdsa-tree-rotations.md](fdsa-tree-rotations.md).

| Common source obligation | Draft declarations / intended connection |
| --- | --- |
| Partial ordinary root equations, C05-042/043 | `Trees.rotateLeft?`, `rotateRight?`, matching-shape equations and exhaustive failure characterizations on the existing `BinaryTree`. |
| Ordered semantics and transport | Success preserves full inorder, node and external-leaf counts; the opposite rotation recovers the input. Arbitrary label maps commute with success and failure, without injectivity. |
| Qualified fold preservation | `fold_rotateLeft`, `fold_rotateRight` use only the actual fringe-fold reassociation equation. Optional-success laws accept a uniform sufficient equation. Existing ordered monoid summaries and a word client retain noncommutative order. |
| Local cache rebuilding for later AVL and other consumers | `Trees.Cached.rebuildLeft`, `rebuildRight`, erasure/inorder laws and exact fringe-validity equivalences; each recomputes two annotations with existing smart nodes. Correctness for the new shape and equality of old/new summaries remain separate claims. |
| Actual two-node measured composition | `Resources.TreeRotations.rebuildLeftRun`, `rebuildRightRun` pass each first returned tree to the second `nodeRun`. Exact work is the two actual callback costs plus six, with reached-value refinement, separate fringe validity and reached-cost bounds. |
| Connected boundaries and resource clients | Generic repeated-label, Empty and missing-pivot cases; noninjective mapping; height change; stale raw annotations and malformed retained fringes; existing scalar callbacks and actual recursive append callbacks. |

The separately declared local-access tariff counts four root reads and two
constructor entries. It neither replaces Chapter 5's unit-per-rotation count
nor identifies source zero-helper tariffs with positive work. Actual append
callbacks give different left/right work and unbounded valid-tree families;
equal ordered values alone do not imply equal or constant resource use.

Positioned rotations and schedules, their legal execution and exact counts,
listification and rotation distance, complete search/balance/tag algorithms,
double-rotation selection and splay correctness/amortization remain in the
original chapter inventories. Accepted repaired Chapter 1 and accepted XT01
are prerequisites to integration or acceptance. All focused and full candidate
checks, both independent review axes and immediate candidate verification remain
pending for this draft.

## Shared ordered-tree observations (FDSA-XT07)

`Applications.Trees.Ordered` adds one recursive relation invariant on the
existing Mathlib BinaryTree and existing inorder observation. Pairwise
inorder order implies the invariant without relation laws; the reverse and
resulting inorder-congruence iff retain explicit transitivity. Relation
weakening and exact label-map pullback remain independent of that premise.
Strict-key specializations use only a key preorder, derive distinct mapped
keys without global key injectivity, and connect to standard SortedLT and
adjacent IsChain order. The weak-order-plus-Nodup converse retains a key
partial order and distinctness of keys rather than only full payloads.

`Applications.Trees.OrderedRotations` consumes actual successful XT06 root
rotation and erased cached-rebuilding observations. Its recursive-invariant
iff laws retain transitivity and actual successful-result premises where
needed; erased-payload order does not acquire a cache-validity or summary
reassociation requirement. The existing operations, cache laws and resource
executors are unchanged.

`Examples.OrderedTrees` supplies connected source and generic cases, including
the printed inorder [2,3,5,6,8,9], legal rotation/inverse, empty/singleton
domains, the successor-relation counterexample, repeated keys, missing
antisymmetry, noninjective key-preserving payload maps and actual cached
rebuilds retaining an invalid fringe. Existing duplicate/cache fixtures keep
their original meanings. Exact source provenance, hypotheses, case reasoning
and the applicable notice are in [fdsa-tree-order.md](fdsa-tree-order.md).

This supports only the invariant portions of C05-001/025, the ordered-state
consequence of C05-043, key-order portions of C06-044/049, and the qualification
for later C04-058. Partial rows remain partial. The actual balancer, all-node
exercise, direct recursive set/BST proof exercise, search/update/split/join
algorithms, Set/Map refinement, balance, costs, positioned rotation schedules,
interval-cache/search and every later chapter obligation remain queued.
This is an uncompiled shared source draft, with every integrated validation
and independent final acceptance gate still pending.

## Shared ordered-tree search paths (FDSA-XS01)

This bounded **uncompiled source draft** uses the existing Mathlib BinaryTree
and `Trees.Ordered` to follow one selected query path, returning the actual
stored entry. It does not activate or accept Chapters 5–10. Exact primary
source identities, the complete applicable Isabelle notice, public statement
boundaries and connected examples are in
[fdsa-tree-search.md](fdsa-tree-search.md).

`Resources.TreeSearch.run` is the single recursion; `find?` and `entries`
project its Option/Nat result. Derived `visits` has direct branch equations
from that same execution. No new comparator wrapper, tree carrier, search
machine, pure duplicate recursion, default payload or generic translator is
introduced. The source specialization uses existing `compareOfLessAndEq`,
`cmp_eq_compareOfLessAndEq` and `cmp_compares`.

| Original source obligation or shared observation | Actual public draft connection and retained limits |
| --- | --- |
| C05-003 comparison meaning; query recurrence in C05-004 and C06-045 | `run` and its nil/LT/EQ/GT equations; `TreeSearchExamples.source_run_eq_cmp`, `observe_presence` and `observe_payload`. The literal comparator is reused; map lookup returns the actual semantic payload. |
| Query clauses of C05-014/028; C06-064/065 | `find?_eq_some_iff`, `find?_eq_none_iff`, `find?_isSome_iff`, `find?_eq_find`, `map_find?_eq_lookup`; source clients `source_find_spec`, `source_none_spec`, `source_find_inorder`, `source_payload_lookup`. Strict keyed order and input-local `Ordering.Compares` remain distinct premises; List.lookup alone adds lawful key BEq. Mutation and full ADT laws remain open. |
| C05-066; query portions of C08-020/021/075/076 and C09-008/009 | `run_map`, `run_map_pullback`, `find?_map`, `entries_map`, `visits_map`; `outer_tag_run`, `outer_tag_counts`, `outer_tag_payload`, `outer_tag_observer`. Outer tags are erased while semantic values are retained, without color/cache/balance validity. Later concrete representation and complete empty-implementation obligations remain. |
| Search-height portions of C08-071/072 and C09-039/040; p.59 worst-case height claim | `entries_pos`, `entries_eq_visits_add_terminal`, hit/miss consequences, `entries_le_height_add_one`, `entries_le_height_of_some`, `visits_le_height`, `visits_pos_of_some`. `exists_run_eq_height`, `exists_run_visits_eq_height` and `exists_source_run_eq_height` give an actual stored-key witness on every nonempty strict tree under stored-key-pair calibration. No logarithmic or later mutation-work bound follows. |
| C05-094 finite present-key comparison | `balanced_present_runs` / `chain_present_runs`, their entry/visit lists, `present_query_sums` and `present_query_means` use actual queries [3,6,9], sums 5/6 and rational means 5/3 and 2. The interpretation is uniform over those three present keys under the declared node-visit tariff. |
| Inherited query clause of C10-003 | The same augmented query semantics and outer-tag transport support the inherited Set query. The other inherited Set laws and complete Set2 interpretation are unchanged obligations. |
| Raw observations and connected premise boundaries | `find?_some_spec`, `key_eq_of_find?_eq_some`, `run_map`; printed-tree correctness/tightness, valid-rotation value preservation with changed E/V, false payload versus absence, Empty payload, malformed off-path key, duplicate-key rotation and dishonest-route examples. `find_eq_indexOf_get` supplies only the homogeneous value connection to the existing two-pass interface. |

Names without a prefix in the shared-law rows are in `Resources.TreeSearch`;
the named connected examples are in `TreeSearchExamples`. The note contains
the fuller declaration map. These are statement and source correspondences,
not checked elaborated types, final review outcomes or closed inventory rows.

E reconstructs a declared source-style count of search invocations, including
a reached empty call; the inspected theories provide no generated T_isin or
T_lookup equation. V counts nonempty visits/three-way route evaluations, with
`E = V + (if result.isNone then 1 else 0)`. Hits have E=V; misses have E=V+1.
V is not an additive reweighting of E alone. Neither observation includes the
literal comparator's separate less-than/equality tests, and comparator result
agreement does not transfer those primitive costs. Whole-tree mapping,
inorder construction and indexOf followed by get retain their own work. No
compiler, sharing, stack, allocation or target-runtime claim is made.

All original chapter obligations remain mandatory and partial rows remain
partial. Concrete insert/delete and both deletion clients, split_min domains,
other direct-proof exercise clauses, complete Set/Map implementations, joins,
unions, positioned rotations and rebuilding costs, interval/sweep algorithms,
color/black-height or height/cache invariants and logarithmic guarantees remain
queued. Chapter 7's Node3 has a conditional second comparison and requires its
own carrier and recurrence. Chapter 10's split returns and reconstructs two
trees as well as a Boolean; query correctness does not prove those outputs or
join/split total work. C10-117's retained conditional treap-work gap is unchanged.
These limits introduce no additional mandatory general framework.

The original base is `66eae34815a177c6b4bf5120e05202ebb8876c91`, with the
preserved unaccepted XT01/XT06/XT07 ancestry. Repaired accepted Chapter 1 and
applicable tree prerequisites must precede integration/acceptance. The original
Chapter 2 prefix `c80eec92f5458eccfd1c34c8314d666c2a1e3847` is unchanged.
All matching focused/full guarded candidate checks, both integrity passes,
exhaustive audit, independent Standards/Spec reviews and immediate candidate
verification remain pending. This draft and its checkpoint do not certify any
chapter or any inherited tree component.
