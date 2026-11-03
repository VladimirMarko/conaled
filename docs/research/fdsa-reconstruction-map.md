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

## Shared binary-tree shape bounds (FDSA-XT02)

This bounded cross-cutting **uncompiled draft** adds common structural
mathematics used by Chapters 4, 11 and 15, on the saved XT01 tree carrier and
fold. It accepts or activates none of those chapters. Source distinctions,
connected uses and statement assessment are in
[fdsa-tree-shape.md](fdsa-tree-shape.md).

| Common source obligation | Draft declarations / intended connection |
| --- | --- |
| Minimum external-leaf height and source predicates | `Trees.minHeight`, map/constructor laws, recursive `Complete`, `AlmostComplete`, source subtraction equivalence and immediate-child closure. |
| Sharp capacity and completeness | Universal `2^minHeight <= numLeaves <= 2^height`, both strict incomplete bounds, and completeness iff equality at either bound. |
| Natural logarithms and height optimum | Existing `Nat.log`/`Nat.clog` interfaces, exact almost-complete formulas, and `height_optimal` for unrelated payload types under a node-count inequality. |
| Real source formulas | Separate `Applications.Trees.ShapeLog`: real sandwich/strict bounds, complete height equality and exact natural floor/ceiling bridges. |
| Connected uses and boundaries | Empty labels, right-heavy almost-complete trees, noninjective maps, actual cached annotations, malformed caches, a minimum-height reader, a genuine optimal-height nonconverse and recursive local-height-balance counterexample. |

The recursive mathematical predicate does not by itself complete the source's
executable checker obligation. Immediate-child closure does not claim the
general subtree theorem. Braun/weight-balance bridges, constructor exercises,
array algorithms and the existing leftist representation and merge-cost bridges
remain with their chapter tickets. The existing leftist rank proofs are
unchanged. All integration, candidate validation and final review gates remain
pending for this draft and its unaccepted prerequisites.
## Shared Braun structural facts (FDSA-XT09)

This bounded cross-cutting **uncompiled, unaccepted draft** supplies the common
Braun shape mathematics used by Chapter 11 arrays and Chapter 16 priority
queues, on the saved XT02 base `974a97321a8ec174b56104c7e6efaaca881b6639`.
It activates or accepts neither chapter. The complete source correspondence,
actual declaration/case map, licensing and source-level statement assessment
are in [fdsa-braun-shape.md](fdsa-braun-shape.md).

| Selected source connection | Actual draft declarations and applications |
| --- | --- |
| C11-008; C16-001 shape component | `Trees.Braun`, `braun_nil`, `braun_node`, `braun_node_iff`: exact recursive left-equal-or-one-larger size bias, with both child predicates. |
| Arbitrary label transport and C11-019 erased-shape uniqueness | `braun_map` is an iff without injectivity or payload capabilities; `braun_shape_eq` compares maps to Unit across independent universes and requires both Braun premises plus equal node counts. `braun_eq_of_numNodes_eq` retains the Unit-labelled source specialization. |
| C11-014/015 local constructor and its intermediate formulas | Additive `Shape` declarations `almostComplete_node_of_numNodes_balance`, `height_node_eq_clog_of_numNodes_succ`, `minHeight_node_eq_log_of_numNodes_succ`; additive `ShapeLog` ceiling/floor counterparts. Both AC children, actual count hypotheses, leaf positivity and the adjacent-power interval are retained. |
| C11-016/017; C16-042 height input only | `braun_almostComplete`; actual applications of the unchanged general log/clog, Real rounding and `height_optimal` laws. Nil uses leaves1, and the optimum competitor may have an unrelated payload type and any shape. |
| Consequential structural and payload boundaries | `BraunShapeExamples` connects Empty/singleton, left/right two-node orientation, malformed equal-count children, B5/A5, noninjective maps, Unit erasure and different Bool payloads to the public laws. |
| Actual cache compositions | `braun_erase_iff`, `braun_annotate_iff`, `annotated_size_contract`, `cached_shape_and_size` and `sizeBraunFive_contract` combine actual XT01 observations. `valid_cache_nonBraun` and `braun_invalid_cache` distinguish recursive cache validity from shape. |

Braun bias is not ordinary breadth-first left packing. The five-node Braun
shape has source low-bit indices 1–5 but conventional heap-path positions
`{1,2,3,4,6}`. That calculation and the source's swapping `del_left` versus
ordinary BST extraction are documented consumer boundaries; neither operation
nor an indexing implementation is introduced here. Erased shape equality does
not imply array-order equality or heap validity, and no cost transfers merely
from a structural height bound.

The earlier XT02 section and its original exclusions are preserved verbatim.
XT09 supplies only the selected follow-up above. Full recursive symmetric
balance C11-018 remains mandatory later work; no second recursive predicate is
defined here. C11-122 / Exercise 11.1 still requires the independent direct
power-bound and height proof without first proving AC. The retained AFP PQ
source supplies a direct route for that later obligation, not a proof imported
by this unit.

All 135 Chapter 11 rows, all 48 Chapter 16 rows, their other exercises, index
characterization and converse, array observations/cache/operations/conversions,
heap algorithms/domains, source-specific costs and all other original book and
appendix obligations remain required. The source notice and exact July 2026
PDF/Isabelle/dated AFP identities are retained in the linked note; the formal
companion pins are not claimed to be the manuscript's generating revision.
Accepted repaired Chapter 1 and the shared prerequisites, matching focused/full
guarded validation with both integrity phases and exhaustive audit, both
independent final review axes and immediate candidate verification remain
necessary. Source presence, this map, a commit and a checkpoint are not acceptance.
