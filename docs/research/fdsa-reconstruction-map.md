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
| 2 | Sorting | Queued; shared insertion costs below |
| 3 | Selection | Queued; shared insertion costs below |
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
| A | List Library | Shared standard interfaces and checked adapters below; acceptance tracked separately |
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
| Nonrecursive inlining | Use `bind`/`pure` without `tick` | Omitting an entry charge is an explicit model convention |

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

The checked observations are nonprimitive call counts under the specified
equations. They do not establish allocation, stack depth, garbage-collection
cost, Lean execution time or a physical RAM bound. The source's implementation
discussion is conditional on a suitable compiler, runtime, representation and
target. No such end-to-end stack is postulated here. Its discussion of inlining
also identifies the zero-cost corner case; no unsupported asymptotic
equivalence is asserted for a function whose model cost is identically zero.

The chapter prefers explicit inequalities over asymptotic machinery. Its
concrete bounds and exact exercise are checked above; the remaining discussion
does not assert an additional algorithm theorem. Higher-order time conventions
refer forward to Appendix B.1 and remain on that appendix's coverage list.

## Shared insertion costs for Chapters 2 and 3

The local cross-cutting ticket FDSA-X002 develops the insertion-sort cost model
used by §2.2, Exercise 2.1 and the small-input sorting case in Chapter 3. Its
development does not accept either chapter or omit their remaining obligations.

`Resources.InsertionSort.insertRun` instruments `List.orderedInsert`, and
`sortRun` instruments the recurrence of the existing `insertionOn`. The value
projection is proved equal to the existing algorithm. A comparison, constructor
or projection adds no charge in this model; every insertion invocation and
every sort invocation, including their empty cases, adds one. Consequently the
observed cost follows the displayed T-insort equations exactly. These are source
call counts, with no claim about the cost of an arbitrary comparison function or
Lean execution time.

| Intended result | Checked witness under `Resources.InsertionSort` |
| --- | --- |
| Insertion returns the existing left-biased ordered insertion | `insertRun_value` |
| Insertion count lies between 1 and input length plus 1 | `insertRun_cost_bounds` |
| An accepted head comparison terminates insertion immediately | `insertRun_cost_of_head` |
| Preceding every input element gives the immediate count | `insertRun_cost_of_all` |
| Rejecting every comparison traverses the entire input | `insertRun_cost_of_all_not` |
| Sort returns the existing insertion sort and preserves length | `sortRun_value`, `sortRun_length` |
| Sort counts recursion, insertion into its actual result, and entry | `sortRun_cons_cost` |
| Uniform lower count `2n+1` | `sortRun_cost_lower` |
| Uniform triangular upper count `(n+1)(n+2)/2` | `sortRun_double_cost_le`, `sortRun_cost_le` |
| Source Lemma 2.1's weaker bound `(n+1)^2` | `sortRun_quadratic` |
| Pairwise-ordered input attains the lower count | `sortRun_cost_of_pairwise` |
| Pairwise rejection makes every insertion traverse its tail | `sortRun_double_cost_of_opposite` |
| Descending distinct natural values attain the upper count | `reverse_range_opposite`, `sortRun_cost_reverse_range` |
| Existing keyed stability, sortedness and permutation contract | `sortRun_stable` |

The lower count is one final empty sort invocation, one sort entry per element,
and at least one insertion invocation per element. The upper count replaces each
insertion cost by its sorted tail's length plus one. A descending range attains
every such upper bound. Here `reverse(range n)` has length `n`; the source's list
`[n,n-1,...,0]` is the specialization at `n+1`. The exact formula includes empty
and singleton inputs, whose counts are 1 and 3. Nonincreasing lists with repeated
values are not asserted to attain the worst case: accepting an equal key stops
that insertion.

Statement review checked that the operations, erasure, permutation-derived
length and uniform count bounds require only a decidable relation. Pairwise
order suffices for the best-case result, without global order assumptions.
Pairwise rejection is the hypothesis for the generic worst-case result, and
the descending natural range proves it satisfiable at every length. The doubled
inequality and equality justify natural-number division in the triangular
formula. Sorting correctness is a separate use of the existing stable-sorting
contract and retains its linear-preorder and decidable-key assumptions; it
requires no order on payloads.

`Examples.InsertionCosts` connects the public results to independently computed
counts: `[1,1,2]` uses 7 calls, while `[2,1,0]` uses 10. It also checks insertion
at a tied head even when the later tail comparison would fail, traversal to the
end, empty and singleton input, the universal bounds, and keyed correctness
for arbitrary payloads without payload instances. A String instance checks
preservation of two distinguishable records sharing a key. Its selection client
uses the existing `Selection.pairwise_ranked` contract to obtain an occurrence
rank from the measured sort's output, including a repeated value. That client
observes a sorted result; it does not charge indexing or claim a complete
selection runtime bound. The connected small-input client pairs that rank with
the sorting-only bound of 21 calls for an input of length at most five, derived
from the general triangular inequality and the explicit length hypothesis.

## Appendix A: shared list interfaces, printed pages 343–345

This cross-cutting foundation reuses the existing Lean list carrier and
operations. The twenty source entries and all their displayed cases have the
following correspondence. Standard equation theorems are retained directly;
`Examples.ListLibrary` supplies the boundary and composition witnesses named
below. This source map does not itself assert completion of the independent
review and candidate-verification gates.

| Source entry | Existing value and equation witnesses | Checked use |
| --- | --- | --- |
| Length | `List.length_nil`, `length_cons` | `duplicate_pipeline`, `update_observations` |
| Append | `List.nil_append`, `cons_append` | Existing `Examples.FunctionalBasics.append_equations`; `split_reassembles` |
| Underlying set | `{x \| x ∈ xs}`, using `List.not_mem_nil`, `mem_cons` | `empty_membership_set`, `cons_membership_set` |
| Map | `List.map_nil`, `map_cons` | `duplicate_pipeline` |
| Boolean filter | `List.filter_nil`, `filter_cons` | `duplicate_pipeline`, `minimum_filter_spec` |
| Concatenation of a list of lists | `List.flatten_nil`, `flatten_cons` | `duplicate_pipeline`, including an empty inner list |
| Take | `List.take_nil`, `take_zero`, `take_succ_cons` | `split_reassembles`, `overlarge_split` |
| Drop | `List.drop_nil`, `drop_zero`, `drop_succ_cons` | `split_reassembles`, `overlarge_split` |
| Head of a nonempty list | `List.head?`, `head?_cons`; proof-domain `List.head` | `head_valid`, `empty_payload_queries` |
| Tail | `List.tail_nil`, `tail_cons` | `last_and_tail_boundaries`, `empty_payload_queries` |
| Remove last element | `List.dropLast_nil`, `dropLast_singleton`, `dropLast_cons_cons` | `dropLast_cons_equation`, `last_and_tail_boundaries` |
| Reverse | `List.reverse_nil`, `reverse_cons` | `duplicate_pipeline`; Chapter 1's separate measured realizations |
| Zero-based indexing | `List.getElem?_cons_zero`, `getElem?_cons_succ`; proof-domain `getElem` | `index_valid`, `invalid_index_and_update`, `empty_payload_queries` |
| List update | `List.set_nil`, `set_cons_zero`, `set_cons_succ` | `update_observations`, `update_repeated_value`, `invalid_boundary` |
| Half-open natural interval `[i..<j]` | `List.Ico`, `Ico.succ_top`, `Ico.eq_nil_of_le` | `range_zero_equation`, `range_succ_equation`, `range_boundaries`, `range_membership` |
| Replicate | `List.replicate_zero`, `replicate_succ` | `replication_boundaries` |
| Distinctness | `List.Nodup`, `nodup_nil`, `nodup_cons` | `duplicates_are_not_distinct` |
| Sum | `List.sum_nil`, `sum_cons` | `sum_source_equations`, `duplicate_pipeline` |
| Nonempty minimum | `List.min?`, `min?_singleton`, `min?_cons`; proof-domain `List.min` | `minimum_source_equation`, `minimum_valid`, `minimum_repeated_values`, `minimum_empty`, `empty_payload_minimum` |
| Sortedness for an arbitrary relation | `List.Pairwise.nil`, `List.pairwise_cons` | `sorted_wrt_cons`, `adjacent_relation_is_insufficient` |

The source's `concat` combines a list of lists and therefore corresponds to
`List.flatten`. Ranges include the lower endpoint and exclude the upper one;
`List.Ico i j` uses the truncated natural length `j-i`. Its checked successor
equation covers both `i ≤ j` and the empty alternative. Shape inspection for
drop-last uses `xs.isEmpty`, which distinguishes exactly the empty list without
requiring equality decisions on payloads.

The source supplies no invalid-input value equation for head, indexing or
minimum. Optional queries return `none` there. Their valid-input bridges return
`some` of the existing proof-domain result. Tail and list update retain their
specified total behavior: an invalid lookup returns `none`, while an invalid
update preserves the input, including its length and every position. The
source's zero-based index does not alter conaled's existing one-based public
selection interface.

Minimum's operation alone needs `Min α`; its source-style right-recursive law
also needs associativity because the standard realization folds from the left.
The book's linear-order specialization supplies that law. Leastness in
`minimum_filter_spec` separately requires a linear order and a successful
optional result; `filtered_minimum_example` discharges that premise on actual
data. Neither a top element nor a default payload is introduced. The checked
`Empty` cases demonstrate head/index failure and optional minimum with an
empty-domain `Min` operation. Sum has the different explicit capability
`Zero α`, so it cannot be instantiated at `Empty`; its literal equations need
only `Add α` and `Zero α`, without associativity or commutativity.

Distinctness and arbitrary-relation sortedness are propositional observations.
An executable Boolean view uses the corresponding decidability capability when
needed. `Pairwise` checks every later element. The checked relation `y = x+1`
on `[0,1,2]` satisfies adjacent comparisons but fails `Pairwise`, so transitivity
cannot be assumed merely from the word "sorted". The source's Boolean filter
already matches Lean's `α → Bool` interface.

Statement review retained arbitrary payload universes and the exact validity
conditions. The duplicate pipeline independently computes four flattened
elements, filtered-and-incremented values `[3,3,2]`, reverse `[3,1,2,2]` and sum
8. Update cases distinguish two equal occurrences by their positions. Minimum
with repeated values returns 2; the filtered-minimum client retains membership,
predicate satisfaction and leastness for the original input. Empty, singleton,
overlarge and reversed-boundary cases are covered without adding global
inhabitation or equality assumptions.

These are value correspondences. The standard reverse's accumulator
implementation does not inherit the naive source reversal's costs. The same
distinction applies to minimum's fold association and to other optimized
standard operations. Appendix B's separate cost recurrences remain separate
obligations.

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
