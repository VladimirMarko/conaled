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

**Accepted-base snapshot — 4 November 2026.** Chapter 1 was accepted at
`07e480f6ec9958d4975bb90151005b84f2907614`. The shared foundation was accepted at
`f17cc6b1a2bf44215b16202ed0fcee2b5c130761`, covering insertion costs, all twenty
Appendix A entries, Appendix B.1 and all ninety Appendix C notation rows.
The local tracker retains their complete validation and independent review
evidence. Later shared-unit and chapter acceptance requires its own matching
immutable-candidate gates; whole Appendix B remains open.

## Chapter order and scope

The full scope is all 27 chapters and appendices A–C. Mathematical definitions,
theorems and exercises need checked witnesses. Notation and explanatory material
need explicit correspondence and scope accounting. Existing results count only
when their statements, assumptions and algorithms actually match the source.
Chapter organization is a coverage index; modules follow reusable domain concepts.

| Chapter | Topic | Current implementation scope |
| --- | --- | --- |
| 1 | Basics | Accepted at `07e480f`; detailed witnesses below |
| 2 | Sorting | [112-obligation source correspondence](fdsa-sorting.md), including the selected stable Exercise 2.7; validation and acceptance tracked separately |
| 3 | Selection | Formalization in progress; see the [chapter correspondence](fdsa-selection.md) for coverage and remaining obligations |
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
| A | List Library | Accepted at `f17cc6b`; all twenty entries mapped below |
| B | Time Functions | B.1 accepted at `f17cc6b`; remaining subsections and whole-appendix acceptance pending |
| C | Notation | Accepted at `f17cc6b`; complete notation correspondence linked below |

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
review and intended connections for three additions:

- Uniform fine/coarse tariff bounds from a fixed finite local-case catalogue,
  with an exact append-branch client and both asymptotic directions.
- Omission of one nonrecursive entry under pointwise/eventual positivity,
  with zero and intermittently-zero counterexamples. Merely being
  non-identically-zero is insufficient.
- Actual shared-demand cache transitions, demanded-value agreement and a work
  bound against a finite eager catalogue, with external-program correspondence
  explicit and unshared duplication treated separately.

These source repairs were accepted with Chapter 1 at commit
`07e480f6ec9958d4975bb90151005b84f2907614`, after the full native build/audit,
both independent reviews and immediate candidate verification. The companion
tracker retains the exact evidence and earlier failed or unknown attempts. Section
1.5.3's preference for explicit bounds remains explanatory. Higher-order time
conventions refer forward to Appendix B.1 and stay on that appendix's list.

## Chapter 2: Sorting, printed pages 13–29

The [complete sorting correspondence](fdsa-sorting.md) retains all 112 frozen
obligations: C02-001–107 and the five operational clarifications C02-108–112.
It maps every section, display, named result and exercise to exact declarations,
connected examples, standard reuse or an explicit correction/proof-step
disposition. This is source correspondence at the recorded immutable candidate,
not a declaration of acceptance.

The ordinary algorithms preserve input multiplicities and establish pairwise
sortedness with their stated order laws. Keyed contracts preserve full records
and filtered equal-key subsequences. Exercise 2.7 selects the source floor-left
top-down sorter, with contiguous take/drop and the non-strict left-tie merge.
Alternating and reversed-pass variants retain ordinary correctness and their
explicit instability cases.

Measured insertion, merge, top-down, bottom-up and natural-sort recurrences
operate on actual returned children or runs. Comparison counts, function-entry
counts, append observations and the declared closure/scanner operational work
remain separate. The natural best-case development covers the actual one-run
output and zero merge comparisons, constant local closure creation, bounded
materialization, the full scanner and the stated zero/single-run final dispatch.
It makes no all-input operational merge or physical-runtime claim.

Both quicksort average assertions have source developments. Uniform input uses
one global uniform permutation of occurrence labels and conditional laws of
that same experiment. Fresh random pivot selects a new uniform occurrence
index at each nonempty recursive call. Actual integrability, child-value and
cost transport, rank laws and recurrence proofs lead to the harmonic formula
for the exercise tariff. Literal append-inclusive means have separate bounds.
Mapped-key distinctness, zero/one logarithm boundaries, duplicate quadratic
families and uncharged sampling/indexing overhead stay explicit.

The note records the source's early accumulator names, antisymmetry wording,
floor-left split, conditional logarithm domains and cost-model distinctions.
The public entrypoint adds 23 example imports while preserving the already
exposed shared foundations and probability units. The existing audit imports
that entrypoint and therefore includes the chapter through its normal dependency.
Exact compiler, exhaustive audit, independent Standards/Spec and immediate
candidate-verification outcomes remain in the local records. Accepted Chapter 1 and the independently accepted shared prerequisites are
preserved; the local records retain their exact acceptance evidence.
No later chapter is accepted by these Chapter 2 preparations.

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

## Shared list call counts — Appendix B.1

The seven primitive operations and seven exact properties on printed
pp.347–348 are mapped below. This is cross-cutting work used by subsequent
chapters; it does not complete Appendix B's algorithm-specific subsections.
The callback-bearing operations live in `Resources.ListCalls` and use the
existing `Resources.Measured`, `bind`, `pure` and `CallCount.tick` vocabulary.

| Source operation/property | Checked realization and result |
| --- | --- |
| Append equations and `n+1` | Existing `ListReversal.appendRun_nil`, `appendRun_cons`, `appendRun_exact` |
| Length equations and `n+1` | Existing `SymmetricCosts.lengthRun` and `lengthRun_exact` |
| Map equations and sum of callback costs plus `n+1` | `ListCalls.mapRun_nil`, `mapRun_cons`, `mapRun_value`, `mapRun_cost`, `mapRun_exact` |
| Filter equations and sum of predicate costs plus `n+1` | `filterRun_nil`, `filterRun_cons`, `filterRun_value`, `filterRun_cost`, `filterRun_exact` |
| Take equations and `min k n+1` | `takeRun_nil`, `takeRun_zero`, `takeRun_succ_cons`, `takeRun_exact` |
| Drop equations and `min k n+1` | `dropRun_nil`, `dropRun_zero`, `dropRun_succ_cons`, `dropRun_exact` |
| Valid zero-based lookup equations and `k+1` | `lookupRun_zero_cons`, `lookupRun_succ_cons`, `lookupRun_value`, `lookupRun_cost_of_lt`, `lookupRun_valid` |

Map retains independent input and output universes. Its callback supplies both
the actual mapped value and its natural-number observation; filter similarly
uses the returned Boolean to choose whether to retain the head. Each list
occurrence, including repetitions, contributes its callback observation once.
Both filter branches process the complete tail. The exact summed formula needs
no constancy, equality, ordering or inhabitation capability on the payload.
`filterRun_cost_eq_mapRun` relates only their cost projections. The constant-cost
specializations require constancy only on elements of the supplied input, and
give `(c+1)*n+1`. Knapsack's existing source map pays two units per cons; that
different model is unchanged and is not used for this correspondence.

Take and drop are value projections of the already verified `splitRun`, with
its observation preserved. Their individual source equations are checked,
including zero, empty and successor cases. `take_drop_separate` sequences two
operations on the original input through `bind` and proves twice the fused
split's observation. It does not apply drop to the returned prefix. Equality
of the pair of output lists is therefore kept separate from equality of costs.

Lookup recursively follows the list, with no random-access substitution or
default element. The source gives no empty-input cost equation. This optional
extension explicitly chooses `(none,1)` there; `lookupRun_cost` proves the
extension's total count `min k n+1`. Only `lookupRun_cost_of_lt`, under `k<n`,
is the printed exact-cost property. `lookupRun_valid` connects the optional
result to `some` of the standard proof-domain indexed element and the valid
count. The first invalid index reaches the empty list and costs `n+1`; larger
invalid indices have the same extension count. Those failure counts are not
attributed to the book.

Statement review compared the definitions, branch behavior, explicit validity
domain, quantifier universes, and observations with the source recurrences.
The initial missing connection was that standard list values and the existing
Knapsack tariff did not supply these measured-callback equations; a plain
evaluation example could not fill that proof obligation. The retained checked
clients in `Examples.ListCalls` use the new public exact results:

- Mapping `[2,2,3]` with `(x+10,x)` gives `([12,12,13],11)`. Filtering either
  `[2,2,3]` or `[3,2,2]` with `(x≤2,x)` gives `([2,2],11)`. The second filter
  case checks that discarding the head preserves the later retained elements.
- Zero- and unit-cost callbacks on three elements cost 4 and 7. Filtering out
  every element with a unit-cost callback still costs 7.
- `map_then_length` composes the actual mapped result with the existing measured
  length, with independent payload universes. The concrete callback case costs
  `11+4=15`. `append_then_length` similarly combines existing append and length
  without duplicating either realization.
- Lookup of position 2 in `[4,4,9]` returns `(some 9,3)`. Positions 3 and 20
  return `(none,4)` under the declared extension. Empty lookup works at `Empty`.
- Taking and dropping two elements of `[1,2,3]` each costs 3; the sequential
  pair costs 6 and the fused split costs 3. Zero, empty-payload and overlarge
  counts are checked separately.

These definitions and examples remain subject to complete candidate validation
and independent review before acceptance. Cost observations concern the stated
recursive model, not execution time of standard-library list operations.

## Shared affine recurrence groundwork

`Resources.AffineRecurrence.exists_affine_bound_of_two_branch` supplies a
uniform all-input affine upper bound for an already total scalar function.
Its two natural child maps have a strictly contracting eventual sum bound;
its recurrence and toll are upper bounds. The scalar carrier is an
Archimedean linearly ordered commutative ring, with signed function values
and signed tolls allowed. Ordinary finite maxima, natural multiples and strong
induction provide the witnesses; no recurrence structure or executor is added.

`Examples.AffineRecurrence` connects the theorem to the actual terminating
quarter-size recurrence over rational casts, a signed integer recurrence, and
parameter-uniformity boundaries. The finite prefix, including zero, is covered
by the same constants as every later input. A one-sided order bound is kept
distinct from an absolute-value or asymptotic norm bound.

At the 4 November 2026 receiving-preparation snapshot, both independent
assessments of the original source were complete with no new XR source findings;
the unit had no compiler, expanded-type, guarded-full-check or audit result.
Current receiving validation and acceptance are recorded in the local
`fdsa-control` review and acceptance evidence. Its
[source and statement notes](fdsa-affine-recurrence.md) preserve Chapter 3's
remaining exact ceiling and negative-offset laws, sharper source constant
choices, selector-to-cost correspondence and noncontracting counterexample.
This groundwork does not activate or accept Chapter 3, and it does not prove
termination of an algorithm by merely enlarging a later proof cutoff.

## Architecture and statement review

Appendix C's complete notation correspondence, source corrections and checked
semantic boundaries are recorded in [the notation map](fdsa-notation-map.md).
It reuses these list and foundation interfaces rather than introducing source
editor syntax as a second notation layer.

Operations, returned values and observations remain separate. Exact agreement
uses ordered lists, so duplicates and order are preserved. Costs require their
own recurrence proofs and are not transported from semantic equality. The
realizations are optional and do not impose an allocation or storage capability
on other targets. These are ordinary Lean/Type results; no cross-setting
interpretation of these new induction proofs is claimed.

For Chapter 1, the only existing public-interface adjustment is the universe
signature of `Resources.erasureSquare`. Its value carriers may now live above the cost type;
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

## Shared ordinary list merge observations — FDSA-XM01

`Applications.Sorting.Merge` adds the two order-free input sublists, arbitrary-
relation pairwise converse and the input-local keyed sortedness iff, preserving
its existing operation/forward/stability contracts. `Resources.ListMerge.run`
is one actual selected-branch execution with comparison/invocation observations.
Its first cost coordinate (`run.2.1`) has the handwritten C_merge equations;
its second cost coordinate (`run.2.2`) counts all merge entries, including the
terminal base. Exact erasure, E=C+1, loose length bounds and input-local exact
map/key transport retain arbitrary payload universes and require no sorting,
equality or inhabitant on the raw domain.

This supports C02-025, the merge portion of C02-027, and C02-028/029/031/033/035/037.
`Examples.MergeCosts` connects actual bind/reweight, the second merge's real
first value, source/key adapters, stable and unsorted cases, noninjective key
erasure, Empty, the qualified C1 positive/zero comparison, and an actual raw
LeftistQueue.toListQ node body. That body's counts concern only its one merge
of already obtained child lists. Full child/traversal work is not included.

The prescribed C2 merge/comparison model and chosen C14 exercise components
are distinguished in [the source note](fdsa-list-merge.md), with pinned sources,
license and full observation boundaries. The original 107/current 112 C2
requirements are unchanged; their whole-sort, logarithmic, run/builder, exercise
and stability source clients are mapped in [fdsa-sorting.md](fdsa-sorting.md).
All concrete C14 queue/whole-enumeration/carrier
and quadratic claims remain queued, and binomial carry is a different operation.
The original foundation prefix c80eec9 excludes this later component.
The source note retains a dated validation snapshot; acceptance requires the
complete immutable-candidate gates recorded in the local FDSA-XM01 record.

## Shared difference-list closure groundwork

`Resources.DifferenceListCosts` adds ordinary measured suffix callbacks with
separate ordered-prefix and application-cost predicates. Identity, singleton
and composition callbacks have a declared invocation tariff; their creation
operations carry a separate fixed-size capture tariff. Existing `run` executes
compositional pushes. The seed-general construction laws imply `2*n+1` for
creation and one application of the identity-seeded builder.

The value representation remains Batteries.DList. Its fused push and the
explicit compositional model have value correspondence, with no transfer of
exact costs. Connected cases retain nonempty suffixes, duplicate/order
preservation, empty payloads, repeated materialization, charged identity and
empty-prefix histories with unbounded application work. Shared self-composition
distinguishes distinct creation events from unfolded invocation occurrences.

This cross-cutting source component is included in the active Chapter 2
candidate. The [source and statement notes](fdsa-difference-list-costs.md) retain
its closure model; the [sorting correspondence](fdsa-sorting.md) maps the actual
singleton-seeded ascending worker/scanner and ordinary append/reverse clients.
Local candidate/review records distinguish focused evidence, source corrections
and pending full gates. The abstract observations do not imply compiler or
machine-runtime bounds, and this source map does not accept the chapter.

The source note retains a dated validation snapshot; full immutable-candidate
acceptance gates remain required.

## Shared three-way partition values and source execution (FDSA-XQ01)

This bounded cross-cutting component exposes the existing independent
partition semantics to Sorting and Selection, with a separately measured
one-pass realization for Appendix B.2. It does not accept either chapter
or widen the initial Chapter 2 foundation prefix. Exact provenance,
source/model distinctions, interface compatibility and cases are in
[fdsa-three-way-partition.md](fdsa-three-way-partition.md).
The source note retains the dated validation history; it does not substitute
for this unit's full candidate gates.

| Common source obligation | Draft declarations / intended connection |
| --- | --- |
| Three ordered filters and occurrence semantics, partition component of C02-102 and C03-011 | `Sequences.Partition.partition3` retains the existing two-stage value body, exact filter/perm/membership/length laws and standard nested tuple. |
| Qualified strict-side decrease, C03-013 | Existing `partition_strict_sizes` retains pivot membership as a sufficient premise. Arbitrary-pivot correctness remains unconditional. |
| Existing Selection compatibility | The old same-signature operation and seven theorem names remain wrappers/adapters. The selection-specific remainder, Rank, Consumers and RankSelection examples are unchanged. |
| Companion source value equations | Shared nil/cons theorems expose one-tail reconstruction with tests `y<p` then `p=y`, without defining another pure operation or assigning a cost to the old implementation. |
| Actual source count, C03-031 and B-018/019 | `Resources.Partition.partitionRun` uses one recursive tail call and its actual returned triple; separate value and count laws give the shared value and work `length+1`, including nil. |
| Consequential clients | Generic equal-block/empty cases; mixed ordered duplicates; absent outside/interior pivots; old-name compatibility; same-program bind on the actual returned lower bucket with expected total thirteen. |

The manuscript prints the three-filter specification and time recurrence;
the pinned companion supplies the explicit single-pass code equation. The
old two-pass value implementation, new actual source program and Exercise
2.4's two-filter quicksort metric remain distinct. No physical runtime,
tail-recursion, constant stack or arbitrary monotone bucket-transport claim
is introduced.

Chapter 2's complete quicksort3 and actual random-quicksort source developments
are mapped in [fdsa-sorting.md](fdsa-sorting.md). Selection rank/middle-index
bridges, actual selector recursion and termination, median-of-medians and its
random policies/total costs remain mandatory in their original chapters.
Accepted repaired Chapter 1 is preserved. The full candidate build/audit, both
independent review axes and immediate candidate verification remain required;
no source preflight or authored draft supplies acceptance evidence.

## Shared fixed-subset minimum probability (draft)

The [uniform-permutation minimum unit](fdsa-permutation-minimum.md) supplies a
source draft of the probability that a member of a fixed finite subset is
first under one global uniform permutation of injective priorities. It uses
ordinary permutations, finsets and Mathlib measures, with no new probability
carrier. Its examples connect the general theorem to overlapping subsets,
infinite-target integer priorities, empty indices, outsiders and ties.

This groundwork supports Chapters 2 and 10. It does not supply conditional
pivot/subproblem laws, full relative-order restrictions, the expected first
position, treap construction/ancestor/charging proofs or algorithm cost
correspondences by itself. The Chapter 2 algorithm clients of this and the
later order/tail units are mapped in [fdsa-sorting.md](fdsa-sorting.md).
Its source note retains a dated validation snapshot;
the local FDSA-XU01 record retains the frozen scope and subsequent gate results.

## Shared whole-subset ordering (draft)

The [relative-order unit](fdsa-permutation-order.md) connects the actual
inverse-permutation/list-filter observation to the uniform law on every
order of a fixed subset. Its value contracts retain exact membership,
distinctness, support, a mapped-sublist order bridge and repeated-filter
composition. The source-event probability and Measure.map semantics have
separate measurable hypotheses; a complete position list supplies finiteness
locally. The connected examples use complete triple outputs, mapped meaning,
nested filtering and empty/orientation/invalid-enumeration boundaries.

This is further shared groundwork for Chapters 2 and 10. Conditional
histories, adaptive subsets, joint independence, expected positions, algorithm
semantics and actual costs remain separate obligations. Chapter 2's actual
algorithm clients are mapped in [fdsa-sorting.md](fdsa-sorting.md); they do not
postulate a joint independence law. The source note retains the 4 November 2026 development validation history;
the local FDSA-XU02 record retains the frozen exact scope and subsequent
candidate/review evidence. Full immutable-candidate acceptance gates remain
required.

## Shared conditional remaining orders (draft)

The [conditional-tail unit](fdsa-permutation-tail.md) connects a specified
optional head to the law of the actual remaining list. Its existing HasLaw
premise permits an arbitrary current environment measure, so the result can
be reused after a prior conditioning without assuming the full environment
is again uniform. Fixed remaining-subset filtering composes this observed
law, and explicit global-permutation source-fiber/map specializations retain
their separate measurable hypotheses and on-event value bridges.

The examples include two successive reveals, a changed environment with a
uniform observed tail, actual filtered projections, null conditioning and a
counterexample to weakening subset containment. Chapter 2's actual child-filter,
conditional-mean and cost recurrence clients are mapped in
[fdsa-sorting.md](fdsa-sorting.md). Complete history and Chapter 3 algorithm,
sampling-coupling and cost obligations remain separate. The source note retains the 4 November 2026 development validation history; full immutable-candidate acceptance gates remain required. Local FDSA-XU03 retains the frozen scope, exact expectations,
candidate identity and later validation/review evidence.

## Shared binary-tree observations and cached folds (FDSA-XT01)

This bounded cross-cutting unit supplies common observations
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
their chapter inventories. The original XT01 source now has complete independent
Standards and Spec source assessments with zero findings, both overall Blocked
pending actual receiving-candidate compilation, types, full check/audit and final
review. The current receiving base is accepted Chapter 3 commit
`298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`; all unit and chapter acceptance
gates remain. This shared entry does not close the Chapter 4 coverage ledger.
