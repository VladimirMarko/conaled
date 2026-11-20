# Priqueue: maximum occurrences, source lists and measured comparisons

This note records the Lean correspondence for the complete `Priqueue` chapter
of *Verified Functional Algorithms*. CTB-96 continues CTB-16 under the standing
three-book task and receiving issue #558. It covers the relational signature,
the actual unsorted-list implementation, both exercises, the observation
adapter and the chapter's qualified resource claims. Source qualification
requires the frozen checks and both independent review axes. Once those gates
pass, Priqueue brings VFA to 14 of 17 units including Preface; Binom, Decide
and Color remain. All outstanding FDSA/PFDS chapters and appendices, the
whole-library checks and receiving acceptance remain open. Binom implementation
starts only after Priqueue is accepted and its recovery checkpoint is secured.

## Source and maintained owners

The primary source is the `vfa/Priqueue.v` member of VFA edition 2.1, dated
2026-08-24 10:11 at the archive level. The archive SHA-256 is
`f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
The member has 9,029 bytes and 273 lines, SHA-256
`e4dc740bf2c3f338dedae3e6544a8d94d58fd80f810472610122b9ccc4866b9d`.
The complete primary and [canonical plan](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1014-Priqueue.md)
were read, including surrounding prose, the inner admission and the commented
module-ending experiment. The plan has SHA-256
`0028ed8013db98fb62e365eb31153ab5030d027bc9a3b9d06f7e8fbb43a42c7d`.
The retained [lexical inventory](../history/textbooks/checkpoint-012/books/vfa/records/research/source/vfa-source-inventory.json)
identifies 43 declarations, two grouped exercises, two modules and no
pedagogical commands. The historical inventory is not an acceptance record.
The retained [MIT notice](../licenses/vfa-MIT.txt) applies; downloaded primary
bodies remain outside the recovery payload.

| Maintained owner | Responsibility |
| --- | --- |
| [MaximumQueue](../../Applications/Search/MaximumQueue.lean) | Four Nat-key operations, the eleven guarded relational laws, witness/count/maximum consequences, explicit observation and valid-state adapters. |
| [ListMaximumQueue](../../Applications/Search/ListMaximumQueue.lean) | Exact dual source selector, ordinary list carrier, identity abstraction, complete law bundle and raw-list ExactQueue realization. |
| [ListPriorityQueue](../../Applications/Resources/ListPriorityQueue.lean) | Actual measured comparison-first selection, deletion and append; exact counters, erasure, weighted bounds and explicit non-unit comparison work. |
| [MaximumQueueContract](../../Examples/MaximumQueueContract.lean) | Constructive guarded Option-list implementation, invalid-state boundaries, complete laws and occurrence-preserving adapter clients. |
| [ListMaximumQueues](../../Examples/ListMaximumQueues.lean) | Exact source branches/remainders, repeated maxima, identity-versus-permutation boundary and public source/adapter laws. |
| [ListPriorityQueueWork](../../Examples/ListPriorityQueueWork.lean) | Actual measured operation compositions, exact work vectors, changing-candidate unary comparisons and qualified asymptotic families. |
| [MaximumQueueClients](../../Examples/MaximumQueueClients.lean) | One build/native-merge/two-removal client instantiated for source lists and the accepted leftist queue. |

Existing `SourceSelection` supplies the comparison-first recursion and its
generic permutation/order proofs. `Sequences.Multiplicity` supplies occurrence
observations. `PriorityInterface.ExactQueue` remains the common exact-entry
interface, and `exactLeftist` supplies the second queue realization.
`Resources.SelectionSort`, `ListAppend`, `UnaryComparison` and `Growth` supply
the accepted measured projections and bound-to-asymptotics bridge. No new
heap, key-replacement map, generic order hierarchy or runtime harness is added.

## The source contract and its observation boundary

`Search.MaximumQueue.Operations Q` contains exactly `empty`, `insert`,
`deleteMax` and native `merge`. The raw carrier `Q : Type u`, validity
predicate and abstraction relation remain ordinary separate parameters.
Keys are exactly `Nat`. Insertion adds one occurrence, including repeated
keys. Deletion returns `Option (Nat × Q)`, so key zero is distinct from
absence. Native merge belongs to this source signature even though the
existing minimum-queue operations record has no meld field.

`Laws ops Valid Abs` has exactly eleven fields. It preserves every validity
guard and abstraction witness from the source. In particular, successful
deletion states an input-to-output cons permutation and an upper bound on
the residual observation. Merge relates **any actual output witness** to
the appended input witnesses. It does not demand that the literal append
be an abstraction witness for every implementation. The source Axiom
declarations become fields of a proved contract, and `ListMaximumQueue.laws`
discharges every field for actual source functions.

The proved `Laws` consequences answer the source's specification question.
Every valid state has an abstraction witness, and witnesses for the same
state determine the same multiset and occurrence function. An empty-state
witness must be `[]`. For any given valid input witness, deletion returns
None exactly when that witness is empty. Successful deletion establishes
residual validity, obtains a residual witness and proves the returned key
occurs in the original input and bounds every original key. The occurrence
and size equations are

\[
\operatorname{count}_a(pl)
=\operatorname{count}_a(ql)+[a=k],\qquad
|ql|+1=|pl|.
\]

Merge preserves validity, supplies an output witness, adds every key count,
adds lengths and agrees with finite-multiset addition. These are occurrence
contracts: membership sets alone would identify `[7,7]` with `[7]` and lose
the behavior of the second deletion. A general empty observation does not
identify a raw state with `ops.empty`; no such equality theorem is claimed.
The contract likewise does not assert physical sharing, observation cost,
payload stability or identical residual shapes between implementations.

The concrete source `Abs` is equality of lists. `abs_intro`, `abs_eq` and
`abs_iff` give the source constructor and its elimination/characterization
without introducing a second identity relation datatype. `[1,2]` and `[2,1]`
are permuted and have the same occurrence observation, but they do not satisfy
the concrete identity relation. Witness uniqueness up to permutation is
weaker than requiring every permutation to be a witness.

`MaximumQueueContract` constructs a complete second source contract on
`Option (List Nat)`. The malformed raw state `none` is invalid and deliberately
violates an unguarded empty-observation law; valid `some` states execute the
actual source list operations. All eleven guarded fields are proved. This
checks why the generic adapter cannot assume that all raw states are valid.

## Exact source recurrence and complete list realization

`selectMax seed tail` is definitionally the accepted `SourceSelection.select`
at the relation `head ≤ candidate`, equivalently at `OrderDual Nat`'s order.
This is a change of comparison, with no preprocessing traversal. On an empty
tail it returns `(seed, [])`. On `head :: tail`, it decides `head ≤ seed`
before the recursive call: the true branch recurses with the same seed and
prepends head to the returned remainder; the false branch recurses with head
and prepends the displaced seed. Equality takes the true branch.

The exact source equations give `selectMax 2 [1,3] = (3,[1,2])` and
`deleteMax [3,1,2] = some (3,[1,2])`. A tail-first selector or a sorted-deletion
queue can have the same maximum and multiset with a different remainder.
Those observational agreements do not replace this source recurrence.

`select_perm` uses the accepted generic permutation theorem in the source's
input-to-output orientation. `select_length` and `select_mem` preserve every
occurrence independently of order assumptions. The extremum theorems use the
actual reversed natural order. `select_biggest_aux` retains the source's
redundant Forall premise and concludes that the seed is bounded by the chosen
key. `select_biggest` proves the Forall bound on the exact returned remainder.
The stronger `select_maximum` bounds every original key. The source comment's
stale auxiliary-lemma name is replaced by reuse of the actual accepted seed
theorem; no proof hole is carried over from either source admission.

The source queue carrier is `List Nat`. Empty is `[]`, insertion is cons,
nonempty deletion returns Some of the actual selector result, and merge is
append in the supplied operand order. Validity is True for every raw list.
Each individual concrete source law is exposed, then assembled into `laws`.
`deleteMax_relate_forall` additionally exposes the source's literal Forall
presentation, equivalent to the membership-bound field in the shared contract.

## All 43 source declaration records

In the table, `MQ` abbreviates namespace `Search.MaximumQueue`, and `LQ`
abbreviates `Search.ListMaximumQueue`. These abbreviations are documentation
only. Every source ID appears once and in source order.

| Source record | Actual Lean correspondence |
| --- | --- |
| `Priqueue.PRIQUEUE.priqueue@67` | Ordinary parameter `Q : Type u` of `MQ.Operations` and `MQ.Laws`. |
| `Priqueue.PRIQUEUE.key@68` | Exact `Nat` specialization in all four operation fields and `LQ.Key`. |
| `Priqueue.PRIQUEUE.empty@70` | `MQ.Operations.empty`. |
| `Priqueue.PRIQUEUE.insert@71` | `MQ.Operations.insert : Nat → Q → Q`. |
| `Priqueue.PRIQUEUE.delete_max@72` | `MQ.Operations.deleteMax : Q → Option (Nat × Q)`. |
| `Priqueue.PRIQUEUE.merge@73` | `MQ.Operations.merge : Q → Q → Q`, retained as native merge. |
| `Priqueue.PRIQUEUE.priq@75` | Separate `Valid : Q → Prop` parameter of `MQ.Laws`. |
| `Priqueue.PRIQUEUE.Abs@76` | Separate `Abs : Q → List Nat → Prop` parameter of `MQ.Laws`. |
| `Priqueue.PRIQUEUE.can_relate@77` | `MQ.Laws.can_relate`, guarded witness existence. |
| `Priqueue.PRIQUEUE.abs_perm@78` | `MQ.Laws.abs_perm`, guarded witness permutation. |
| `Priqueue.PRIQUEUE.empty_priq@80` | `MQ.Laws.empty_valid`. |
| `Priqueue.PRIQUEUE.empty_relate@81` | `MQ.Laws.empty_relate`, with no extra premise. |
| `Priqueue.PRIQUEUE.insert_priq@82` | `MQ.Laws.insert_valid`. |
| `Priqueue.PRIQUEUE.insert_relate@83` | `MQ.Laws.insert_relate`, literal relation to the cons witness. |
| `Priqueue.PRIQUEUE.delete_max_None_relate@85` | `MQ.Laws.deleteMax_none`, both directions with the validity guard. |
| `Priqueue.PRIQUEUE.delete_max_Some_priq@87` | `MQ.Laws.deleteMax_valid`. |
| `Priqueue.PRIQUEUE.delete_max_Some_relate@89` | `MQ.Laws.deleteMax_relate`, input-to-output permutation and residual upper bound with all witnesses. |
| `Priqueue.PRIQUEUE.merge_priq@95` | `MQ.Laws.merge_valid`, requiring both valid inputs. |
| `Priqueue.PRIQUEUE.merge_relate@96` | `MQ.Laws.merge_relate`, quantifying over an actual result witness. |
| `Priqueue.List_Priqueue.select@129` | `LQ.selectMax`, `selectMax_eq_source`, `selectMax_eq_dual`, `selectMax_nil` and `selectMax_cons`. |
| `Priqueue.List_Priqueue.select_perm@139` | `LQ.select_perm`; exact selected pair and source permutation orientation. |
| `Priqueue.List_Priqueue.select_biggest_aux@147` | `LQ.select_biggest_aux`, preserving its redundant Forall premise. |
| `Priqueue.List_Priqueue.select_biggest@155` | `LQ.select_biggest`; both inner and final source admissions are replaced by the actual proof. |
| `Priqueue.List_Priqueue.key@170` | `LQ.Key := Nat`. |
| `Priqueue.List_Priqueue.priqueue@172` | `LQ.Queue := List Key`. |
| `Priqueue.List_Priqueue.empty@174` | `LQ.empty`, `empty_eq`. |
| `Priqueue.List_Priqueue.insert@175` | `LQ.insert`, `insert_eq`; exact cons insertion. |
| `Priqueue.List_Priqueue.delete_max@176` | `LQ.deleteMax`, `deleteMax_nil`, `deleteMax_cons`. |
| `Priqueue.List_Priqueue.merge@181` | `LQ.merge`, `merge_eq`; exact operand-order append. |
| `Priqueue.List_Priqueue.priq@192` | `LQ.Valid`, `valid`; True on every raw source list. |
| `Priqueue.List_Priqueue.Abs'@196` | `LQ.Abs`, `abs_intro`, `abs_eq`, `abs_iff`; equality realizes the one-constructor identity relation. |
| `Priqueue.List_Priqueue.Abs@199` | The same `LQ.Abs` identity relation, with no permutation saturation. |
| `Priqueue.List_Priqueue.can_relate@204` | `LQ.can_relate`, using the list itself as witness. |
| `Priqueue.List_Priqueue.abs_perm@214` | `LQ.abs_perm`, from equality of both witnesses. |
| `Priqueue.List_Priqueue.empty_priq@224` | `LQ.empty_valid`. |
| `Priqueue.List_Priqueue.empty_relate@227` | `LQ.empty_relate`. |
| `Priqueue.List_Priqueue.insert_priq@230` | `LQ.insert_valid`, retaining the input validity premise. |
| `Priqueue.List_Priqueue.insert_relate@233` | `LQ.insert_relate`, exact identity witness after cons. |
| `Priqueue.List_Priqueue.delete_max_Some_priq@237` | `LQ.deleteMax_valid`, retaining the actual successful deletion premise. |
| `Priqueue.List_Priqueue.delete_max_None_relate@243` | `LQ.deleteMax_none`, identity-to-empty iff the actual result is None. |
| `Priqueue.List_Priqueue.delete_max_Some_relate@249` | `LQ.deleteMax_relate` and `deleteMax_relate_forall`, substituting both identity witnesses and using the selector proofs. |
| `Priqueue.List_Priqueue.merge_priq@258` | `LQ.merge_valid`; the source-proved member of the second exercise is included. |
| `Priqueue.List_Priqueue.merge_relate@262` | `LQ.merge_relate`, exact append after identity substitutions. |

## Exercises, modules and remaining prose

| Source obligation | Disposition |
| --- | --- |
| `select_perm_and_friends`, 137–165, standard, three stars | All three source selector theorems are proved through the exact operation bridge, including the auxiliary premise and the inner admission in `select_biggest`. Exact remainder, permutation and upper-bound cases consume them together. |
| `simple_priq_proofs`, 241–269, standard, two stars | None iff empty abstraction, successful deletion, merge validity and merge abstraction are proved and consumed by the complete `laws` bundle. No optional or advanced exercise is omitted. |
| `From VFA Require Import Perm`, 64 | Accepted Lean permutation, Forall and decidable-reflection APIs replace the source import and tactic infrastructure. |
| `Module Type PRIQUEUE`, 66–101 | Four supplied operations plus eleven guarded proof fields on the separate carrier, validity and abstraction parameters. |
| `Module List_Priqueue <: PRIQUEUE`, 111–271 | `LQ.ops` and the fully proved `LQ.laws` instantiate the complete source signature. |
| Commented premature End, 113–121 | The completed law-bearing construction demonstrates the obligation to supply every field. The commented line is not an actual Fail command; no broken module or expected diagnostic string is added. |
| Applications and implementation comparison, 3–49 | Maximum Nat matches the chapter's convention. Earliest-event and shortest-path uses require the appropriate priority order. The heap/BST repeated-removal/insertion merge strategy is not a universal lower bound for native meld; keyed dictionaries require occurrence handling. These motivating applications do not request new algorithms here. |
| Comparison discussion, 53–62 | Unit comparison count is separated from actual comparator work. The explicit unary refinement below is a declared model, not a native Lean Nat runtime claim. |
| Specification adequacy, 103–106 | The proved witness, occurrence, maximum, size and merge consequences, plus the guarded-state example, establish the stated behavior and its boundaries. |
| Proof adaptation and `bdestruct`, 126–164 | Exact source duality and ordinary decidable reflection replace source tactic syntax; the stale auxiliary reference and both levels of admissions are handled explicitly. |
| Trivial representation and abstraction order, 188–219 | True validity and identity abstraction implement the actual lists. Interface witness permutation does not require permutation closure of a concrete relation. |
| Operation characterizations, 224–269 | Every source theorem supplies its corresponding proved law field, preserving Some/None cases, both merge guards and all abstraction witnesses. |

There are zero inventoried Check/Print/Compute/Extraction commands in this
chapter. Actual Lean type inspections and connected executions belong to the
formalization evidence; they do not manufacture a source command inventory.

## Exact occurrence adapter and interchangeable clients

`MQ.encode k = ((), OrderDual.toDual k)` and `decode` are inverse on
`Unit × OrderDual Nat`. The priority inequality is exactly reversed:
`(encode a).2 ≤ (encode b).2 ↔ b ≤ a`. `encodedOperations` retains the supplied
carrier and directly folds the provided entries for insertion; its deletion
maps the actual source result. It does not preprocess or sort the raw state.

An explicitly supplied observation and its abstraction-witness proof connect
the relational source contract to `ExactQueue`. `exactQueueOfAllValid` keeps
the raw carrier when all states are valid. In general, `validOperations`
restricts execution to `{q // Valid q}` and obtains the residual proof from the
actual successful source result. `validLaws` proves the full relational
contract on that subtype, and `exactQueueOnValid` then supplies the existing
exact interface. The raw operation projection theorems preserve all four
source operations, including native merge. No arbitrary abstraction witness
or queue representative is selected by an executable operation.

`LQ.exactQueue` takes the all-valid route with identity observation. Its
entries are the list mapped to Unit/dual priorities. `exactQueue_add_keys`
describes the actual insertion fold as append; the map occurs in the
mathematical observation or caller's supplied entries, not as an inserted
raw-queue traversal. `exactQueue_native_merge` separately observes source
append, because ExactQueue has no meld operation.

The shared `MaximumQueueClients` client builds `[7,2,7]` and `[7,0]`, performs
the implementation's native merge and proves that two successful removals
exist. Both returned priorities decode to 7. The first residual has two
copies of 7; the second has one and is observed as a permutation of `[2,7,0]`.
The proof consumes the existing exact interface's bound on every original
entry, residual validity and occurrence permutation. It runs unchanged for
the source list queue and `exactLeftist` under order duality.
`interchangeable_two_removal_client` connects both actual removal sequences
and proves permutation of their final observations. Their carrier states and
raw residual shapes are not equated.

## Measured execution and resource claims

`Resources.ListPriorityQueue.selectRun` executes the comparison before choosing
the recursive candidate. Its comparator returns `Measured Bool Nat`; the
returned Boolean drives the actual branch, and the returned work contributes
to the actual run. It exposes four independent coordinates: source calls,
comparison invocations, comparator work and source cons constructions.
Pairs and Options are uncharged. Empty/insertion each receive one operation
entry charge. Deletion charges its own entry and the invoked selector calls.
Merge reprices accepted recursive append, including its terminal invocation,
with no extra charge for the source merge alias.

`selectRun_value` and `selectRun_realizes` erase to the accepted exact
recurrence. `selectRun_unit_projection` agrees in result and comparison count
with the already accepted `Resources.SelectionSort.selectRun`.
`selectRun_source`, `deleteMaxRun_source` and the other source erasure theorems
connect the measured runs to all four actual list operations. `mergeRun`
reuses `ListAppend.copies`; its copy projection is exact. Generic occurrence,
length and one-copy deletion laws do not assume a lawful comparator.

Let `n` be the selector's tail length, `N` the whole queue length, `m` the
left merge length, and `W` the actual sum of comparator work along the run.
These sizes and observations are distinct.

| Actual operation | Calls | Comparisons | Comparator work | Source cons constructions |
| --- | ---: | ---: | ---: | ---: |
| Empty | 1 | 0 | 0 | 0 |
| Insert | 1 | 0 | 0 | 1 |
| Select on tail length `n` | `n+1` | `n` | `W` | `n` |
| Delete from length `N` | `N+1` | `N−1` | `W` | `N−1` |
| Merge with left length `m` | `m+1` | 0 | 0 | `m` |

Subtraction is natural subtraction, so the delete equations include both
empty and singleton queues. Both have zero comparisons, but their Option
results and call counts differ. Ties and an already maximal seed still visit
the entire selector tail. Successful deletion's residual length is also
proved from its actual permutation, independently of the cost observation.

For nonnegative weights `a,b,c,d` on these four coordinates, the exact prices
are `a` for empty, `a+d` for insertion,
`a(n+1)+bn+cW+dn` for selection,
`a(N+1)+b(N−1)+cW+d(N−1)` for deletion, and `(a+d)m+a` for merge.
`price_add` composes measured runs. A local comparator bound `C` on pairs of
occurrences in the original input proves `W ≤ C*n`; the induction preserves
the input predicate when the actual candidate changes. A global bound is a
specialization of this local premise. The linear coefficient is
`a+b+c*C+d`, yielding the stated selector/deletion size envelopes.

`selectRun_price_isBigO`, `deleteMaxRun_price_isBigO` and
`mergeRun_price_isBigO` apply the accepted natural-bound bridge only after
these execution equations and inequalities. They quantify over actual
families, with explicit size bounds and a uniform comparator-work bound.
The right merge family is unrestricted because append traverses only the
left spine. Merge therefore has an upper bound in total input length as
well, but no total-size lower bound holds for every split: empty-left merge
has one call and zero copies for arbitrarily large right lists.
`merge_no_total_lower` proves this separator, while `mergeRun_growing_left`
attains exactly `m` copies. Swapping `[1,1]` and `[2]` preserves the multiset
but changes copied cons from two to one.

The non-unit refinement uses the accepted lockstep unary `≤` execution,
called on `(head,candidate)` in the source's non-strict orientation. Its
work is `min head candidate + 1`. Keys bounded by `M` yield per-call bound
`M+1`. Actual changing-candidate selection of `2` against `[1,3]` has work
5; deletion from `[2,7,7,4]` has three comparisons and work 16, with the same
source result as unit comparison. Equal-key queues of length two have work
`key+1`, and `unary_fixed_length_unbounded` proves that fixed list length
alone cannot bound this comparator work. Native Lean Nat representation and
hardware timing are not inferred from the unary model.

## Connected cases and acceptance evidence

The source cases distinguish empty from zero, both comparison branches and
ties, exact remainders, two repeated-maximum removals and duplicate-rich merge.
They use source permutation/Forall laws, selected membership, original upper
bounds, one-occurrence count loss and residual length. Identity abstraction
is checked against a nontrivial permutation. A tagged-payload tie exposes the
generic selector's actual choice without claiming cross-implementation
payload stability. An arbitrary equality relation preserves occurrences but
fails the corresponding extremum property.

The measured examples compose two deletions with the actual first residual,
and append-merge followed by deletion with the actual merged value. They
check exact vectors, endpoint costs, every-tie traversal, source erasure,
copy asymmetry, independent carrier/key universes, explicit unary prices and
real asymptotic families with their required bounds. No native-evaluation
shortcut substitutes for a proof. The guarded implementation and common
list/leftist client separately check validity scope and representation reuse.

These syntactic counts are not allocation, sharing, garbage collection,
peak-live-space, stack or wall-clock theorems. Priqueue requests no benchmark.
The later Binom measurement exercise retains its own actual workloads,
repetitions, timing and saved-result obligations. Existing secured runtime
executions retain their original identities; checkpoint044 retention is not
a new runtime execution.

[CTB-96](../textbooks/CTB.json) retains Priqueue's historical donor qualification;
CTB-78 owns current receiving validation and independent Standards/Spec review.
Named source declarations, the two law/operation structures and their
fields/constructors, the resource metric and its four constructors, private
helpers and generated machinery must still be assessed by their actual kinds.
The complete mathematical maps and cases above remain their ordinary owners.
Processed historical drafts, old type exports and predecessor payload mappings
need not accompany every checkpoint. Completing Priqueue does not close the
three-book task or receiving acceptance; new formalization follows the current
integration gate.
