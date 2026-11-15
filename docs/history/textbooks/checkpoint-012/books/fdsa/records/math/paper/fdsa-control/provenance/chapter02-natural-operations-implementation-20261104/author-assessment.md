# Natural-run operational implementation: complete static author assessment

## Status and exact scope

The two-file source draft is complete under the approved plan. All 106 declared
items were read against their intended source contracts: **63 core declarations
(six definitions and 57 theorems), and 43 example theorems**. The static author
assessment finds **no unresolved mathematical or intended-statement issue**.
This is an **uncompiled draft**. Its written proof terms and tactic scripts have
not been elaborated, kernel checked, linted or audited in this slice. Actual
elaborated-type readback, compiler diagnostics and every acceptance gate remain
pending. The inventory contains copied source headers, not purported elaborated
types. No claim in this report upgrades prior validation or integration status.

The source-only author branch was fast-forwarded from
`33a7c616bbb5d4a774ec614838d7670c61083ec4` to the fixed checked development base
`0ec9954479b081664bd4504c90fb66fba5fd22c8`. The ancestor check, actual alignment
and exact before/target pin/source hashes are in `start.json`, `alignment.log`
and `alignment-result.json`. Both new source files are the only new repository
items; existing tracked sources, project configuration and recorded pins remain
unchanged. The scoped commit and its exact terminal status are recorded in
`receipt.json` when committed. This is development ancestry, not acceptance.

The accepted integration remains R `07e480f6ec9958d4975bb90151005b84f2907614`.
The first pending foundation remains F `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`;
no substitution of the later shared prefix occurred.

## Read instructions and controlling source

This continuation stays inside the existing implementation/review loop. The
repository `AGENTS.md`, implementation skill, example-driven-development skill
and worked example, review-loop instructions, architecture/domain/glossary and
applicable ADR instructions were read. Nix alone is waived by the user. Exact
Lean/Lake/dependency pins and all proof/validation/review gates remain binding.
Root expressly owns compilation and acceptance; this author ran no build, made
no cache changes and spawned no agents.

The fixed design is the complete approved
`provenance/chapter02-natural-operations-preparation-20261104/plan.md`, SHA-256
`2123880901ee2b016cc15737f90dd14a5bf78fb408c75c2195bba96a81693958`, and its
`root-assessment.json`. C02-110–112 were reread from
`research/chapter02-obligations.md` and compared with the full retained Chapter2
requirements. The actual source is the pinned FDSA book, Chapter2 pp.21–25;
book SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Earlier scoped source/review evidence is retained; XD01's exact current core
hash is recorded below, rather than falsely reusing its earlier pre-correction
identity. The historical reports remain historical.

## Reused interfaces and mathematical boundaries

The implementation reuses `Resources.Measured`, `pure`, `bind`, `CallCount.tick`,
XD01 `Builder`, `Rep`, `AppCost`, creation operations, `pushRun`, `buildFrom` and
actual `toDList` bridges. There is no new carrier, interpreter, generic executor,
abstract closure datatype or numerical model. The source scanner values,
comparison scanner, BottomUp values/comparisons and natural composition remain
unchanged. Public import roots and reconstruction maps were not edited.

`α : Type u` is arbitrary. Generic scanner definitions, erasure, permutation,
run-count and cost bounds need no equality, order or default value on payloads
and no comparator laws. `κ : Type v` is a separate universe for keys. Sorted
specializations use `LinearOrder κ`. Strict descending specializations use only
`LT κ` and `DecidableLT κ` plus the explicit actual strict comparisons. There
is no hidden `[Inhabited α]`, `[DecidableEq α]` or payload order assumption.

Value erasure for an arbitrary ascending callback requires `Rep f pref` and
nothing about cost. The arbitrary ascending operational bound instead requires
only the all-suffix `AppCost f k`; no Rep or sorted-prefix premise appears.
The arbitrary continuing-path whole-pair theorem requires neither contract:
it preserves the actual `buildFrom` result, actual suffix application, value
and observation. Descending workers accept arbitrary supplied accumulators;
their earlier construction and length are outside the worker boundary.

## Fixed tariff and arithmetic readback

| Executed branch | Written exact work |
| --- | --- |
| Initial empty / singleton | 1 / 3 |
| Initial two-or-more | 3 + chosen actual worker |
| Ascending empty tail | F(a) + 3 |
| Ascending continuation | 4 + worker on actual `pushRun` result |
| Ascending restart | F(a) + 4 + scanner on unconsumed next::tail |
| Descending empty tail | 3 |
| Descending continuation | 3 + worker on actual current::acc |
| Descending restart | 4 + scanner on unconsumed next::tail |
| Empty/single-run merger dispatch | 1, only on outer length ≤ 1 |

Here F(a) is the observation of the actual supplied callback on `[a]`.
Each scanner/worker entry and tested pair costs one. XD01 supplies the callback
creation/application charges. Direct descending cons, the terminal singleton
suffix and the emitted outer-run cons each cost one. The singleton callback's
own entry already accounts for its local cons. It is not charged twice.

The simultaneous induction uses input length for runs and remaining length+1
for workers. Its potential bounds are exactly Wr≤6*n+1, Wa≤k+6*m+5 and
Wd≤6*m+5. At ascending continuation, four immediate units and the next
invocation weight k+2 give `4+(k+2+6*m+5)=k+6*(m+1)+5`. Restart gives
`k+4+(6*(m+1)+1)=k+6*(m+1)+5`. The descending counterpart needs no accumulator
length term. This covers restarts directly; no unsupported disjoint-run sum or
sharing assumption is used.

The actual initial ascending builder is
`bind (createSingleton first) (buildFrom middle)`. If m is the middle length,
construction and every one application each cost 1+2*m. With p=m+1 represented
prefix length, each weight plus one is 2*p. For complete run length r=m+2,
each weight plus three is 2*r; only then is 2*r-3 stated. The construction and
unfolded invocation weights agree on this particular source path. This is not
a theorem identifying distinct shared creation events with future invocation
occurrences. The existing shared-closure counterexample remains visible.

The exact ascending worker work is k+6*m+3; the descending worker work is
3*m+3. Initial ascending work 6*n-5 has an explicit n≥2 premise and an
unsaturated add-five predecessor theorem. Initial strict descent costs 3*n
for nonempty input, including n=1. Empty scanner input costs 1 and singleton
input costs 3 separately. The one-unit dispatch yields total 2 for empty,4 for
singleton,6*n-4 for ascending n≥2, and3*n+1 for nonempty strict descent.

`baseMergeOps` requires an outer-length≤1 proof and matches the actual run list.
It retains distinct [] and [[]] cases. Its `tick(allRun)` bridge is proved only
through the existing two base equations. `singleRunOpsBy` captures the scanner
pair once and dispatches its actual first projection, with erasure transporting
the supplied domain proof. Value correctness for an arbitrary merge comparator
is valid because neither permitted base branch calls it. Multi-run comparison
`allRun` is not assigned this operational observation. The full scanner bound
6*n+1 and restricted natural execution bound 6*n+2 are explicit affine bounds;
no additional Growth wrapper, machine-time bound, compiler-allocation claim or
stability promise is added.

## Complete core declaration assessment

The exact source header for every row is in `source-inventory.json`. The following
rows record the intended mathematics and the connected use or boundary assessed.
All rows have static outcome **consistent with the frozen intended contract;
elaboration pending**.

| Declaration in `Resources.NaturalRunOperations` | Intended claim and domain readback | Connected use / boundary |
| --- | --- | --- |
| `runsOpsBy` | Actual mutually recursive scanner; one selected branch, tested next/current comparison, singleton callback or descending seed, and exact direct allocation tariff. | Empty, singleton, homogeneous, restart and tagged cases. |
| `ascOpsBy` | Actual supplied Builder is pushed or invoked once on the terminal singleton; restart scans the unconsumed next element. No Rep or AppCost in the definition. | Arbitrary builder restart, unlawful reverse callback and padded worker. |
| `descOpsBy` | Actual supplied accumulator is extended or emitted; no traversal or earlier creation of acc is charged. | Arbitrary accumulator and descent/restart cases. |
| `runsOpsBy_nil` | Empty input returns no runs and costs exactly 1 scanner entry; arbitrary payload universe/comparator. | Empty payload has no inhabitance instance. |
| `runsOpsBy_singleton` | Singleton returns its one nonempty run; entry, cell and outer cons cost 3. | Generic singleton payload and execution cost 4. |
| `runsOpsBy_cons_cons` | Both initial branches cost 3 plus their actual selected worker; false comparison uses the singleton callback. | Ascending and descending costs, initial restart examples. |
| `ascOpsBy_nil` | Exact actual callback value on [a] and callback observation plus 3; no callback contract assumed. | Unsorted supplied prefix, padded/expensive callbacks. |
| `ascOpsBy_cons` | True branch emits actual f[a] and restarts, cost F+4+Wr; false branch pushes actual f and costs 4+Wa. | Restart worker and continuing source-path proof. |
| `descOpsBy_nil` | Exact [a::acc] and cost 3 for every acc, including empty or arbitrarily long accumulators. | Arbitrary descending accumulator. |
| `descOpsBy_cons` | Strict continuation costs 3+Wd; failed descent emits actual accumulator and costs 4+Wr. | Three-boundary worker costs 7. |
| `singleton_toDList` | Singleton callback erases to Batteries singleton with the same payload value; proof irrelevance only. | Initial ascending value erasure. |
| `runsOpsBy_value` | Initial scanner erases exactly to runsBy; arbitrary Boolean operation and Type u payload. | Generic occurrences, run counts and all connected scanner cases. |
| `ascOpsBy_value` | For arbitrary supplied Rep f pref, erasure is ascBy with the actual toDList callback; AppCost is absent. | Uses pushRun_rep and toDList_pushRun, preserving full worker semantics. |
| `descOpsBy_value` | Exact erasure to descBy for arbitrary current payload, acc and remaining tail; no order conditions. | Full supplied-accumulator boundary preserved. |
| `runsOpsBy_perm` | Flattened full payload occurrences are permuted, regardless of comparator laws. | Generic scanner contracts; no stability assertion. |
| `runsOpsBy_flatten_length` | Flattened value length equals input length, derived from full permutation. | Generic scanner contracts. |
| `runsOpsBy_length_le` | Outer run count is at most input length; zero input remains zero outer runs. | Generic scanner contracts and distinct empty-inner dispatch examples. |
| `runsOpsBy_sorted` | Every emitted run is key-sorted for strict key comparison under LinearOrder on the key only. | Existing runsOn_sorted is reused through erasure. |
| `runsOpsBy_work_le` | All input lengths and all Boolean comparators satisfy Wr ≤ 6*n+1, including restarts. | Generic scanner contracts; empty/singleton costs fit the bound. |
| `ascOpsBy_work_le` | Only all-suffix AppCost f k is assumed: Wa ≤ k+6*tailLength+5. Rep and prefix ordering are absent. | Reverse-value callback with arbitrary uniform cost; continuation adds 2 potential. |
| `descOpsBy_work_le` | Wd ≤ 6*tailLength+5 independently of supplied acc contents and length. | Arbitrary accumulator base and restart recurrence. |
| `ascOpsBy_buildFrom` | Exact actual buildFrom/application pair on an ascending adjacent chain, for completely arbitrary f; cost construction+application+2*(m+1)+3. | Unlawful reverse callback gives [[3,2]], cost 26; source initial path. |
| `buildAscending` | Actual source seed program binds createSingleton first to buildFrom middle. Existing measured carrier only. | Tied ascending source path and suffix examples. |
| `buildAscending_eq` | Whole pair exposes the returned seed extension and one seed creation, without applying it. | Source path correspondence proof. |
| `buildAscending_cost` | Construction including the singleton seed is exactly 1+2*m. | Concrete duplicate prefix builds in 5; path and repeated-application cases. |
| `buildAscending_rep` | Returned callback represents first::middle on every suffix; no key or equality instances. | General suffix and two-application examples. |
| `buildAscending_appCost` | Every suffix application costs 1+2*m for the actual returned callback. | Source prefix weight, suffix and repeated-application examples. |
| `buildAscending_apply` | Whole application pair retains full prefix then suffix order and exact cost 1+2*m. | Duplicate prefix plus [9,8] and tied scanner source path. |
| `buildAscending_weight` | Creation and invocation weight each satisfy count+1=2*representedPrefixLength. No arbitrary Rep-to-size transfer. | Actual source first singleton and one push per middle item. |
| `buildAscending_counts_add_three` | For the nontrivial source run first::middle++[last], each count+3 equals twice its length. | Positive equality precedes subtraction; run length is at least 2 by shape. |
| `buildAscending_counts` | Both source counts are 2*r-3, derived from the unsaturated add-three equalities. | Does not apply the formula to empty/singleton scanner input. |
| `runsOpsBy_buildAscending` | The scanner actual output is the returned source builder applied to [last]; exact work includes construction, application and control 2*m+5. | Ascending ties example uses this path theorem directly. |
| `ascOpsBy_work_of_chain` | Under AppCost f k and all false adjacent tests, exact Wa=k+6*tailLength+3; no Rep or sorted prefix. | Actual push weight increases by 2 each step. |
| `descOpsBy_work_of_chain` | Under all true adjacent tests, Wd=3*tailLength+3 for every acc. | Strictly descending homogeneous family. |
| `runsOpsBy_work_ascending_add_five` | For length at least 2 and a false-test chain, Wr+5=6*n. Domain prevents boundary subtraction mistakes. | Source ascending exact pair and one-run execution laws. |
| `runsOpsBy_work_ascending` | Same explicit domain gives Wr=6*n-5 by arithmetic from the add-five law. | Ascending two/three and ties examples. |
| `runsOpsBy_of_ascending_chain` | Whole pair is ([xs],6*n-5) under actual false-test chain and n≥2. | Keyed sorted specialization; no arbitrary ordering assumptions. |
| `runsOpsBy_work_descending` | Every nonempty true-test chain has Wr=3*n, including singleton. Empty remains separately 1. | Descending two/three and generic singleton boundaries. |
| `runsOpsBy_of_descending_chain` | Whole pair is ([reverse xs],3*n) for a nonempty strict test chain. | Payload-preserving reverse value and exact descent observations. |
| `runsOpsBy_of_sorted` | Key-sorted input of length ≥2 has actual strict-scanner pair ([xs],6*n-5); only keys need LinearOrder. | Ascending two/three and initial source families. |
| `runsOpsBy_of_strictly_descending` | Pairwise strict descending keys imply the reversal pair under only LT and DecidableLT on keys; nonempty explicit. | No weak-descent/tie substitution; tagged counterexample retained. |
| `baseMergeOps` | Only lists with outer length≤1 are in the domain; [] and [run] each execute tick(pure result), including run=[]. | Both empty outer and empty inner cases. |
| `baseMergeOps_nil` | Empty outer list returns [] and dispatch cost 1 for every proof of its domain. | Empty payload execution costs scanner 1 plus dispatch 1. |
| `baseMergeOps_singleton` | Any single run, even [], returns itself and costs 1. | Distinct [[]] boundary retained. |
| `baseMergeOps_spec` | On the restricted domain, whole pair equals (mergeAllBy cmp xss,1) for every comparator. | Only actual source base equations are used. |
| `baseMergeOps_eq_tick_allRun` | On exactly the same domain, whole pair equals tick of existing comparison allRun. | Empty outer/inner examples; no extension to multi-run operational work. |
| `singleRunOpsBy` | Captures actual scanner pair once, transports the domain by erasure, and binds that returned run list to baseMergeOps. | No second pure scan or alternate output is substituted. |
| `singleRunOpsBy_spec` | Exact pair equals natural sorter value for arbitrary merge comparator and actual scanner work+1. | Source single-run execution connection; comparator is unused by both base branches. |
| `singleRunOpsBy_value` | Actual composed value is sortNaturalBy for any comparator on the proved domain. | Full payload permutation and source keyed correctness. |
| `singleRunOpsBy_work` | Exact operational observation is actual scan work plus one base dispatch. | Empty/singleton and homogeneous totals. |
| `singleRunOpsBy_work_le` | On its explicit run-count domain, total operational work ≤6*n+2 for every input length. | Affine bound follows the actual scanner bound, not comparison counts. |
| `singleRunOpsBy_perm` | All full payload occurrences preserved by the composed execution for arbitrary lt; domain explicit. | Source keyed arbitrary payload example also retains permutation. |
| `singleRunOpsBy_correct` | Strict key scanner plus source left-tie key≤ merge yields key sortedness and full permutation on the restricted execution domain. | Nat×arbitrary-payload example, no payload equality/order/default instances. |
| `singleRunOpsBy_nil` | Empty actual execution returns [] and costs 2 for every admissible proof. | List Empty example. |
| `singleRunOpsBy_singleton` | Singleton actual execution returns [a] and costs 4 for any Boolean comparator. | Generic arbitrary payload example. |
| `runsBy_length_le_one_of_ascending_chain` | Every false-test adjacent chain, including [], supplies the dispatch-domain proof. | Exact ascending execution can use a logically derived domain. |
| `runsBy_length_le_one_of_descending_chain` | Every true-test adjacent chain, including [], supplies the dispatch-domain proof. | Strict descending execution; singleton chain is vacuous and valid. |
| `singleRunOpsBy_of_ascending_chain` | Whole execution pair (xs,6*n-4) with n≥2, false-test chain and domain; subtraction is derived from add-five law. | Ascending totals 8,14,20. |
| `singleRunOpsBy_of_descending_chain` | Whole execution pair (reverse xs,3*n+1) with nonempty true-test chain and domain. | Descending totals 7,10; singleton total 4 agrees. |
| `runsOn_length_le_one_of_sorted` | Sortedness under LinearOrder supplies the domain at all lengths, including zero and one. | Constant key family and homogeneous execution cases. |
| `runsOn_length_le_one_of_strictly_descending` | Pairwise strict descent supplies the domain with only LT and DecidableLT on keys, at all lengths. | Does not admit the tagged tied decreasing input. |
| `singleRunOpsBy_of_sorted` | For a source key-sorted input of length≥2, derived-domain execution returns xs and costs 6*n-4. | Repeated arbitrary payload and range exact families. |
| `singleRunOpsBy_of_strictly_descending` | For nonempty strictly descending keys, derived-domain execution reverses xs and costs 3*n+1. | Only strict comparisons are required; empty remains its own case. |

## Complete connected example assessment

The numeric targets below were checked by the fixed recurrence arithmetic above,
not copied from a running evaluator. Proof drafts use public general laws or
actual branch composition. In particular, the tied source run exercises
`runsOpsBy_buildAscending` directly, and the reverse-valued arbitrary callback
exercises `ascOpsBy_buildFrom` without a Rep/AppCost premise. Families use proved
ordering or constant-key facts. Negative builder cases reuse XD01 definitions.

Every example row is statically consistent with its intended independent target;
none is represented as compiler-checked yet.

| Declaration in `Examples.NaturalRunOperations` | Independent intended target and assessment |
| --- | --- |
| `empty_payload` | List Empty scanner yields ([],1); no payload inhabitance or comparator evaluation. |
| `empty_payload_execution` | Actual empty execution yields ([],2), including its base dispatch. |
| `singleton_payload` | Every payload/comparator gives ([[a]],3). |
| `singleton_payload_execution` | Every payload/comparator gives ([a],4), with derived singleton domain. |
| `ascending_two` | [1,2] gives one run, work 7 through keyed homogeneous law. |
| `ascending_three` | [1,2,3] gives one run, work 13 through keyed homogeneous law. |
| `ascending_two_execution` | [1,2] returns itself with actual scan plus dispatch work 8. |
| `ascending_three_execution` | [1,2,3] returns itself with work 14. |
| `descending_two` | [2,1] reverses into [1,2], scanner work 6. |
| `descending_three` | [3,2,1] reverses into [1,2,3], scanner work 9. |
| `descending_two_execution` | Strict descending execution costs 7 including dispatch. |
| `descending_three_execution` | Strict descending execution costs 10 including dispatch. |
| `ascending_ties` | [1,1,2,3] retains both ties, scanner work 19. Proof calls actual source-builder path then exact builder counts/value. |
| `ascending_ties_execution` | Same tied run costs 20 with dispatch; no stability theorem is asserted. |
| `three_boundary_worker` | Supplied current 1/acc [3], tail [2]: actual restart yields [[1,3],[2]], worker work 7. |
| `three_boundary` | [3,1,2] has two runs and scanner work 10=initial 3+worker 7. |
| `restart_worker` | Current 3/seed singleton 1, tail [2,4]: two runs, worker work 12=application 1+4+next scan 7. |
| `restart_boundary` | [1,3,2,4] has two runs and scanner work 15. |
| `odd_runs` | [1,3,2,4,0] retains final singleton, three runs, scanner work 19. Explicit second restart costs 11, first worker 16. |
| `weak_descent_with_ties` | Tagged [3A,3B,2C] starts ascent at the tie, emits [[3A,3B],[2C]], work 11. |
| `multiple_runs_outside_dispatch` | All three concrete multi-run inputs falsify the ≤1 domain; no one-unit operational merger is claimed for them. |
| `weak_descent_outside_dispatch` | Tagged tied decreasing input also falsifies the dispatch domain; weak descent is not strict descent. |
| `arbitrary_builder_restart` | Supplied compose(singleton1)(singleton3), current5, tail[4,6]: values [[1,3,5],[4,6]], work14, excludes earlier seed creation. |
| `unsorted_builder_value_and_work` | Supplied compose(singleton2)(singleton1), current3, nil tail: [[2,1,3]], work6. |
| `unsorted_builder_remains_unsorted` | The same actual result is not key sorted; a value/cost law does not add a missing prefix-order premise. |
| `arbitrary_descending_accumulator` | Any current, comparator and acc: empty worker tail yields [a::acc], work3 independently of acc length. |
| `arbitrary_cost_without_rep` | Arbitrary uniform k and reverse-valued callback satisfy the worker bound with no Rep assumption. |
| `arbitrary_callback_continuation` | Current2, callback(reverse,17), tail[3]: actual arbitrary-callback path produces [[3,2]], work26=creation2+application19+control5. |
| `expensive_capture_worker` | Capturing identity-valued callbacks with arbitrary p,q costs 1; actual terminal application/worker costs p+q+4. |
| `empty_outer_dispatch` | [] returns [] with dispatch1 and exact tick(allRun) bridge for any cmp. |
| `empty_inner_dispatch` | [[]] returns [] with dispatch1 and the same restricted bridge, while preserving a different outer count. |
| `source_builder_with_suffix` | Source prefix [1,1,2] costs5 to construct; applying to [9,8] gives [1,1,2,9,8], costs5. |
| `source_builder_two_applications` | One actual construction followed by two actual distinct suffix applications returns both values and costs 3+6*m; no application memoization. |
| `charged_identity_changes_worker_work` | Composing with charged identity preserves terminal worker values but increases work by2 for every supplied f. |
| `padded_worker` | Existing XD01 padded empty-prefix callbacks produce [[a]] for every n but terminal worker work2*n+4. |
| `no_worker_bound_from_empty_prefix` | For every proposed constant B, a Rep-empty-prefix supplied builder has terminal worker work>B. |
| `shared_closure_counts_retained` | Existing four self-composition extensions retain creation5/application31/combined36 even for Empty payload. |
| `generic_scanner_contracts` | All comparators and payloads retain full permutation, flattened length, run-count bound and fixed operational bound. |
| `arbitrary_payload_correct` | For Nat×Type u payloads, only the run-count domain is required for sortedness and full occurrence preservation; no payload instances. |
| `constant_key_domain` | Every arbitrary-payload list has at most one run for false comparator, including empty input. |
| `repeated_payload_exact` | For every payload and n≥2, repeated-payload execution returns the same length n list, work6*n-4; small cases handled separately. |
| `ascending_range_exact` | The range-n sorted family has the same exact total work for n≥2, using independently proved range ordering. |
| `comparison_counter_is_separate` | [1,2,3] has scanner comparisons2 and total natural comparisons2, while the operational execution costs 14. Counters are not conflated. |

## Static revisions and remaining verification

Before committing, source readback made a few local proof/readability adjustments
within the two new files: explicit parentheses in the source-run concatenation;
a direct congruence proof for the empty ascending worker cost; explicit Nat
reflexivity for the run-count domain; a single simplification for the captured
base-dispatch pair; and explicit namespace qualification for existing comparison
operations. The intended tariff, algorithm branches, theorem premises, equations
and expected counts were unchanged. Two independent path cases were made to
call the actual builder-path theorems. No existing-source finding required an
out-of-scope edit. No known mathematical/specification discrepancy remains.

`static-source-checks.json` records only text and byte observations: no prohibited
proof tokens or `letI`, no trailing whitespace, no lines over 100 characters,
warningAsError and autoImplicit settings retained, no existing tracked diff,
and all saved dependency/pin hashes unchanged. These observations are not a
Lean linter or proof audit. Tactic elaboration, recursive termination proofs,
simp hygiene, dependent proof transport and the written type hypotheses must
still be checked by the qualified compiler. No failed attempt is invented and
no result is guessed.

Root should compile the exact immutable successor in its exclusive qualified
checkout, targeting `Applications.Resources.NaturalRunOperations` and
`Examples.NaturalRunOperations`; the author tree has no build authorization.
Retain each actual terminal result and full/native logs. After any proof-only
correction, update exact identities, inspect all 106 actual declarations with
explicit universes/types, and perform author readback. Both independent review
axes, complete applicable candidate check/audit, matching verification, immediate
candidate verification and root's integration sequence remain outstanding.
The existing review/finding records continue; this static author report replaces
neither independent axis and grants no acceptance.

## Source identity

- `Applications/Resources/NaturalRunOperations.lean`: 29,861 bytes, 690 lines, SHA-256 `c5742c0b6e1617b9646aaf9b92d8c5f4dfd02457735c1eb6d4a561fede258e24`.
- `Examples/NaturalRunOperations.lean`: 15,966 bytes, 352 lines, SHA-256 `fe08adbd075edbed29bd094e3c3a4d5ef156b31cf84463f5b1957c5f019dff9a`.

The core has 63 declarations (6 definitions, 57 theorems); examples have 43 theorems,
for 106 declarations total. The complete copied-source inventory and bounded
alignment records are saved beside this report. All further author writes are
held after the scoped commit receipt and handoff are secured.
