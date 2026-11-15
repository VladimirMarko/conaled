# Shared FDSA foundations — independent Spec review

Recorded 3 November 2026. This is the Spec axis of the existing combined
X002 / APP-A / XB01 / APP-C review loop. It is not a new review workflow, a
third review axis, or acceptance of the whole sorting chapter or Appendix B.

**Outcome: Blocked pending complete-candidate validation evidence.**
The source assessment is complete and has **zero concrete Spec findings**.
The six-module focused check passed on the exact candidate. At the time this
report was written, root reported that the ordinary guarded full check was
still active, and its evidence directory had no terminal `result.json`.
Consequently, neither a successful full build nor the exhaustive audit nor a
new matching foundation verification record is established by this report.

## 1. Immutable scope and authority

| Item | Identity |
| --- | --- |
| Incorporated accepted Chapter 1 base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Merge base independently checked | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Reviewed candidate | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |
| Exact saved foundation prefix incorporated | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Original combined base retained in history | `1aabd512284fe86254278ac631eda061d311050b` |
| Isolated checkout | `/workspace/scratch/31d6377eca78/fdsa/conaled-ch01-review` |
| Candidate branch | `work/fdsa-foundation-integration` |
| Diff | `git diff 07e480f6ec9958d4975bb90151005b84f2907614...f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |

The accepted Chapter 1 commit is an ancestor of the candidate. The base change
therefore follows the existing review-loop rule for an incorporated integration
tip. It does not erase the original requirements, earlier assessments, failed
validation attempts, or carried findings. The complete commit inventory after
the accepted base is `697bcf2`, `333f900`, `df116c2`, `c994c22`, `50dc7df`,
`c80eec9`, `0c93725`, `9875bfd`, and `f17cc6b`.

The nonempty three-dot diff has nine paths, 1,515 insertions and six deletions.
All nine paths are in scope. The clean isolated worktree's reviewed files were
compared byte-for-byte with the candidate Git objects. No task path was
excluded. The later XP01 draft is outside the exact first prefix selected by
the retained integration preflight; its future requirements remain in force.

The user's full authority is retained in `fdsa-control/REQUEST.md`. The four
frozen requirements below govern this combined review. Their historical
queued/blocked status prose does not shrink their mathematical scope. The
Chapter 1 prerequisite has now been accepted. The user's native-environment
exception waives Nix, not the pinned compiler/dependencies, validation,
independent reviews, or final candidate identity check.

| Frozen record under `fdsa-control/reviews/` | Independently checked SHA-256 |
| --- | --- |
| `insertion-requirements.md` | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `list-library-requirements.md` | `83cffa5aff717943d449f4380189a9e9a761252730f5a14f4e392f1e62d154d4` |
| `list-calls-requirements.md` | `0a2f7a2869c10276da2cc9a852e20936c6aba2d094d5232b96e94fbf47ecf78d` |
| `notation-requirements.md` | `21a4ad13752d4316817e97f655af9a768726aa682124a39a2aeac248460b5a48` |

### Reviewed file identity

| Candidate path | Bytes | SHA-256 |
| --- | ---: | --- |
| `Applications/Resources/InsertionSort.lean` | 7,257 | `385ea0ba077ac05a10547bc95cd37eb4fa80ef8fe826c6e2c250cca33f2b4aad` |
| `Applications/Resources/ListCalls.lean` | 7,939 | `bce039ed24b88dcb7fc2496acede9e5118cadc0a9e76da8c4a166f93e5b46488` |
| `Examples/InsertionCosts.lean` | 3,862 | `f808254936f1757e639b4f49d94904056b92c84802d9a887a16d31c861c7ff37` |
| `Examples/ListLibrary.lean` | 6,761 | `036cf4c12ddf5d25ce433d9f7dbedfcbb96dfc3c7f602d10605388d2791e47ad` |
| `Examples/ListCalls.lean` | 4,333 | `24d0809f51d04b0a9cadb5a349141e7327a5f7721f63c1021113527917487d5d` |
| `Examples/FunctionalNotation.lean` | 8,277 | `fe4b585a6753110dee67c1942ce68d16d9bf00feb5946f32791682c634c42eef` |
| `SquareApplications.lean` | 8,412 | `7f00379973161019217585a5ed32d0374247300544ae448b2a4b86aa11c6bf64` |
| `docs/research/fdsa-notation-map.md` | 24,280 | `cff778380868755fa7e7018797bf3d5e8c7b0cc55b5e3cd37bc64b3f32658d5b` |
| `docs/research/fdsa-reconstruction-map.md` | 31,701 | `c3059fc931180a6c0e6ec07ea7b92953aac451677a3939b0daaeb433e042bbe9` |

## 2. Source evidence and review method

The primary book is the supplied official PDF at
`/workspace/scratch/31d6377eca78/research-source/functional_data_structures_algorithms.pdf`.
Its SHA-256 was independently recomputed as
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
This is the pinned July 27, 2026 edition. The relevant printed pages are 14–15
and 28 for insertion sorting and Exercise 2.1, 343–345 for Appendix A, 347–348
for B.1, and 355–359 for Appendix C. The corresponding PDF pages were read;
printed pages 345, 348 and 359 were also visually inspected to resolve the
minimum/sortedness, exact-cost, fold and interval tables. No extracted book
text or page images are embedded in this report.

Two immutable primary Isabelle theory files clarify semantics that the
notation table alone leaves implicit. They were fetched read-only, their
actual definitions inspected, and their byte identities checked:

| Primary source | Bytes | SHA-256 | Relevant observation |
| --- | ---: | --- | --- |
| [Groups_Big.thy at f86f290](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Groups_Big.thy) | 71,613 | `719e0d98fe46cfc9ec88ef7e2a8687d07c55ed77cd45d66fbe524c8361e51943` | The ordinary set fold tests finiteness of the index set and has the neutral result on an infinite index set. Sum instantiates the additive neutral element. |
| [Euclidean_Rings.thy at f86f290](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Euclidean_Rings.thy) | 96,584 | `e5c9ce17d740ee9f6efb0e38870a5052d4276010b831f7a9d249265f018ae1bc` | Integer division rounds downward when the signs differ and division is inexact; zero-divisor division is zero. |

That Isabelle revision postdates the book, as the candidate map records. It is
supporting semantic evidence, not a claim to have recovered or rechecked the
book's original Isabelle build. The PDF remains the primary coverage source.

The assessment used the repository's code-review workflow and
example-driven-development statement-review guidance: intended claims,
quantifiers, hypotheses, actual definitions, nonvacuity and connected uses
were checked separately from compilation. Relevant unchanged project APIs
were inspected, including `Measured`, `CallCount`, sorting/stability,
selection rank, `FunctionalBasics`, and the measured length/split operations
in `SymmetricCosts`. Pinned Lean/Mathlib implementations were inspected where
their exact recursion, fold direction or typeclass requirements mattered.

The original inventories and source preflights inform the coverage trail.
The current six Lean files and complete notation map were read, together
with the reconstruction-map changes and relevant unchanged definitions.
Historical source-readiness and validation records were not promoted to
candidate acceptance. No new compiler process, fixture gate, or dependency
mutation was performed by this reviewer.

## 3. X002 — insertion-sort costs and existing contracts

**Assessment: required source scope satisfied at the statement and
implementation level; complete-candidate validation pending.**

`Resources.InsertionSort.insertRun` follows the actual `List.orderedInsert`
branch: an empty list costs one; a successful comparison with the head costs
one and stops; otherwise it recursively inserts into the tail and adds one.
`insertRun_value` erases to that canonical operation with the same comparison
orientation. In particular, an equal key is inserted before an existing equal
head. The sort processes its tail first, so that orientation preserves the
original equal-key payload order.

`sortRun` feeds its actual returned sorted tail to insertion using the
existing measured composition vocabulary, and pays its own entry tick.
`sortRun_value` identifies its returned value with `List.insertionSort`, whose
standard definition is the corresponding right fold of `orderedInsert`.
The implementation is therefore an instrumented source execution, rather
than a cost formula attached to an independently chosen output.

The insertion statements include the uniform bounds from one through
`xs.length + 1`, the minimally sufficient head-success condition, an
all-members sufficient condition, and the all-reject full-traversal equality.
The sorting statements include the uniform lower bound `2 * n + 1`, the
doubled triangular upper inequality, its natural-division form
`(n + 1) * (n + 2) / 2`, and the weaker `(n + 1)^2` source bound. The doubled
form avoids a hidden rounding assumption when deriving the exact natural
quotient.

Operation, erasure, length and uniform-bound results require only a decidable
relation on an arbitrary payload type. `sortRun_cost_of_pairwise` uses the
actual `List.Pairwise r` precondition: no unneeded transitivity or totality is
added to the best-case theorem. The opposite-pairwise theorem describes
rejecting comparisons, and `reverse_range_opposite` supplies an attainable
worst-case family at every length. The exact reverse-range theorem is for
`reverse (range n)`, which has length n. It is consistent with the preceding
source example ending at n having n+1 elements. There is no false claim that
all descending inputs with duplicates attain the strict worst case.

Correctness is connected to the existing `StableSort` contract through
`sortRun_stable`. Its key capabilities are `LE`, decidable comparison,
`Std.IsLinearPreorder`, and the decidable key equality used by the existing
equal-key filter contract. It does not impose an order or equality decision
on payloads, or strengthen the key domain to antisymmetry. The existing
contract includes sortedness, full-list permutation, and preservation of
each equal-key filtered sequence; it is not reduced to support equality.

The checked clients exercise public results on independently determined
observations. They cover empty cost 1, singleton cost 3, duplicate sorted
input `[1,1,2]` with cost 7, and reverse-range input `[2,1,0]` with cost 10.
Inserting 2 at the head of `[2,0]` checks the short circuit despite the tail
not satisfying the comparison. Inserting 4 into `[1,2,3]` checks the full
traversal cost 4. Arbitrary payloads and tagged equal keys exercise the
stability contract rather than only a numerical permutation.

The selection client applies the unchanged occurrence-sensitive rank theorem
to the actual indexed sorted result. A repeated-value example checks that
rank is not replaced by distinct-value position. The length-at-most-five
client proves a sorting budget of 21 calls and combines it with the rank
observation. Its stated budget is explicitly sorting-only, with no unproved
charge for indexing or the rest of Chapter 3. The three original insertion
preflight improvements—head-only insertion, occurrence-rank use, and an
arbitrary-payload stability client—are all present. Remaining Chapter 2
obligations are not claimed discharged by this shared foundation.

## 4. APP-A — all twenty list entries

**Assessment: all twenty source entries have standard reuse mappings,
appropriate observation bridges and retained boundary/composition clients.**

The candidate introduces no parallel list type. The twenty-entry map in
`fdsa-reconstruction-map.md` was checked against the source, with the following
semantic decisions preserved:

| Entry | Reviewed carrier or operation | Boundary or capability retained |
| --- | --- | --- |
| Length | Standard `List.length` | Empty/cons value equations; costs remain a separate measured claim. |
| Append | Standard `List.append` | Empty/cons equations and original order. |
| Set of list elements | Propositional membership predicate | No payload `DecidableEq`; duplicate multiplicities are intentionally forgotten only here. |
| Map | Standard `List.map` | Actual mapped values, order and duplicate occurrences. |
| Filter | Standard Boolean `List.filter` | Boolean predicate result controls retention. |
| Concatenation | Standard `List.flatten` | Source sublist order retained. |
| Take | Standard `List.take` | Zero, empty and overlarge counts. |
| Drop | Standard `List.drop` | Zero, empty and overlarge counts; take/drop recomposition. |
| Head | `head?` and proof-domain `head` | Agreement on nonempty inputs; no arbitrary payload default. |
| Tail | Standard total `List.tail` | Empty and singleton behavior. |
| Butlast | `List.dropLast` | Correct conditional cons equation and empty/singleton behavior. |
| Reverse | Standard `List.reverse` | Value equations only; the accepted Chapter 1 source-cost model remains distinct. |
| Indexing | Zero-based proof-domain indexing and `getElem?` | Valid-input agreement and explicit optional failure. |
| Update | `List.set` | Valid selected position, other positions, length, and invalid-index identity. |
| Half-open natural range | `List.Ico` | Inclusive lower/exclusive upper endpoint, equal/reversed emptiness, zero upper bound and successor equation. |
| Replication | Standard `List.replicate` | Zero count and repeated occurrences. |
| Distinctness | `List.Nodup` | Repeated elements violate distinctness. |
| Sum | Standard `List.sum` | Literal right-fold equations with only `Add` and `Zero`. |
| Nonempty minimum | `List.min?` and proof-domain `min` | Valid-input agreement; algebraic recurrence and ordered leastness are distinguished. |
| Sortedness for a relation | `List.Pairwise` | Every later element, not merely adjacent comparisons. |

The set observation is a proposition-valued `Set`; it requires neither a
decision procedure nor an inhabitant. The `dropLast` cons condition tests
whether the tail is empty, not equality of payloads. The successor range
equation uses the correct `i ≤ j` branch for `List.Ico i (j+1)`; its complement
gives the empty range. The endpoint and membership clients check the standard
half-open interpretation directly.

For head, index and minimum, the source's specified domain is preserved by
explicit proof-domain or optional interfaces. Optional failure outside that
domain is a chosen representation, not a source equation about an arbitrary
default. `empty_payload_queries` and `empty_payload_minimum` check that no
global inhabitant was introduced. The latter can use the vacuous `Min Empty`
operation; no claim is made that `Empty` supports `Zero` for summation.

The sum recurrence is the actual standard right fold, so it does not need
associativity or commutativity merely to state that recurrence. The minimum
implementation uses a left fold. Its source-style recursive equation
therefore exposes `Std.Associative min`, while the valid `min?`/`min` bridge
requires only `Min`. The separate leastness client uses `LinearOrder` and a
successful optional result. These distinct capability requirements are
justified by their actual claims, rather than hidden under a blanket linear
order for every list operation.

`sorted_wrt_cons` has the source's arbitrary-relation all-later-elements
meaning. `adjacent_relation_is_insufficient` supplies a nontransitive relation
and a list whose adjacent comparisons succeed but whose full pairwise
condition fails. This is a substantive guard against an incorrect translation
to `IsChain`.

Retained uses include a duplicate-preserving map/filter/flatten composition,
valid and invalid updates, updating one of repeated equal values, split
reassembly, overlarge take/drop, half-open ranges, a repeated minimum, and a
filtered minimum with a proved leastness observation. The map consistently
distinguishes value equality from source execution cost: an optimized
standard reverse or minimum does not inherit the book's recurrence tariff
merely because its output agrees.

## 5. XB01 — Appendix B.1 call counts

**Assessment: the seven source primitives and seven exact cost laws are
covered, including callback observations and the source lookup domain.**

The source B.1 equations were checked directly, including the visually
inspected exact-property table. Let n denote input length and c(x) the
callback count at an occurrence. The resulting coverage is:

| Primitive | Implementation/reuse | Reviewed exact observation |
| --- | --- | --- |
| Append | Existing measured append | First input length plus one; no duplicate algorithm. |
| Length | Existing measured length | n + 1; not the runtime of an uninstrumented standard length. |
| Map | `Resources.ListCalls.mapRun` | Sum of callback counts over list occurrences, plus n + 1, with the actual mapped callback values. |
| Filter | `Resources.ListCalls.filterRun` | The same occurrence-count sum plus n + 1; both keep and discard branches pay predicate and tail costs. |
| Take | Adapter over existing `splitRun` | `min k n + 1`, with the standard taken prefix. |
| Drop | Adapter over existing `splitRun` | `min k n + 1`, with the standard remaining suffix. |
| Lookup | Sequential `lookupRun` | k + 1 when k < n, with optional output agreeing with zero-based lookup. |

`mapRun` and `filterRun` use existing measured `bind`, `pure` and `CallCount`
operations. A cons charges its actual callback observation, recursive-tail
observation and one entry call. The callback's value component participates
in the resulting list; it is not discarded in favor of a separately computed
output. Filter branches on the returned Boolean. Rejected elements still
charge their predicate and recurse through the tail.

The exact cost uses a mapped list sum, so two equal payload occurrences each
contribute their own callback observation. It is not a sum over support.
The constant-callback theorem assumes constant cost only on members of the
given input, and yields `(c+1)*n+1`. The map/filter count equality concerns
cost components only. Nothing claims equality of their returned values or
changes Knapsack's separately documented +2 tariff.

Map supports separate source and result universes; the list operations do
not add order, payload equality, or inhabitant assumptions. The measured
take/drop adapters preserve the existing split value/cost observation and
prove the source zero/nil/successor equations. `take_drop_separate` runs both
operations on the original input. It adds their two costs, while the fused
split returns both values for one traversal. It does not accidentally apply
drop to the already taken prefix.

Lookup recurses sequentially through the list. The source specifies its
displayed recurrence on nonempty input and exact law on valid indices; it
does not supply an invalid-input cost equation. The implementation's chosen
empty failure `(none,1)` and resulting total `min k n + 1` law are explicitly
identified as an extension. `lookupRun_cost_of_lt` and `lookupRun_valid`
recover exactly the source domain without `Inhabited` or a random-access
execution shortcut.

Concrete clients retain the independently calculated cases from the frozen
requirements. Callback `(x+10,x)` on `[2,2,3]` produces `[12,12,13]` at cost
11. The corresponding predicate callback produces `[2,2]` at the same cost,
including examples with a rejected first or last occurrence. Zero-cost and
unit-cost callbacks on length three give 4 and 7; all-rejected unit callbacks
still give 7. The map-then-length composition measures the actual returned
list and obtains 15 in its duplicate case. Append-then-length composes the
two actual observations.

Index 2 of `[4,4,9]` returns 9 at cost 3; index 3 and a much larger invalid
index both fail at cost 4. Empty lookup over `List Empty` requires no payload
default. Take and drop of 2 from `[1,2,3]` cost 3 each; their sequential
combination costs 6 while the fused split costs 3. Zero, overlarge and empty
payload cases are retained. These uses exercise public theorems and expose
the value/count distinction rather than only restating definitions.

## 6. APP-C — all ninety notation rows

**Assessment: all AC-001 through AC-090 rows are mapped with their typed
semantics. The required semantic boundary checks are present.**

The complete ordered map was compared with the actual five-page appendix.
Coverage is 34 symbol rows, four subscript/superscript rows, and 52 syntactic
sugar rows: arithmetic/list AC-039–052, sets AC-053–067, multisets AC-068–077,
folds AC-078–084, and intervals AC-085–090. The requirement is a faithful
standard mapping with meaningful connected checks, not a theorem or parser
declaration for every editor glyph. The candidate follows that scope.

### Binders, Boolean truth, comprehensions and sets

The map distinguishes meta equality, definitional declarations, propositional
equality, `Iff`, Boolean operations, implication and function types. Explicit
truth adapters carry the necessary `Decidable` hypotheses; ordinary set
statements do not acquire blanket decidability. Decorated identifiers do not
silently become lookup or powers. Function composition is checked through
the standard composition operation.

The comprehension client preserves both generator order and repeated
occurrences: the repeated generator case returns `[2,12,2,12]`. Set union,
intersection, strict inclusion, direct image, restricted and two-variable
comprehension, bounded quantification, indexed union, and set-of-sets union
and intersection retain their actual membership meanings. In particular,
proper subset retains inequality, direct image does not assume injectivity,
and the two-variable comprehension retains both existential witnesses.
Product types and Cartesian products of sets remain distinct typed uses.

### Arithmetic and division

Natural and real division have explicit types. The unrestricted Isabelle
integer quotient maps to `Int.fdiv`, with the nonnegative-divisor bridge to
the default quotient proved separately, including zero. The checked
negative-divisor case gives `5 fdiv (-2) = -3`, whereas Lean's default
integer division gives -2. The primary `divide_int` definition corroborates
that distinction. Zero-divisor behavior is checked explicitly.

The floor/ceiling example on -3/2 distinguishes integer floor -2 and ceiling
-1. Natural exponents are not confused with real exponentiation. Existing
accepted `FunctionalBasics` clients supply the natural truncated-subtraction
and integer-to-natural boundary evidence; those definitions and uses were
inspected rather than assumed from their names.

### Lists, multisets and multiplicity

The Appendix A bridges cover list endpoints, indexing and updates. Standard
multiset map/filter/cardinality observations preserve multiplicity, with
decidable predicates required only where an executable filter needs them.
Submultiset is the multiplicity-sensitive order `≤`; support-only `⊆` is not
substituted. The two-copies-versus-one-copy example proves that support
inclusion can hold while submultiset inclusion fails. Its current proof uses
membership and the impossible cardinal inequality 2 ≤ 1, keeping the intended
statement without requiring a decision procedure for an infinite-domain
universal support predicate.

The fold example gives sum 7 and product 12 for the list/multiset occurrences
`[2,2,3]`, while the deduplicated finite set has sum 5 and product 6. This
checks the distinction observationally, not only by naming different types.

### Finite-index and otherwise-neutral folds

For a finite set, the map uses standard `Finset.sum`/`prod` through the finite
set's representation, with the required commutative monoid structure. List
fold laws use the weaker ordered monoid capabilities. The closed natural
interval example includes both endpoints, giving sum 9 and product 24 for
2 through 4. The general AC-080 row does not silently restrict all source
ordered intervals to Nat or assume that every such interval is finite.

`finiteIndexProduct` tests finiteness of the entire index set. On a finite
set it takes the standard finite product; on an infinite set it returns one.
The additive counterpart `finiteIndexSum` returns zero in the infinite case.
Finite-set, supplied-Finset and infinite equations are proved. The definition
is explicitly classical and noncomputable, so it does not claim an algorithm
deciding finiteness. It introduces no public `DecidableEq`, `Fintype`, or
inhabitant requirement for the index type, and index/value universes are
independent.

This matches the inspected `Groups_Big` convention. It is not a support-based
fold, `finsum`, `finprod`, or convergent series. The finite singleton index
returns the exceptional value 7, while the same function over all Nat returns
the neutral value even though its nonneutral support is a singleton. That
paired case specifically detects the tempting support-based mistranslation.
An empty index type also produces the neutral values without an inhabitant.

### All six interval forms and the printed defect

The source table's upper interval `{..y}` has an incorrect internal-name
cell; the defect was visually confirmed in the pinned PDF. The candidate
correctly maps the upper interval to `Set.Iic y`, records the correction, and
checks distinguishing Nat cases at 0 and 2 with endpoint 1.

`all_interval_memberships` proves the six actual lower/upper endpoint
predicates for `Ici`, `Iic`, `Icc`, `Ico`, `Ioc`, and `Ioo`. The corrected
signature uses `Preorder`, which is the exact domain required by the pinned
standard interval definitions. The earlier separate `LE`/`LT` signature did
not elaborate; it was not an established more-general API. The correction
retains the ordered source domain without adding totality or antisymmetry.

## 7. Public integration, corrections and carried findings

`SquareApplications.lean` adds the four new example imports, which connect
the two new resource modules transitively. The accepted Chapter 1 repair
imports remain. The notation map and reconstruction-map changes preserve
the value/cost and source/extension boundaries described above. The updated
reconstruction prose records accepted Chapter 1 and Chapter 2 activation;
it does not constitute acceptance of this foundation or the complete sorting
chapter. Acceptance evidence remains in the control records.

Relative to saved prefix P, the insertion core, insertion examples and
ListLibrary file are byte-identical. The ListCalls correction renames the
reserved local binder, repairs the proof-only simp form and qualifies
`Nat.two_mul`; the matching example binder change is semantic-preserving.
The actual algorithms, recurrence constants, output observations and theorem
hypotheses remain unchanged.

The notation correction replaces deprecated set imports/API use, repairs the
standard interval capability, and proves the same multiset boundary using
membership/cardinality. The interval domain correction was assessed against
the actual source and pinned standard definitions above. No cost model,
expected case, payload capability, dependency, toolchain, build tool or
warning policy was changed to obtain the focused pass.

| Carried ID | Original issue | Spec disposition on f17cc6b |
| --- | --- | --- |
| `FDN-ELAB-001` | Reserved ListCalls local binders and proof elaboration/linter failures, followed by the masked unqualified `two_mul`. | The changes preserve statements and execution observations. Focused attempt3 confirms the corrected modules compile. Source repair is adequate; full-candidate confirmation remains pending. |
| `FDN-ELAB-002` | Deprecated set API use, missing standard interval capability and an unavailable decision instance for the support predicate. | Standard API/domain and proof corrections retain the intended source meaning. Focused attempt3 confirms compilation. Source repair is adequate; full-candidate confirmation remains pending. |

These IDs remain visible; neither is erased by the new base or labeled
finally closed solely because the focused build passed. There are no new
concrete `FDN-SPEC-*` findings. The validation hold below is a required-evidence
status, not an invented source defect or an additional review axis.

## 8. Validation status and remaining acceptance work

| Evidence | Established fact | Limit |
| --- | --- | --- |
| Accepted Chapter 1 fresh baseline | The prerequisite and native setup were already accepted by the owning workflow. | This does not verify the new foundation candidate. |
| Historical `shared-foundations-validation.json` | Preserved earlier scope/evidence, including a later XP01 draft. | It does not match this candidate and is not reused as current success. |
| Focused attempts 1 and 2 | Actual failures are retained in their original provenance directories. | They are not rewritten as successes. |
| `provenance/chapter02-foundation-focused-attempt3/result.json` and complete log | Actual exit 0 on unchanged clean f17cc6b; all six foundation targets passed. | Focused compilation is not the whole guarded build or exhaustive audit. |
| `provenance/chapter02-foundation-full-attempt1/` | Root owns `./check.sh --candidate HEAD` using the exact supplied native kit, threads 1. At report time root reported the run active and `result.json` was absent. | Terminal result, complete audit, and a new matching verification record are still required. |
| Immediate `./check.sh --verify-candidate HEAD` | Required by the existing review loop before acceptance. | Root must perform it against the finally approved same candidate after both axes are complete. |

The focused attempt3 recorder starts at 2026-11-03 21:24:10.447407 UTC and
ends at 21:24:14.975707 UTC, with actual exit 0 and elapsed time approximately
4.528 seconds; the native-kit run reports 4.479 seconds. Its result is 1,334
bytes, SHA-256
`6ef3c6f3f926c53a32810f053280d1d8bac60296886f16e07aaed117e4ac9f54`.
Its complete 7,782-byte log has SHA-256
`c7ad375385228d3bd1fc17d6b781de382147639eac4ecd2ec7b9618b4ac3de60`.
The recorded 1,071 Lake jobs include dependencies and are not a count of new
project modules.

The focused recorder observes the earlier Chapter 1 `.lake/verification.json`,
whose SHA-256 is
`8d9257a238ab4c2e0743a41851a080f403aa09b41f4bf34690496c1f9a7b0264`.
That is not a foundation verification record. A running full log, cached
artifact, or absence of a currently visible error is not terminal success.

Remaining advisory module-import warnings in the successful focused output
do not themselves establish a semantic failure. The actual blocking errors
from the earlier attempts have specific retained dispositions above. No
diagnostic suppression or warning-policy change was used. The Standards
axis assesses applicable warning policy against the complete log; this Spec
axis has identified no mathematical consequence in the retained advisory
diagnostics. The full run's actual diagnostics must still be reconciled.

The applicable route is the ordinary guarded check following the accepted
fresh native baseline, because these are source-only changes. This reviewer
found no concrete trigger requiring another fresh baseline or an extra
fixture gate. The user waived Nix only. The exhaustive source-policy/output
integrity/axiom audit, exact pins and same-candidate validation remain required.
Source inspection found no admission or newly introduced axiom, but that
inspection is not a substitute for the complete required audit.

Once root supplies the actual terminal full result, complete guarded-build
and audit evidence, and matching candidate record, this same Spec axis can
reconcile that evidence into this report without starting a duplicate source
review. A candidate change would instead require review of the full updated
task scope and any affected dependencies under the retained loop. Both
independent axes, immediate candidate verification, integration records and
the recovery checkpoint remain separate completion obligations.

## 9. Explicit outcome

- **Base:** `07e480f6ec9958d4975bb90151005b84f2907614`.
- **Candidate:** `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.
- **Spec findings count:** 0 concrete source findings.
- **Worst Spec issue:** none identified in the completed source assessment.
- **Carried implementation findings:** `FDN-ELAB-001` and `FDN-ELAB-002` retain
  source-adequate corrections and focused confirmation, with complete-candidate
  confirmation pending.
- **Spec outcome:** **Blocked**, solely pending actual full terminal
  build/audit/verification-record evidence. This is not a Passed review or
  authorization to integrate the candidate.

This report was written only after the coordinator released checkpoint0079's
writer hold. No candidate source, Git ref, dependency, build process or cache
was changed by this reviewer.
