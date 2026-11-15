# Shared foundations — independent Standards review

Reviewer: `/root/foundation_review_coordinator/standards`.
Source assessment completed 3 November 2026, approximately 21:39 UTC.

## Current outcome

**Blocked pending the actual full candidate validation result.** The complete
nine-path source Standards assessment is finished with **zero concrete
Standards findings; worst source issue: none**. The focused six-module build
has passed on the exact candidate. The root-owned whole-candidate check was
still active when this source report was prepared, and its terminal result and
matching foundation verification record were not yet available.

This is a completed source assessment with a validation hold, not approval of
the foundation integration. The same reviewer can reconcile terminal evidence
in this report without starting another review loop. The independent Spec axis
and root's immediate candidate verification remain separate obligations.

## Immutable scope and continuity

| Item | Reviewed identity |
| --- | --- |
| Incorporated accepted Chapter 1 base and independently confirmed merge-base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Exact immutable candidate | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |
| Original combined foundation base, preserved in the record | `1aabd512284fe86254278ac631eda061d311050b` |
| Exact first shared prefix incorporated into the accepted base | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Isolated checkout | `/workspace/scratch/31d6377eca78/fdsa/conaled-ch01-review` |
| Review comparison | `git diff 07e480f6ec9958d4975bb90151005b84f2907614...f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |

The independently inspected comparison is nonempty: nine paths, 1,515
insertions and six deletions. It includes both resource modules, all four
example modules, the public import root and both research maps. No task source
in that comparison is excluded. The commit inventory after the accepted base
is `697bcf2`, `333f900`, `df116c2`, `c994c22`, `50dc7df`, `c80eec9`, `0c93725`,
`9875bfd` and `f17cc6b`. Read-only Git checks confirmed exact candidate HEAD,
empty porcelain status and the stated merge-base. `git diff --check` passed.

This continues the existing combined X002 / APP-A / XB01 / APP-C workflow. The
accepted incorporated Chapter 1 commit is the updated base under the retained
review-loop rule; this does not erase the original requirements, history,
failed elaboration attempts or source-only assessments. The later XP01 change
at `c28ba718` remains outside the exact first prefix under the existing shared
integration preflight. Its requirements are not waived. This foundation scope
does not accept all of Chapter 2 or the algorithm-specific remainder of
Appendix B.

The complete frozen requirements were read and their byte identities were
independently checked:

| Record under `fdsa-control/reviews/` | Bytes | SHA-256 |
| --- | ---: | --- |
| `insertion-requirements.md` | 3257 | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `list-library-requirements.md` | 3123 | `83cffa5aff717943d449f4380189a9e9a761252730f5a14f4e392f1e62d154d4` |
| `list-calls-requirements.md` | 4040 | `0a2f7a2869c10276da2cc9a852e20936c6aba2d094d5232b96e94fbf47ecf78d` |
| `notation-requirements.md` | 3406 | `21a4ad13752d4316817e97f655af9a768726aa682124a39a2aeac248460b5a48` |

The historical blocked/queued prose in these frozen records does not supersede
the actual accepted Chapter 1 prerequisite. Their mathematical and integration
scope remains unchanged. The full `REQUEST.md`, current combined round record
and historical validation record were read. The user's explicit Nix exception
and local-ticket/no-GitHub-write instructions govern; exact compiler/library
pins and formal validation requirements remain applicable.

## Applicable standards and review method

The candidate's `AGENTS.md`, README development/build/audit guidance,
`docs/agents/review-loop.md`, architectural-quality and domain guidance,
glossary, ADR index, ADRs 0001 and 0010, the example-driven-development skill
and worked example, and the code-review skill and heuristics were read. No
applicable `CODING_STANDARDS.md` or `CONTRIBUTING.md` was found in the ordinary
candidate inventory.

The applicable rules require ordinary native clients, reuse of established
carriers/interfaces, separation of operations and observations from laws,
appropriate minimal assumptions, meaningful connected examples, explicit
statement review, public coverage and matching validation. The code-review
skill prohibits promotion of missing, stale or incomplete required validation
to a passing result. The heuristics are subordinate to the mathematical and
repository setting; no pattern alone is reported as a defect.

All six Lean additions were read completely, together with the complete
`SquareApplications.lean`, notation map and reconstruction map. Relevant
unchanged interfaces were read in full: `Resources.Measured`, `CallCount`,
`SymmetricCosts`, `ListReversal`, `Sorting.Sort`, `Sorting.Stable`,
`Selection.Rank` and `Examples.FunctionalBasics`. The relevant pinned Mathlib
insertion-sort and interval definitions were inspected. The insertion and
list-call preflights, the Appendix C set-fold reuse analysis and the retained
ListCalls/FunctionalNotation source-readiness report were also read.

Those preflights and readiness reports support continuity and identify intended
cases; they are not compilation or final acceptance evidence. In particular,
the earlier source-readiness assessment did not establish the now-repaired
interval elaboration or multiset proof. This review independently assesses
the actual corrected candidate. Full book-item completeness and primary-source
comparison belong to the separate Spec axis; this report does not substitute
its author's readiness judgment for that axis.

## Architecture, contracts and minimal capabilities

### Measured insertion sort

`Applications/Resources/InsertionSort.lean` uses the existing ordinary
value/observation pair and `CallCount.tick`. `insertRun` at line 19 is an actual
recursive insertion: it returns immediately when the head comparison succeeds,
otherwise recurses on the tail and adds one entry. `sortRun` at line 68 binds
the actual recursively sorted tail into insertion and adds the sort entry.
The erasure theorems identify these values with the existing canonical list
operations; costs are not deduced merely from a value equality.

The relation-level statements need only `DecidableRel`. They impose no payload
inhabitance, equality or global order laws. The head-only theorem really needs
only the first comparison; the all-members and all-failing conditions are
separate sufficient conditions. Pairwise source cases, universal lower and
upper bounds, the doubled triangular argument and the natural-division bound
remain distinguishable. The descending distinct range gives a worst-case
witness for every length, including zero and one, without treating duplicated
keys as strict descending witnesses.

The stability bridge at line 171 reuses the established `StableSort` contract
and key-side capabilities. Arbitrary payloads acquire no order/equality
instances. No antisymmetry is introduced where the existing linear-preorder
contract suffices. Selection/rank consumers live in the example module rather
than adding a dependency from the resource core to selection. Costs remain
counts in the declared source model; the code does not claim physical runtime
or charge a selection/indexing operation to the sort observation.

### Appendix A ordinary list interfaces

`Examples/ListLibrary.lean` reuses standard lists and list operations rather
than introducing a second list representation. The membership-set clients do
not require decidable payload equality. Half-open Nat ranges preserve endpoints
and reversed/zero-boundary behavior. Head and indexing bridges retain their
validity proofs or optional results. Invalid lookup returns `none`; an invalid
list update is the existing no-op. Repeated values do not obscure distinct
positions. The `Empty` clients demonstrate that no default payload was added.

The pairwise sorted relation at line 125 is kept distinct from an adjacent
chain for an arbitrary relation. The following counterexample supplies a
concrete consequence of that distinction. Literal list-sum equations need only
addition and zero. The source-style recursive minimum view explicitly adds
associativity of `min`; the operation itself retains its weaker `Min`
capability, and leastness uses the required ordered structure plus an actual
`some` result. The filtered-minimum client instantiates these premises.
Standard list value equalities are not promoted into cost claims about their
optimized implementations.

### Appendix B.1 actual callback observations and composition

`Applications/Resources/ListCalls.lean` reuses the established measured-value
representation and bind. `mapRun` and `filterRun` at lines 20 and 62 evaluate
the actual callback for each occurrence. Filter uses the returned Boolean to
select the output while paying the callback and tail traversal in both
branches. Their exact observations retain the occurrence sum plus `n+1`;
repeated equal values remain repeated summands. Constant-callback results
require constancy only on the supplied input's members. The input and result
types may inhabit independent universes.

Take/drop at lines 104 and 109 project the existing measured split, preserving
its observation and its zero/empty/cons equations. `take_drop_separate` at line
140 performs both operations on the original list and adds both observations.
It proves agreement of the returned pair and twice the fused split count;
equal values do not imply equal costs. Reusing the split implementation here
avoids redundant traversal definitions while giving the declared source
recurrences explicitly.

`lookupRun` at line 150 is sequential recursion with an optional value. Its
valid-domain count theorem explicitly requires `k < xs.length`. The total
`min k length + 1` observation includes the documented invalid-input extension
and does not retroactively attribute invalid-domain behavior to the book.
There is no default element, random-access shortcut or new tariff for the
existing Knapsack model. Actual output-to-input bind compositions with measured
length and append appear in the public examples.

### Native notation, partial operations and finite-index folds

`Examples/FunctionalNotation.lean` uses native binders, sets, lists, multisets,
finite sets and algebraic structures. There is no new parser, carrier family,
blanket decidability instance or framework. The Prop/Bool correspondence puts
decidability precisely on the executable bridge. Images and comprehensions
retain their witnesses and generator order. The set laws preserve arbitrary
types without global membership/equality decisions.

The corrected six-interval theorem at line 77 requires `Preorder`, matching
the actual standard interval API in pinned
`Mathlib/Order/Interval/Set/Defs.lean`. No totality or antisymmetry is added.
The Nat upper-interval cases expose the documented printed-source correction
on both sides of the endpoint. Integer floor division is distinguished from
Lean's default quotient: their general bridge has the nonnegative-divisor
premise, and a negative divisor separates them. Zero and negative-real
floor/ceiling cases retain the intended total and typed conventions.

Multiset support inclusion is explicitly separated from multiplicity-sensitive
inclusion. Repeated-value folds distinguish list/multiset observations from
deduplicated finite-set observations. These are useful native clients rather
than restated syntax claims.

The only new convention adapter, `finiteIndexProduct` at line 148 and its
generated additive counterpart, decides finiteness of the entire indexing set
locally and uses the standard finite fold when finite, the neutral element
otherwise. It is explicitly noncomputable. The public index type has no
equality, enumeration or inhabitance requirement. The value type needs exactly
the commutative monoid structure appropriate to an unordered fold. Finite,
Finset and infinite equations are exposed. The infinite-index examples with
finite support would detect substitution of the different finite-support
convention. Empty indices are exercised with a legitimate nonempty algebraic
value type. Ordered list folds require only monoid structure, without
commutativity.

Keeping this small source-convention adapter and reusable compositions in an
example module is consistent with the repository's native-client policy. It
does not justify a new generic folding framework or a per-glyph theorem quota.
There is no new compiler frontend, preservation family or tooling change to
trigger an unrelated cross-setting theorem or upstream-parity exercise.

## Connected examples and statement review

The retained cases connect public operations and theorems to observable
mathematical consequences. They are not supported solely by assuming their own
conclusions. The main connections checked were:

| Group | Checked public connection and boundary |
| --- | --- |
| Insertion entry counts | Empty/singleton, sorted duplicates, descending distinct range, universal bounds and the quadratic specialization consume the measured model and its public laws. |
| Immediate versus full insertion | A tied head succeeds even when a later tail comparison would fail; inserting 4 in `[1,2,3]` traverses fully and costs 4. |
| Stability and rank | Arbitrary payloads and distinguishable equal-key records use the existing stability contract; the actual measured sorted output supplies occurrence rank, including a repeated-value rank example. |
| Budget composition | The bound for length at most five supplies cost at most 21; the combined rank/budget client states exactly the sort's observation and value property. |
| List boundaries | Empty payloads, valid and invalid indexing, invalid update no-op, reversed/overlarge ranges, repeated-position updates and take/drop reconstruction use standard list laws. |
| List meanings | A flatten/filter/map/reverse pipeline retains order and repetition; the adjacent-chain counterexample protects the arbitrary-relation pairwise definition; actual filtered-minimum and repeated-minimum clients instantiate the minimum statements. |
| Callback occurrence costs | Map on `[2,2,3]` returns `[12,12,13]` with cost 11; discarded-head and discarded-last filters both retain `[2,2]` and still cost 11. Zero/unit callbacks and all-discarded output retain the expected entry/callback counts. |
| Measured composition | The actual mapped list feeds measured length, giving the concrete cost 15 and a general independent-universe formula. Actual append feeds measured length with the left-copy tariff retained. |
| Lookup and traversal | Valid position 2 returns `some 9` with cost 3; first and far-invalid positions both return `none` with cost 4. Separate take/drop costs 6 where fused split costs 3. Zero, excessive and empty-payload cases remain. |
| Notation boundaries | Prop/Bool decisions, corrected upper intervals, negative-divisor floor division, negative floor/ceiling, support versus multiplicity and repeated folds expose semantic differences. |
| Finite-index convention | Singleton value 7, infinite Nat indices with one exceptional value, empty indices and ordered list append folds exercise the public adapter equations and the exact neutral-otherwise convention. |

Simple reduction examples supplement these connections. No blanket rule
requires a separate example for each helper or notation row. No suspicious
vacuity, unnecessary payload capability or unexplained strengthening of a
source model was found in the reviewed statements. The source maps explicitly
record the meanings and domains that differ between Lean and the source
presentation. All twenty Appendix A entries, the seven B.1 call entries and
all ninety Appendix C rows are retained as mappings; the independent Spec
review determines full correspondence to the pinned book.

## Public integration and documentation

The complete public root retains the accepted Chapter 1 imports and adds the
four new example imports. Those imports bring both new resource cores into
the public closure. No old public import was dropped. This supports the
required whole-candidate coverage and exhaustive audit; a focused six-target
build alone does not establish that audit.

Both research maps were read in full. They retain source version/provenance,
exact statement pointers, partial-operation and arithmetic boundaries,
observation-versus-runtime limits and the finite-index convention. The
reconstruction map now truthfully records accepted Chapter 1 and active
Chapter 2 while keeping foundation readiness separate from complete chapter
acceptance. The original investigation base is historical provenance, not a
claim that the current integration uses that older base. The corrected
interval capability is recorded explicitly. No book PDF or large extracted
source text is added to the formal source diff.

## Carried compiler findings

No prior source Standards finding is discarded or silently renumbered. The
shared implementation findings remain visible with these dispositions:

| Stable ID | Actual correction and Standards disposition |
| --- | --- |
| `FDN-ELAB-001` | Reserved local `prefix` binders became `taken` (and paired `suffix` became `dropped`) in the separate take/drop theorem and its example. `lookupRun_valid` uses the unflagged simp proof. The formerly masked multiplication lemma is now explicitly `Nat.two_mul`. Statements, value/cost equations, hypotheses, universes and expected cases are preserved; binder changes are alpha-renaming. Focused attempt 3 confirms elaboration. Complete-candidate/audit confirmation remains pending. |
| `FDN-ELAB-002` | Deprecated set API/import usage was replaced with the current named APIs. The malformed interval declaration now supplies exactly `Preorder`, as required by all six standard interval constructors; this preserves the intended ordered source domain without totality or antisymmetry. The multiset conclusion is unchanged and its proof now uses membership and the impossible cardinal inequality `2 ≤ 1`, avoiding unavailable infinite-domain `decide`. Focused attempt 3 confirms elaboration. Complete-candidate/audit confirmation remains pending. |

The first and second actual focused failures remain part of the history. A
later passing focused run does not rewrite them as successful attempts. No
algorithm, source observation, cost tariff, expected case, compiler/dependency
pin or warning policy was changed by these repairs.

## Validation and warning disposition

### Actual focused success

The independently read record at
`fdsa-control/provenance/chapter02-foundation-focused-attempt3/` reports actual
exit 0, state `passed`, exact final candidate and empty final source status.
It ran the six explicitly named module targets through the supplied unified
native kit with one thread. Its start/completion times are
`2026-11-03T21:24:10.447407+00:00` and
`2026-11-03T21:24:14.975707+00:00`. The complete log ends with successful build
completion (1,071 Lake jobs including dependencies) and the kit's actual exit
0, elapsed 4.479 seconds.

| Focused evidence | Bytes | SHA-256 |
| --- | ---: | --- |
| `result.json` | 1334 | `6ef3c6f3f926c53a32810f053280d1d8bac60296886f16e07aaed117e4ac9f54` |
| `full.log` | 7782 | `c7ad375385228d3bd1fc17d6b781de382147639eac4ecd2ec7b9618b4ac3de60` |

The recorder's observed verification-file hash
`8d9257a238ab4c2e0743a41851a080f403aa09b41f4bf34690496c1f9a7b0264`
belongs to the previous accepted Chapter 1 verification record. It is not a
foundation success record and cannot discharge the present full-gate hold.

### Current ordinary full gate and applicability

The actual request/start records at
`fdsa-control/provenance/chapter02-foundation-full-attempt1/` name clean exact
`f17cc6b`, the supplied native kit, one thread, and the ordinary stock command
`./check.sh --candidate HEAD`. It started at
`2026-11-03T21:24:53.925501+00:00`. The log reports official Lean 4.35.0 at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and success of the source-policy,
public-coverage and version phase. The source guard reports no admissions,
source axioms, unsafe/partial definitions, `native_decide` or skipped kernel
checking.

The read-only log observation contains 937 cold trace-miss invalidations and
the integrity summary `hashed 87 artifacts; 937 modules invalidated`. Every
observed rebuild reason is the missing-file case; no contrary integrity
diagnostic was found in those records. This is evidence of ordinary guarded
rebuilding, not evidence of terminal full success. At the source assessment's
last observation there was still no `result.json`; the full log was live.

The accepted Chapter 1 report
`reviews/chapter01-standards-unified-final.md` retains the actual successful
fresh baseline and its matching compiler/dependency/audit evidence. The current
nine-path diff changes no checker, proof audit, compiler/dependency pin,
root-selection implementation or integrity implementation. The previous
validator-fixture applicability ruling therefore continues to apply; there is
no concrete new trigger for a duplicate fresh run or another fixture suite.
The ordinary full candidate check and exhaustive audit remain mandatory.
Environment setup or checkpoint round-trip checks cannot replace them.

### Concrete warning assessment

The focused complete log has nonfatal module-system import advisories in both
existing modules and new source. In the new source, they identify
`Mathlib.Tactic.Linarith` in the insertion core, the list big-operator import
in the list-call core, four Mathlib list imports in `Examples.ListLibrary`,
and the thirteen Mathlib imports in `Examples.FunctionalNotation`. These are
the compiler's import/module migration advisories, not the repaired deprecated
API diagnostic or a remaining proof/linter failure. Their text recommends
adding `module`; all six targets nevertheless completed successfully under the
unchanged pinned environment and policy.

All six new files retain `autoImplicit false` and `warningAsError true` after
their imports, following the existing source convention. No warning option,
build command or linter was suppressed. It would be inaccurate to label every
warning as coming from an unchanged baseline file: the new import advisories
are recorded here explicitly. No concrete rule violation or semantic/public
visibility defect follows from those advisories alone, and a broad module
system migration is not part of this bounded change. The complete full-run
warning inventory still requires assessment when the closed log is available.

## Required terminal reconciliation and final disposition

Before this axis can become Passed, the same reviewer must read the actual
terminal result and closed full log, confirm successful whole-candidate
compilation and exhaustive audit with the allowed axiom union, match the
retained verification record to the actual candidate record and exact pinned
compiler/dependencies, and reconfirm candidate identity/cleanliness. The final
audit must cover the public root and these six additions. Partial module
counts, printed per-module axioms, focused success or a previous candidate's
verification file cannot discharge this hold.

The coordinator separately needs the independent Spec outcome on the same
candidate. Immediately before acceptance/integration, root must perform the
stock `./check.sh --verify-candidate HEAD` and confirm the approved commit.
That subsequent action is not claimed by this source report.

This reviewer ran no compiler, build, source-policy runner, cache writer or
process-control action, and changed no source, Git ref/index, dependency or
root-owned evidence. The only write is this permitted outside-source report.
Checkpoint 0079's writer hold was respected and the report was written after
the coordinator released it.

**Base:** `07e480f6ec9958d4975bb90151005b84f2907614`.
**Candidate:** `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.
**Concrete unresolved Standards findings:** 0. **Worst source issue:** none.
**Standards outcome:** **Blocked — required terminal validation pending**.
