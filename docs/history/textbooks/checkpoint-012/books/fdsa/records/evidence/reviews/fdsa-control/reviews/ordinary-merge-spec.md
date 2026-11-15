# FDSA-XM01 ordinary merge — independent Spec review

Recorded 4 November 2026. This is the independent Spec axis of the existing
ordinary-merge implementation/review loop. The reviewer authored no XM01
source. Its separate Chapter 2 bottom-up draft remains outside this candidate
and under an edit/build hold.

**Outcome: Blocked pending applicable complete-candidate validation.**
The full source assessment is complete with **zero concrete Spec findings**.
The exact candidate's three-target focused build and required 17-declaration
type inspection passed. Neither supplies the integrated source/coverage checks,
both integrity phases, exhaustive audit or matching full-candidate verification
record. No XM01 acceptance, foundation acceptance or whole-chapter completion
is claimed.

## 1. Immutable scope and review inputs

| Item | Independently checked identity |
| --- | --- |
| Fixed accepted Chapter 1 base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Merge base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Candidate | `72a0951aee406f7db67998d2a3bf8810f4e1bccc` |
| Original source draft | `5f409e71bb068e3b8cc133226046ce8bbe29d982` |
| Resource proof correction | `57a7d338dedb53a5526bbbc05f7be5fd83443d03` |
| Recovered isolated checkout | `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ordinary-merge` |
| Diff | `git diff 07e480f6ec9958d4975bb90151005b84f2907614...72a0951aee406f7db67998d2a3bf8810f4e1bccc` |

Read-only Git checks confirmed the exact clean checkout HEAD, matching merge
base, three-commit inventory and nonempty complete diff: **six paths, 1,002
insertions and no deletions**. No source path is excluded. All six files were
read in full through `git show`, rather than reviewed from another worker's
mutable draft. Their working copies match those candidate objects.

| Candidate path | Bytes | SHA-256 |
| --- | ---: | --- |
| `Applications/Resources/ListMerge.lean` | 8,629 | `df38ab6fd95baca45be4c5f7e6cd86f4e168fbff0ab21899783c8b52a41d1975` |
| `Applications/Sorting/Merge.lean` | 7,840 | `951db5238af4e2acd9a987318f04023de6d039156094f50a6ce775a4c6a7aac7` |
| `Examples/MergeCosts.lean` | 23,410 | `ae3e60b22c4b03cd78d33f5fe44729b83bb26ab589e014a9039927319d4f1466` |
| `SquareApplications.lean` | 8,319 | `ef3d3bbac7d252aa6c2575f619001176347f083f452802148c968c6e37ccca41` |
| `docs/research/fdsa-list-merge.md` | 14,955 | `25f1982d56183111c112d3e38f4473000668685d126677935dcecc3d1a5cf5b3` |
| `docs/research/fdsa-reconstruction-map.md` | 17,800 | `f59022d0709bbb48bdf976021c3c0bbf29861af3eddab377e9ef9fb491c948ff` |

The **entire** frozen `reviews/ordinary-merge-requirements.md` was read. Its
identity remains 19,999 bytes / 346 lines, SHA-256
`b54e2b332cc31c04ac12fb5b19cc96fa494a80e1455fcfc173f59b6fe340d3d9`.
The scope is all eight sections, including every required connected family,
source/license distinctions and validation/integration conditions. Historical
status wording does not undo accepted Chapter 1 or waive any current gate.

The complete round record/identity, original candidate record and source
assessments were read, including all DOC dispositions and both subsequent
proof-correction patches. The pre-code assessment and relevant primary-source
sections of the frozen source preflight were also inspected. Author/root
readbacks are retained evidence; the assessment below independently checks the
actual candidate's mathematics and uses.

Applicable repository code-review, statement-review and review-loop guidance
was applied. Relevant unchanged contracts were read from the candidate Git
objects: `Measured`, `CallCount`, `CallComparison`, `SourceMerge`, `Stable`,
`LeftistQueue` and the complete existing `StableSorting` example. The original
contents of `Sorting.Merge` were also read. Sixteen baseline source/tooling
identities from the original capture were independently rechecked and remain
unchanged. The complete original Merge file is retained around the four added
declarations; removing the single added `Examples.MergeCosts` import recovers
the original public root exactly; the complete old reconstruction map remains
an unchanged prefix.

## 2. Primary source and declared observation boundary

The recovered pinned July 27, 2026 PDF is available at
`/workspace/scratch/b4a17a285e23/research-source/functional_data_structures_algorithms.pdf`,
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The actual source pages were read: printed pp.17–18 / PDF pp.23–24 for merge,
correctness and comparisons, and printed pp.180–181 / PDF pp.186–187 for the
chosen priority-queue exercise reuse.

The book's ordinary merge returns the other operand at an empty side and,
when both sides are nonempty, compares the two heads and removes exactly the
selected head. Its comparison observation has zero empty-side bases and one
comparison plus the same selected recursive observation. The loose source
bound is the sum of input lengths. The candidate matches these equations;
it does not replace the comparison count with a function-entry count.

The pinned Lean `Init.Data.List.Sort.Basic` recurrence, relevant `Sort.Lemmas`
APIs and the runtime-replacement declaration in `Sort.Impl` were inspected
read-only. `List.merge` has the same verification recurrence. Its runtime
replacement is a separately proved value equality to `mergeTR`; that fact
does not transport the candidate's logical call counts to compiled helpers,
allocation, stack use or elapsed time. The candidate explicitly preserves
this boundary.

The invocation observation is a separately declared interpretation of this
same logical merge, with one for an empty-side call and one for each selected
nonterminal call. It includes exactly one terminal invocation. Comparing two
heads is one unit regardless of the comparator's internal work; key computation,
cons, untouched-suffix traversal and external preparation have no extra charge
in the declared comparison observation. These limitations are explicit in the
core header and source note, not hidden behind output equality.

Exercises 14.1 and 14.3 leave implementation choices open. The book requests
a list-based mergeable queue and a heap-to-sorted-list implementation with a
quadratic bound; it does not prescribe this component's exact local invocation
tariff. The candidate labels ordinary list merging and root-plus-child-list
merging as chosen ingredients. It does not claim that those complete exercises,
their carrier correspondence or their whole-execution bounds are already proved.

## 3. Value layer and sortedness converse

**Assessment: all four required additive contracts are present with the
intended weak assumptions.**

`sublist_merge_left` and `sublist_merge_right` follow the actual head-selection
recurrence. The selected input head is retained with `Sublist.cons_cons`; the
other input is embedded under the newly emitted head with `Sublist.cons`.
Both recursions decrease the sum of input lengths. The result preserves ordered
occurrences within each operand, including duplicates. It is stronger than
support or permutation preservation and requires no ordering law, payload
equality, inhabitant or sorted-input assumption.

`pairwise_of_merge` transports an arbitrary independent relation `R` through
those two sublists using `List.Pairwise.sublist`. The relation is not identified
with the Boolean comparator and needs no decision procedure, reflexivity,
transitivity or totality. Thus the converse is meaningful even when the
comparator has no ordering contract.

`merge_sorted_compatible_on_iff` combines that converse with the existing
forward theorem. Its hypotheses are exactly the existing key `LE` and
`Std.IsPreorder`, plus the two comparator-branch implications for actual
cross-input members. It does not require comparator behavior outside those
members, a global linear order, antisymmetry, payload comparison or key
injectivity. The forward direction still requires both input runs to be
sorted; the converse itself uses none of those extra order hypotheses.

The source/key clients instantiate this generic iff at the actual comparator
`decide (key a ≤ key b)` and connect the existing source adapter. A total
preorder on keys supplies the false-branch ordering implication. Raw source
value agreement itself uses only `LE` and `DecidableLE`; the stronger order
capability is introduced only for sortedness. The existing original forward,
filter, stability and combined contracts are unchanged.

The malformed input `[3,1]` is retained as a sublist for every comparator.
`unsorted_for_every_comparator` derives its impossibility of sorted output
through the public arbitrary-relation converse, not a test of one comparator.
This supplies a nonvacuous use of the new reverse implication.

## 4. One measured execution and exact counts

**Assessment: the operation, values and both cost coordinates follow the same
actual selected recursion.**

`Resources.ListMerge.run` uses the existing
`Measured (List α) (Nat × Nat)` with coordinates **(comparisons, invocations)**.
Either empty-side branch returns its remaining input with `(0,1)`; two empty
inputs therefore mean one call. A nonterminal branch evaluates the Boolean
head comparison, recursively executes only the selected smaller pair of lists,
and uses `Resources.bind` to cons the selected head onto that returned list
while adding `(1,1)`. There is no separately chosen pure output, no independent
scalar recursion and no charge for the unselected branch.

The charge is accumulated after the returned child observation through `bind`.
For these two natural-number totals this equals the stated one-plus-child
recurrence. No event-order trace is claimed or required. Termination uses the
sum of input lengths, which decreases by one in either branch regardless of
comparison behavior or sortedness.

`comparisons` and `entries` are transparent projections of that execution.
The reviewed public coverage is:

| Required claim | Candidate witness and assessment |
| --- | --- |
| Whole-pair empty and selected-branch equations | `run_nil_left`, `run_nil_right`, `run_cons_cons`; preserve the returned operand/child and both observations. |
| Value erasure | `run_value`; follows the same branch as the canonical `List.merge` on arbitrary inputs. |
| Source comparison equations | `comparisons_nil_left/right`, `comparisons_cons_cons`; zero bases and one plus the actual selected child's count. |
| Invocation equations | `entries_nil_left/right`, `entries_cons_cons`; one base and one plus the same selected child's entry count. |
| Existing scalar entry model | `run_entries_cons_cons`; `reweight Prod.snd` is `CallCount.tick` of the actual projected child followed by uncharged cons. |
| Exact relation | `entries_eq_comparisons_add_one`; every execution path ends at exactly one no-comparison terminal call. |
| Source bound and derived entry bound | `comparisons_le`, `entries_le`; length sum and length sum plus one, without a tightness claim. |
| Positive nonterminal cost | `comparisons_cons_pos`; both nonempty inputs force the first comparison. |

All these statements allow arbitrary payload universes and comparators. They
have no sorting, comparator-law, finite-carrier, payload-equality or inhabitance
premise. The required type inspection confirms that the elaborated raw erasure,
entry-relation and bound interfaces retain these assumptions.

Value clients obtain permutation, multiset sum, length sum and membership union
through `run_value` and existing standard merge laws. The resource module does
not introduce a parallel value theory. Source and key clients compose actual
erasure with `sourceMerge_eq_merge` / `mergeBy_source`; their type inspection
shows no hidden payload order instance in the public hypotheses.

## 5. Exact map transport and stability qualifications

**Assessment: full measured transport is proved from branch agreement, and
the examples use it on actual noninjective key erasure.**

`run_map` relates the entire measured run on mapped operands to the mapped
returned list and unchanged pair of observations from the original run. Its
premise is comparison equality only for original cross-input members. Each
visited head pair belongs to those operands; the proof restricts that premise
to the actual left or right tail before invoking the induction hypothesis.
Consequently the same selected branches justify both the values and counts.

The result is not inferred from `List.map_merge` or pure output equality.
`f` need not be injective; source and result universes are independent; no
payload equality or order is needed. The type-inspection output explicitly
retains two universe parameters for this theorem. The contract describes two
declared merge executions, without claiming that computing input/output maps
in an external caller has no work.

`tagged_key_transport` applies `run_map` to `Prod.fst` in both operand orders
for arbitrary payloads at key one. `tagged_counts` obtains `(2,3)` and `(1,2)`
from those full-pair transport equalities and the independent unlabelled tied
cases. `tagged_values` separately establishes the actual full-record orders.
There is no injectivity premise that would defeat this use.

The existing `StableSort` contract observes sorted keys, full-list permutation
and the complete filtered sequence at each equal key. The signed-record client
proves its actual input blocks sorted, uses `mergeBy_spec` through erasure and
compares with the accepted `StableSorting.expected_spec` using uniqueness on
the concrete integer key order. It separately derives two comparisons and
three entries from the actual recurrence. No payload order or new sorting
specification is introduced.

The required counterexamples preserve both substantive stability qualifications:

- An always-false comparator on equal-key tagged inputs satisfies the local
  sortedness compatibility premise and preserves occurrences, yet returns the
  right tag first. `compatible_not_stable` refutes the full filtered-order
  contract for that actual output.
- Under the genuine left-on-equality key comparator, the unsorted tagged
  operands produce the right pair followed by the left pair. Their key-one
  filter is `D,B`, whereas input concatenation gives `B,D`. Thus left ties
  alone do not remove the sorted-block premise of `mergeBy_filter`.

## 6. Connected expected cases and actual sequencing

Every mandatory compact family from frozen section 6 is present. The
independent expected lists and counts agree with the source recurrence; the
proofs consume the public operations/laws and existing observation contracts.
The observations below are `(comparisons, entries)`.

| Family | Independently expected observation/value | Candidate connection |
| --- | --- | --- |
| Empty sides and `List Empty` | Remaining list, `(0,1)`; no default payload | `empty_sides`, `empty_payload`, actual whole-pair base equations. |
| Low/high singleton | `[0]` with `[1,2]` gives `[0,1,2]`, `(1,2)`; `[2]` with `[0,1]` gives the same value, `(2,3)` | Public branch equations; scalar entry client also uses `run_entries_cons_cons`. |
| Interleaving duplicates | `[0,2,2]` with `[1,2,3]` gives `[0,1,2,2,2,3]`, `(4,5)` | Six-element length, actual multiset/support observations and count three for 2. |
| Constant comparator, arbitrary payloads | Always true gives `[a,b,c]`, `(2,3)`; always false gives `[c,a,b]`, `(1,2)` | Actual selected branches without order/equality capabilities. |
| Tied operands and their swap | Same unlabelled `[1,1,1]`, costs `(2,3)` versus `(1,2)` | Explicit equality of values/lengths/permutation plus inequality of both coordinates. |
| Unsorted numeric operands | `[3,1]` and `[2,1]` give `[2,1,3,1]`, `(2,3)` | Unrestricted cost bounds, both public sublists and the every-comparator unsortedness converse. |
| Signed records | Negative record first, then left and right key-two records, `(2,3)` | Accepted expected specification, actual sorted-block contract and recurrence counts. |
| Arbitrary tagged payloads | Left records first; swapping operands changes full-record order and counts | Both full-pair `run_map` uses, separate value witnesses and existing stable contract. |
| Stability boundaries | Compatible right ties fail stability; unsorted left-tie inputs fail equal-key filter order | Actual execution equalities and full `Stable` counterexamples. |

`twoStage` is the literal value-dependent bind required by the scope: the
second merge receives the first run's actual returned list. `twoStage_value`
and `twoStage_observation` use `bind_value` / `CallCount.let_rule` on this
definition. The actual first result's length is supplied by `result_length`.
Consequently total comparisons are bounded by
`2 * (xs.length + ys.length) + zs.length`, and total entries equal total
comparisons plus **two**, yielding the stated plus-two bound. Neither wrapper
entry nor any cost for an unexecuted alternative is added.

Both scalar projections use the existing coordinate additive homomorphisms
and `reweight_bind` on that same value-dependent continuation. The affine
single-run relation `E=C+1` is not passed off as an additive homomorphism.

The actual discriminator is retained: merging `[2]` with `[0]` yields `[0,2]`
at `(1,2)`, then `[1]` with that result yields `[0,1,2]` at `(2,3)`, totaling
`([0,1,2],(3,5))`. The erroneous continuation using `[2,0]` instead gives
`([1,2,0],(2,4))`. `actual_input_matters` checks inequality of both resulting
values and observations. This would detect the material error of feeding an
independently substituted concatenation to the second measured execution.

## 7. Raw queue-body client and C1 tariff application

**Assessment: the queue client is the actual existing node body, with exactly
the limited local cost promised by the requirement.**

`queueBody` merges actual `toListQ l` and `toListQ r` values by priority and
uses `bind`/`pure` to prepend the root pair without an additional observation.
`queueBody_value` identifies that returned list with
`toListQ (PQ.fork k x p l r)` for arbitrary raw rank `k`, payload, priority
and subtrees. Its only ordering capabilities are `LE` and `DecidableLE` on
priorities. No `Heap`, `Ranked`, payload equality or payload order premise
appears. Payload and priority universes remain independent.

The observation is exactly the single ordinary merge's comparison/entry pair.
`toListQ_perm.length_eq` and `entries_length`, which hold on raw queues, supply
the actual child-list lengths. They give the requested merge-only bounds
`C ≤ size l + size r` and `E ≤ size l + size r + 1`. Heap-dependent sortedness
is not used to manufacture those lengths or to strengthen the raw value law.

The malformed fixture is the required raw rank-99 root with priority nine and
rank-zero leaves at priorities one and two. Its body value is the full list
`[((),9),((),1),((),2)]` and its observation is `(1,2)`. The example proves
that this actual output is unsorted. Child traversals, their sequencing and
entries, the enclosing node entry, a source-tree/carrier bridge and a quadratic
whole-enumeration theorem remain outside this local count. The current source
does not claim otherwise.

For the actual nonempty merge executions, `comparisons_cons_pos` discharges
the positive-cost premise of existing `CallCount.add_entry_le`.
`nonempty_tariffs` obtains `C ≤ E ≤ 2*C` from that fact, the exact entry
relation and `cost_le_add_entry`. The low-singleton execution attains `C=1`
and `E=2`. The empty-side execution has `C=0,E=1`, so
`zero_cost_entry_matters` refutes `E ≤ K*C` for every natural `K`. This is
the required qualified comparison; it is not promoted to a uniform bound
over zero-comparison inputs. `CallComparison` is imported only by the examples.

## 8. Source/license documentation and remaining scope

The source note retains the pinned PDF/version/hash and the exact companion
Isabelle revision/theory hashes from the frozen source preflight. It identifies
Tobias Nipkow's companion theory, distinguishes that revision from the
manuscript's generation revision, and keeps ordinary merge separate from the
AFP natural-sort work. The current review checked the mathematical equations
directly against the recovered book and native Lean source; it does not claim
to have rerun the manuscript's Isabelle build.

The complete original Isabelle notice can be recovered from the retained
pre-correction note. Including its final newline, it independently hashes to
the frozen `ISABELLE-COPYRIGHT` identity
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
An exact comparison shows that the current candidate's notice differs only
by removal of trailing line spaces, as disclosed. Copyright attribution,
all three conditions and the complete disclaimer remain. The candidate also
distinguishes Lean FRO/Apache-2.0 source provenance and existing dependency
notices. It introduces no copy of the book manuscript into the source paths.

The source note now correctly calls the comparison bound the source bound
and the invocation bound a derived fact in the separately declared model.
The appended map explicitly identifies the first and second **cost**
coordinates as `run.2.1` and `run.2.2`; it does not mistake the returned list
`run.1` for a count. The note and map retain their conservative source-draft
qualifications, while the later control records provide the now-established
focused results. No narrative source map claims full validation or acceptance.

The direct source mapping is complete for C02-025, C02-027's merge termination,
C02-028/029/031/033/035/037. The component does not claim all of C02-027, the
whole-sort recurrence/cost composition, C02-107 stability or any other retained
Chapter 2 obligation. The original 107-row requirements and reconciled 112-row
inventory remain mandatory. All actual floor-left, logarithmic/power-of-two,
bottom-up/natural, scanner/builder, exercise and full-sort obligations retain
their separate scopes.

Chapter 14's full concrete queue laws, direct minimum/deletion costs, complete
measured enumeration, carrier correspondence and quadratic theorem also remain.
Binomial merging consumes and links equal-rank roots and propagates carries;
the candidate does not identify it with this one-head ordinary list recurrence
or its tariff. The initial shared prefix remains exactly `c80eec9`, without XM01.

## 9. Corrections and carried findings

Both recorded correction patches were compared with the original source
draft and the current files. They change proof scripts only: redundant simp
arguments/map-cons normalization in the resource proof; local-instance syntax,
explicit existing map inputs, recurrence simplification, closed projection
reduction and projection inference in examples. The algorithms, theorem
statements, hypotheses, tariffs and independently expected values remain.

| Stable ID | Independent Spec disposition on this candidate |
| --- | --- |
| `XM01-PRE-DOC01` | Historical pre-code status/punctuation clarification retained; no mathematical expectation changed. It does not turn the initial foundation prefix into accepted work. |
| `XM01-DOC01` | Fixed in the current note: printed comparison-bound provenance is separated from the derived invocation bound. |
| `XM01-DOC02` | Fixed in the current map: explicit cost coordinates `run.2.1` / `run.2.2` remove the measured-pair projection ambiguity. |
| `XM01-DOC03` | Fixed and disclosed: exact original notice recovered and hashed; current complete notice is its trailing-space-normalized form. |
| `XM01-ELAB-001` | Source-preserving resource proof correction independently confirmed; exact-candidate focused build passes. Complete-candidate confirmation remains pending. |
| `XM01-ELAB-002` | Source-preserving example proof correction independently confirmed; focused build and 17-type readback pass without weakening premises or expectations. Complete-candidate confirmation remains pending. |

There are no new concrete `XM01-SPEC-*` findings. The missing full gate is a
required-evidence block, not an invented source defect or an erased finding.

## 10. Validation evidence and explicit outcome

The complete closed successful focused and type-inspection logs were read,
along with their recorder/native results and the exact inspection source.
Their bytes were independently hashed. The failed attempts remain failures;
they are not relabeled by the succeeding correction.

| Evidence | Established result | Limitation |
| --- | --- | --- |
| Focused attempt1, original `5f409e7` | Actual exit 1; preserved resource elaboration diagnostics. | Superseded by a source-preserving proof correction, not erased. |
| Focused attempt2, `57a7d33` | Actual exit 1; resource/value targets passed, connected examples needed correction. | Preserved with its actual candidate and closed log. |
| Focused attempt3, exact `72a0951` | Actual exit 0, 31.376 s recorder / 31.265 s native command; all three requested targets succeeded. | No integrated check, exhaustive audit or candidate verification record. |
| Required 17-type inspection, exact `72a0951` | Actual exit 0, 28.112 s recorder / 27.998 s native command. | Confirms the inspected elaborated interfaces, not a whole-project audit. |
| Private native development environment | Recorded idle dependency-tree ownership transfer and successful full doctor; one Lean thread, separate from foundation outputs. | Environment qualification is not acceptance of this source. |

Focused attempt3's result is 1,241 bytes, SHA-256
`1b285b8bdd2a2d7ff160e925ef259b9fb48327a89589ff36eabe91b10b2b4c30`;
its complete 2,325-byte log has SHA-256
`2898f1aef4e952cffdcc64fc4ac449bea3d105dc90f02f2706b8d97772c5f5a1`.
The type-inspection result is 1,306 bytes, SHA-256
`b410a2972784d2bc661f17599d0c0ed66e27639e77df06da34b3de7aa7bde883`;
its complete 9,351-byte log has SHA-256
`4645276a14c159ab587b16acb8d11e8db95615c9a41c8fff69384c4b42f85910`.
The 1,586 focused Lake jobs include dependencies; this is not a count of new
proofs or an exhaustive audit result.

The type readback confirms both raw sublists, arbitrary-relation converse,
input-local keyed iff, raw erasure, independent-universe full-pair map theorem,
entry relation/bounds, tick projection and the selected source/tagged/sequencing/
queue clients. No payload equality, order or inhabitance capability was hidden
in the raw interfaces. The complete focused log includes module-import
advisories in existing files and in the new `Examples.MergeCosts` file. No
mathematical consequence was identified; these are not all mislabeled as old
baseline warnings, and no source policy or linter was disabled. Applicable
warning-policy assessment belongs to the independent Standards axis.

The exact first foundation candidate has its own outstanding acceptance loop.
XM01's required full check is not supplied by that other candidate's check.
After the exact accepted predecessor is incorporated, root must record the new
base/candidate and all resolutions, preserve this full scope/findings, and
obtain the applicable full `./check.sh --candidate HEAD` evidence, both integrity
passes, source/public coverage, exact pin checks, integrated build and exhaustive
transitive axiom audit. Both independent axes must assess the finally delivered
candidate. Immediate `./check.sh --verify-candidate HEAD` must then match that
approved candidate before local integration. Fresh mode remains governed by
actual README/runbook triggers; no source-review conclusion waives a gate.

**Base:** `07e480f6ec9958d4975bb90151005b84f2907614`.
**Candidate:** `72a0951aee406f7db67998d2a3bf8810f4e1bccc`.
**Concrete Spec findings:** **0**; worst source issue: **none identified**.
**Source assessment:** complete for the entire frozen XM01 scope.
**Overall Spec outcome:** **Blocked**, pending applicable complete validation
and final same-candidate evidence. This is not acceptance.

Only this new review report was written. No candidate source, historical
assessment, Git ref, dependency or build output was modified. The reviewer
launched no compiler, checker or additional review workflow. The separate
foundation Spec terminal continuation remains retained and independent.
