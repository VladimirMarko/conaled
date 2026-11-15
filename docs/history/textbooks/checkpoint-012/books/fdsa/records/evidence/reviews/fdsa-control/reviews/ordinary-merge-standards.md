# XM01 ordinary merge — independent Standards review

Reviewed: 4 November 2026  
Reviewer: independent Standards agent `/root/foundation_continuation`  
Source assessment: **Complete; zero concrete unresolved Standards findings**  
Overall outcome: **Blocked pending complete integrated candidate validation**

This report continues the existing XM01 scope and finding record in
[ordinary-merge-round1.md](ordinary-merge-round1.md). It is an independent full
source assessment of the candidate identified below. It does not reuse the
author/root assessments as an independent approval, replace the separate Spec
axis, approve an incorporated future candidate, or close any book obligation.
The foundation review remains a separate retained task.

## 1. Exact scope and evidence identity

| Item | Identity |
| --- | --- |
| Fixed accepted base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Immutable candidate | `72a0951aee406f7db67998d2a3bf8810f4e1bccc` |
| Merge base | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Checkout / branch | `conaled-ordinary-merge` / `work/fdsa-ordinary-merge` |
| Full diff | `git diff 07e480f6ec9958d4975bb90151005b84f2907614...72a0951aee406f7db67998d2a3bf8810f4e1bccc` |
| Frozen requirements | `reviews/ordinary-merge-requirements.md`, 19,999 bytes, SHA-256 `b54e2b332cc31c04ac12fb5b19cc96fa494a80e1455fcfc173f59b6fe340d3d9` |
| Recorded scope identity | `reviews/ordinary-merge-round1-identity.json` |
| Exclusions | None |

I independently resolved the three Git identities, inspected the actual full
six-path diff, and read every new/changed source body using the pinned candidate
or its clean immutable checkout. Each file's actual candidate bytes match the
round identity record. The exact current diff has 1,002 insertions and no
deletions; the historical original draft had 995 insertions. The seven added
lines since that draft are the recorded proof corrections.

| Candidate path | Bytes | SHA-256 |
| --- | ---: | --- |
| `Applications/Resources/ListMerge.lean` | 8,629 | `df38ab6fd95baca45be4c5f7e6cd86f4e168fbff0ab21899783c8b52a41d1975` |
| `Applications/Sorting/Merge.lean` | 7,840 | `951db5238af4e2acd9a987318f04023de6d039156094f50a6ce775a4c6a7aac7` |
| `Examples/MergeCosts.lean` | 23,410 | `ae3e60b22c4b03cd78d33f5fe44729b83bb26ab589e014a9039927319d4f1466` |
| `SquareApplications.lean` | 8,319 | `ef3d3bbac7d252aa6c2575f619001176347f083f452802148c968c6e37ccca41` |
| `docs/research/fdsa-list-merge.md` | 14,955 | `25f1982d56183111c112d3e38f4473000668685d126677935dcecc3d1a5cf5b3` |
| `docs/research/fdsa-reconstruction-map.md` | 17,800 | `f59022d0709bbb48bdf976021c3c0bbf29861af3eddab377e9ef9fb491c948ff` |

The complete commit scope is:

- `5f409e71bb068e3b8cc133226046ce8bbe29d982` — ordinary merge observations.
- `57a7d338dedb53a5526bbbc05f7be5fd83443d03` — resource proof normalization.
- `72a0951aee406f7db67998d2a3bf8810f4e1bccc` — connected example elaboration.

All commit subjects follow the repository's Conventional Commit form with
the applicable `#174` reference. I read all frozen requirements, all three
complete original source/API/case preflights, the original source statement
assessments, original candidate and preservation records, author release,
the current round record, both correction records and patches, and the
actual focused/type-inspection evidence. Historical status assertions remain
historical; the current terminal records determine the validation status.

## 2. Applicable standards and architectural assessment

The governing guidance is the candidate's `AGENTS.md`, README development and
build/audit policy, architectural-quality and domain guidance, `GLOSSARY.md`,
ADR index and ADRs 0001/0010, `docs/language-direction.md`, the shared review
procedure, `code-review` instructions and heuristics, and the
`example-driven-development` statement-review guidance and worked example.
The standards relevant to the review are unchanged from the fixed base.
No additional root coding-standard/contribution file or applicable nested
`AGENTS.md` was found for these paths.

The user's Nix waiver applies. It does not waive exact Lean/Lake/dependency
pins, proof restrictions, immutable candidate checks, the complete audit, either
independent review axis, or immediate candidate verification.

The extension fits the existing module architecture:

- The value layer adds four facts to the existing merge library. A byte
  comparison confirms that its entire prior content and final namespace
  closure remain intact around the insertion. Existing definitions,
  hypotheses, theorem statements, and proofs are preserved.
- The resource core imports only the existing source-merge bridge and call
  model. It uses ordinary lists, `Measured`, `bind`, and `reweight`, and adds
  one execution with two Nat observations. It creates no alternative pure
  merge hierarchy, new carrier, general tariff framework, or translator.
- Queue, cost-comparison, stability, and sequential-composition consumers
  belong in `Examples.MergeCosts`, where they use independently established
  domain APIs. The resource library does not import the queue or growth
  machinery for an unused capability.
- Removing the single new `Examples.MergeCosts` import exactly recovers the
  old public root. The entire original reconstruction map remains a bytewise
  prefix of the new one. No new audit root or build policy is introduced.

I independently compared all sixteen baseline source/tooling paths recorded
in `ordinary-merge-source-identities.json` between base and candidate; every
one is unchanged. The full diff also confirms no other source/configuration
path changed. This includes the existing measurement/call APIs, source bridge,
stable contracts, queue, compiler/dependency pins, and checker/guard files.
There is no source dependency on an unaccepted shared draft.

The heuristic review found no concrete maintenance or interface defect.
Recurring induction cases follow distinct proof obligations; they do not
justify a larger executor framework. The small wrappers in the examples
expose actual specializations and composition laws. Explicit comparator and
input-local agreement arguments preserve useful generality without requiring
payload order, equality, or unrelated categorical structure. No shared
interpretation interface or preservation family is changed, and no upstream
Felix parity claim is made by this unit.

## 3. Value-layer statement review

`sublist_merge_left` and `sublist_merge_right` retain each operand's ordered
occurrences for every Boolean comparator. Their recursive proofs follow the
actual selected head, use the current `Sublist.cons_cons`/`Sublist.cons`
constructors, and decrease the sum of input lengths. The empty cases include
two empty lists. They do not infer sublist order from permutation or support.

`pairwise_of_merge` quantifies over an arbitrary relation independent of the
comparator and consumes both public sublist laws through the existing
`List.Pairwise.sublist`. The actual elaborated type has no comparator law,
relation decision, transitivity, payload order/equality, or inhabitant premise.

`merge_sorted_compatible_on_iff` combines that converse with the unchanged
forward theorem. It requires `[LE κ] [Std.IsPreorder κ]` and only the stated
two branch implications on members of the actual cross-input lists. It does
not replace that local premise with a global comparator law or linear order.
The forward direction has the required sorted blocks; the reverse direction
uses the weaker arbitrary-relation public result. The payload and key
universes remain independent.

The general source/key clients instantiate this iff with the actual decidable
key comparator and its existing total-preorder law. Source erasure uses
`sourceMerge_eq_merge` and the pulled-back-key `mergeBy_source`, rather than a
second source operation. `source_value`, `key_value`, and `key_source_value`
require only the comparison capabilities of those operations. Sorting and
stable-filter assumptions appear only where the corresponding semantic
properties are claimed.

## 4. Actual measured execution and mathematical observations

`Resources.ListMerge.run` has one recursion. Its empty-side results are the
remaining list with observation `(0,1)`. In a nonempty branch, the actual
`cmp x y` determines which single smaller call is used; `Resources.bind`
passes that call's returned list to the output cons and adds `(1,1)`.
Termination uses the sum of input lengths. There is no independently selected
pure output paired with a counter, no second recursive scalar executor, and
no charge for the unselected branch.

The existing `Measured` and `bind` definitions were read directly: the body is
evaluated at `r.1`, and its actual result supplies both output and the second
summand of the observation. The new execution therefore has the connection
required by its claimed cost model, rather than merely a chosen pair type.

The following complete public families match their intended contracts:

| Public family | Reviewed meaning and assumptions |
| --- | --- |
| `run_nil_left`, `run_nil_right`, `run_cons_cons` | Whole returned-value/observation equations of this execution, including one invocation for `[]/[]`. |
| `run_value` | Erasure to pinned `List.merge` for arbitrary comparator and lists; both recursion branches retain the actual child erasure. |
| `comparisons_nil_left/right`, `comparisons_cons_cons` | Zero bases and one plus the selected child's comparison count; the source's handwritten comparison convention. |
| `entries_nil_left/right`, `entries_cons_cons` | One at a base and one plus the selected child's invocation count. |
| `run_entries_cons_cons` | Reweighting by `Prod.snd` gives the existing `CallCount.tick` around the actual selected projected child and an uncharged cons. |
| `entries_eq_comparisons_add_one` | Exactly one terminal invocation per merge. |
| `comparisons_le`, `entries_le` | Loose bounds by the input-length sum and that sum plus one. |
| `comparisons_cons_pos` | Both inputs nonempty force at least one comparison. |

`comparisons` and `entries` are transparent coordinates of `run`, not separate
recurrences. None of these raw contracts assumes sortedness, comparator laws,
payload order/equality/decidability, distinctness, an inhabitant, or a finite
carrier. The bound includes unsorted and constant-comparator inputs. It is not
advertised as a tight worst-case formula.

The measured recurrence charges Nat observations after the child while the
scalar equations display `1 + child`; the proofs use Nat addition to identify
these values. This does not assert an event-order trace. The documentation
correctly limits comparisons to calls of the supplied comparator, and entries
to this logical merge's invocations. It excludes comparator/key evaluation
work, unrelated helpers, cons allocation, length computation, external
preparation, and a traversal charge on the returned suffix.

### Exact map transport

`run_map` has independent `α : Type u` and `β : Type v`. Its input-local
premise compares only `a ∈ xs` and `b ∈ ys`; recursive tails inherit that
premise by membership. The proof establishes agreement of the actual branch
decisions and transports the entire measured pair. The conclusion maps the
actual output and preserves both coordinates unchanged.

The theorem requires neither injectivity nor payload equality, ordering,
inhabitance, or equal universes. Its premise is a justified comparator
agreement condition, not an assumed output/cost conclusion. The pinned
`List.map_merge` value law alone is not used to infer counts. The tagged
consumer applies this theorem to `Prod.fst` for both operand orders and
extracts the count equality from the resulting whole-pair equality. The
documentation also distinguishes this execution correspondence from the work
of performing a caller's maps.

## 5. Complete connected-client assessment

I compared every frozen required family with the actual definitions,
statements, and derivations. Numerical expectations remain those recorded
before authoring; the correction patches change no expected value or cost.
The cases consume public definitions/laws, and the important assumptions are
proved for the chosen inputs. Reduction at the end of a connected calculation
is appropriate here; the cases are not isolated arithmetic assertions.

| Family and named clients | Connection and independently retained expectation |
| --- | --- |
| `result_perm`, `result_length`, `result_multiset`, `result_mem` | Actual `run_value` followed by existing merge permutation, length, membership, and permutation-to-multiset laws. There is no parallel resource value theory or payload equality premise. |
| `empty_sides`, `empty_payload` | Public base equations cover arbitrary suffixes; arbitrary lists over `Empty` reduce to `([], (0,1))` without an inhabitant. |
| `low_singleton`, `high_singleton`, `low_singleton_entry_model` | `[0]` with `[1,2]` gives `(1,2)` and `[2]` with `[0,1]` gives `(2,3)`, both returning `[0,1,2]`. The scalar client directly consumes `run_entries_cons_cons` and the existing tick. |
| `interleaving`, `interleaving_observations` | `[0,2,2]` with `[1,2,3]` returns `[0,1,2,2,2,3]` with `(4,5)`. General erasure laws supply length, multiset and support, and the actual result retains three copies of 2. |
| `always_true`, `always_false` | Arbitrary `a,b,c : α` give `[a,b,c]` with `(2,3)` or `[c,a,b]` with `(1,2)`. No distinctness, order, or payload equality is introduced. |
| `tied_runs`, `ties_do_not_determine_cost` | The two operand orders return the same `[1,1,1]`, with equal length/permutation but unequal comparison and entry coordinates `(2,3)` versus `(1,2)`. |
| `unsorted_run`, `unsorted_cost_bounds`, `unsorted_inputs_retained`, `unsorted_for_every_comparator` | The actual `≤` run returns `[2,1,3,1]` with `(2,3)`. The raw bounds apply, both sublists are consumed, and the arbitrary-relation converse proves failure of natural-order sortedness for every comparator. |
| `source_value`, `key_value`, `key_source_value`, `key_sorted_iff`, `source_key_sorted_iff` | Actual erasure composes with existing source/key adapters and the new generic iff. No global record order is assumed; local pulled-back instances are explicit. |
| `measured_key_spec`, `records_value`, `records_counts`, `records_exact` | Actual sorted-block proofs feed existing `mergeBy_spec`; uniqueness reuses `Examples.StableSorting.expected_spec`. The signed-record output is the existing expected list, with recurrence-derived `(2,3)`. Key antisymmetry is used by existing uniqueness at concrete `Int`, not imposed on arbitrary raw payloads. |
| `tagged_key_transport`, `tagged_counts`, `tagged_values`, `tagged_exact`, `tagged_stable` | Arbitrary payloads with all keys one retain full left-before-right records. Both operand orders use actual noninjective key transport and retain `(2,3)` / `(1,2)`. StableSort uses the existing contract with the actual sorted blocks. |
| `false_compare_compatible`, `false_record_run`, `compatible_not_stable` | The always-false comparator is locally compatible on equal keys. Output sortedness and permutation hold, while the actual distinct-tag stable-filter contract fails. Compatibility is not silently strengthened to left-tie stability. |
| `unsorted_records_run`, `unsorted_record_filters` | The actual keyed run returns right records followed by left records with `(2,3)`. Key-1 filter `[D,B]` differs from concatenation's `[B,D]`, retaining the substantive sorted-block premise. |
| `twoStage` and its public value/observation/bound/projection clients | Existing `bind` feeds the actual first output into the second merge. Both additive coordinate homomorphisms consume `reweight_bind`; exact totals and input-length bounds are derived from actual executions. |
| `first_stage`, `second_stage`, `twoStage_example`, `substituted_input_example`, `actual_input_matters` | Correct sequencing returns `([0,1,2], (3,5))`; substituting the original concatenation returns `([1,2,0], (2,4))`. The final discriminator proves inequality of both value and observations. |
| `queueBody`, `queueBody_value`, `queueBody_observation`, `queueBody_bounds`, `raw_queue_body`, `raw_queue_erasure_and_order` | The actual raw queue node body uses already obtained child enumerations, one measured priority merge, and uncharged cons. Its rank-99 fixture returns priorities `[9,1,2]`, merge-only `(1,2)`, and a checked unsorted result. |
| `nonempty_tariffs`, `empty_tariff_not_multiplicative`, `low_singleton_attains_factor_two` | Actual positivity and the exact single-merge relation feed the existing C1 inequalities. Empty-side `(0,1)` refutes every Nat multiplicative coefficient, while the low singleton attains `E=2*C`. |

### Composition and observation boundaries

The two-stage general observation uses `CallCount.let_rule` with the actual
first returned list in the second call. `twoStage_entries` proves total
entries equal total comparisons plus **two**. The generic comparison bound
is `2 * (xs.length + ys.length) + zs.length`; the entry bound adds two.
The proof uses the first result's actual length via `result_length`, not an
assumption that the intermediate list equals concatenation. The affine
single-merge shift by one is not treated as an additive homomorphism, and no
extra enclosing entry is charged.

The queue's existing raw constructors, `size`, `entries`, `mergeOn`, `toListQ`,
`toListQ_perm`, `entries_length`, and heap-dependent `toListQ_sorted` were read
directly. `queueBody_value` applies to every raw rank and both raw subtrees
under only priority `LE`/`DecidableLE`. The body observation is exactly that
one merge's observation; the root cons is `pure`. The bounds use unconditional
permutation/length facts to obtain `size l + size r` and that sum plus one.
No `Heap` or `Ranked` premise is added to the raw value/cost laws, and no
heap-dependent sortedness theorem is used for the malformed raw fixture.

No client claims that child traversals, the enclosing enumeration entry, or
the whole queue are measured by this local body. The full tree/carrier bridge
and quadratic theorem remain downstream. Likewise, the actual zero-cost
comparison case prevents promoting the nonempty tariff inequality to a
uniform multiplicative claim over all inputs.

## 6. Source, license, and retained book scope

I independently rehashed the recovered primary PDF: 1,742,029 bytes, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
I read its printed pages 17–18 and 180–181 directly through PDF text extraction.
The source equations prescribe left-tie ordinary merge, its occurrence/support
and length laws, sortedness iff, and the handwritten comparison recurrence
with zero bases. The entry convention is separately declared by this work.
Exercises 14.1 and 14.3 leave implementation choices open; the note correctly
describes the chosen queue/list components without claiming completion.

The source note retains the exact PDF version/hash and pinned Isabelle
`Sorting.thy` revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, hash
`dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.
The complete preserved source preflight supplies the companion comparison,
locations, and additional source identities. The note explicitly discloses
that the companion revision postdates the manuscript and is not its generation
identity. It gives the limited `Heaps.thy` provenance without claiming that
source supplies the chosen exercise implementations.

I read the actual pinned Lean `List.merge` definition, relevant equations,
length/membership/permutation laws, and `Pairwise.sublist`, plus the pinned
Mathlib definitions generating additive coordinate homomorphisms. Lean's
source identifies its verification-oriented merge and runtime replacement,
with Lean FRO/Apache 2.0 attribution. The candidate correctly does not transfer
its declared observations to compiled calls, allocation, stack usage, or time
merely from a value equality.

The complete Isabelle notice was checked against the preserved pre-correction
note, not just its title. The extracted original notice is 1,673 bytes with
the exact recorded SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
The candidate notice equals that original after removing only trailing
line-ending spaces; precisely fifteen lines differ this way. Attribution,
all three conditions, and the full disclaimer remain present. The normalization
is disclosed, and the original bytes remain preserved. This review does not
copy manuscript content into the deliverable.

The note and map restrict direct support to C02-025, the merge portion of
C02-027, and C02-028/029/031/033/035/037. They retain all 112 current Chapter 2
obligations, including C02-108–112 and the historical 107-row requirements.
Floor-left sorting, actual sorted-child cost composition, whole-sort stability,
power-of-two/all-length/real-log bounds, bottom-up/natural work, scanner/builders,
and exercises remain mandatory. Standard ceil-left sort value equality is not
used for source-cost transfer. Complete Chapter 14 ADT/direct costs and full
enumeration remain open. Binomial link/carry is explicitly a different
operation and tariff. No later potential-accounting prefix or unrelated shared
draft is incorporated into this scope.

The source note's draft/pending-validation language does not supply a success
claim. The later actual focused results are recorded separately below; full
integrated compilation, audit, and final review acceptance remain pending.

## 7. Actual validation evidence and its limits

I inspected the full closed logs, actual terminal records, and retained native
command records. For every row below, the actual log byte count and SHA-256
match its terminal recorder result. The four focused/type-inspection runs
also retain native command records: their exits agree with the recorder, and
none reports a timeout or recorder error. Final HEADs match the corresponding
candidates, and final tracked/nonignored status is clean.

| Evidence under `provenance/` | Candidate | Actual exit | Recorder elapsed | Closed full log: bytes / SHA-256 |
| --- | --- | ---: | ---: | --- |
| `ordinary-merge-private-doctor-20261104/` | `5f409e7…` | 0 | 2.076 s | 4,494 / `847b2f74f1d976cc435e182f92c68f9cf3d7cabdd7ac3ecf840b26634ee03ded` |
| `ordinary-merge-focused-20261104-attempt1/` | `5f409e7…` | 1 | 114.332 s | 8,829 / `fbdf8e09e604feec3a921aa124e376dceb5a8ba1ff16439b76c0d6c5c44daa0f` |
| `ordinary-merge-focused-20261104-attempt2/` | `57a7d33…` | 1 | 65.746 s | 8,515 / `63d5e45b2f66e38bb40110abe8de1ad6fbeaf2ca0d256ef7c40dbbcc540e70cd` |
| `ordinary-merge-focused-20261104-attempt3/` | `72a0951…` | 0 | 31.376 s | 2,325 / `2898f1aef4e952cffdcc64fc4ac449bea3d105dc90f02f2706b8d97772c5f5a1` |
| `ordinary-merge-type-inspection-20261104/` | `72a0951…` | 0 | 28.112 s | 9,351 / `4645276a14c159ab587b16acb8d11e8db95615c9a41c8fff69384c4b42f85910` |

The successful focused command, through the supplied qualified native kit with
one Lean thread, is:

```text
lake build Applications.Sorting.Merge Applications.Resources.ListMerge Examples.MergeCosts
```

Attempt 1 failed in the resource proof scripts. Attempt 2 built the resource
library and failed in connected example elaboration. Attempt 3 passed all
requested targets. Its 1,586 Lake jobs include dependencies; that number is not
a complete project-module count or exhaustive audit result. None of these
focused commands produced a candidate verification record.

The private doctor record confirms the compatibility profile, exact dependency
revisions, and the specified official executable/link-input and extra-runtime
checks. It explicitly does not claim a whole-distribution attestation. The
recovered official Lean/Lake 4.35.0 profile and narrow adapter remain disclosed;
Mathlib remains pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`, and all
nine manifest revisions are retained. There was no pin or execution-profile
change in the source correction commits.

The 17-declaration type inspection used `pp.universes true` and explicit
`@` declarations. I read its complete output. It confirms the raw sublist
and arbitrary-relation domains, the local keyed iff, universe-independent
whole-pair map transport, count relation/bounds, actual entry projection,
source/key adapters, tagged transport and values, value-dependent two-stage
observation/discriminator, and raw queue observation. It introduces no hidden
payload order/equality/inhabitance premise. This is necessary statement-review
evidence, not a substitute for the full proof audit.

### Warning assessment

The successful focused log retains eight nonfatal import-module advisories:
one in unchanged `Sorting.Stable`, two in unchanged `Resources.Measured`,
two in unchanged `Resources.Growth`, two in unchanged `Resources.CallComparison`,
and one for the new `Examples.MergeCosts` import of
`Mathlib.Data.Multiset.AddSub`. The last is a new-file advisory and is not
misclassified as baseline. The actual advice concerns adoption of Lean's
module system; it is not an unproved claim or a disabled source linter.

Both new Lean files retain `autoImplicit false` and `warningAsError true`.
No linter option, build check, proof guard, or warning policy was relaxed.
The earlier unused-simp/local-instance diagnostics were corrected in the
proof scripts rather than suppressed. I find no concrete remaining Standards
violation in the visible import advisories. The full integrated log still
requires its own warning review when available.

Source inspection found no admission, new source axiom, user-written unsafe or
partial declaration, `native_decide`, or skipped kernel checking. This is a
source assessment only: the required exhaustive transitive audit over every
project declaration has not yet been supplied for XM01.

## 8. Preserved finding dispositions

| Stable ID | Disposition and reviewed evidence |
| --- | --- |
| `XM01-DOC01` | **Fixed with source review evidence.** The final note identifies the printed comparison bound separately from the derived invocation bound. The original wording is preserved in `ordinary-merge-note-before-doc-corrections.md`. No mathematical bound changed. |
| `XM01-DOC02` | **Fixed with source review evidence.** The appended map explicitly identifies first/second cost coordinates as `run.2.1` / `run.2.2`; it does not identify `run.1` with comparisons. The original appended section is preserved. |
| `XM01-DOC03` | **Resolved by the disclosed bounded normalization.** The complete raw notice hash matches the recorded source notice, and normalized candidate bytes differ only in the fifteen trailing-space lines. Attribution, conditions, and disclaimer are retained. |
| `XM01-ELAB-001` | **Source correction and focused confirmation verified; whole-candidate confirmation pending.** `57a7d33…` removes redundant simp arguments and normalizes map-cons induction hypotheses. Actual definitions, theorem types, premises, and observations are unchanged. Resource compilation succeeds in attempts 2 and 3. |
| `XM01-ELAB-002` | **Source correction and focused/type confirmation verified; whole-candidate confirmation pending.** `72a0951…` repairs proof-local instance syntax, explicit map inputs, recurrence simplification, literal closing steps, and projection inference. Frozen expected values and public statements are unchanged; attempt 3 and all 17 inspected types pass. |

The earlier `XM01-PRE-DOC01` status/punctuation correction is also retained in
its original and corrected preflight records. It changes no mathematics or
numerical expectation. The author-release record ties source release to the
successful checkpoint 0052 receipt and exact frozen requirement hash.

There are **zero new concrete Standards findings** and no unresolved source
finding after this assessment. The lack of full integrated validation is an
explicit acceptance blocker, not a reason to rename or discard the existing
finding history. No source correction is requested by this report.

## 9. Required continuation before acceptance

The exact first shared-foundation candidate has its own pending full gate and
must pass before XM01 integration. This source review does not substitute for
that work or change its original prefix `c80eec92f5458eccfd1c34c8314d666c2a1e3847`.

When root incorporates the exact accepted foundation tip, record the new
integration base/candidate, ancestry, and all resolutions. Preserve this
original base and full frozen XM01 scope. Both independent axes must assess
the resulting full candidate, carrying this assessment and the stable IDs
forward. Review reuse applies only to matching inputs and unaffected content;
an approval of this source snapshot would not approve an unseen integration.

The remaining applicable gates are:

1. The clean immutable final candidate and stable source/dependency/configuration
   inputs, with no shared writable project outputs across active builders.
2. Qualified full `./check.sh --candidate HEAD`, using fresh mode only if the
   actual README/runbook triggers apply. Preserve actual exit and complete
   closed log, including both integrity phases, source/public coverage,
   compiler/dependency identity checks, and the full integrated build.
3. The exhaustive audit on that candidate, with only `propext`,
   `Classical.choice`, and `Quot.sound` permitted, and a matching newly written
   `.lake/verification.json`. An earlier chapter's record is not XM01 evidence.
4. Terminal reconciliation by both independent Standards and Spec axes, with
   full warning/evidence assessment and no unresolved findings.
5. Qualified immediate `./check.sh --verify-candidate HEAD` just before the
   exact approved local acceptance, followed by accurate ticket/coverage
   updates and the required uploaded acceptance checkpoint.

I ran no Lean/Lake build, project checker, proof audit, or dependency/output
mutation during this review, and made no candidate/source/ref change. The
only new artifact is this report. No GitHub mutation or push was performed.

**Final Standards result:** full source assessment complete; zero concrete
unresolved source findings; worst unresolved source issue: none. Base
`07e480f6ec9958d4975bb90151005b84f2907614`, candidate
`72a0951aee406f7db67998d2a3bf8810f4e1bccc`. **Overall: Blocked pending complete
integrated candidate validation.**
