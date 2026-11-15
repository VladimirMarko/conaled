# Uniform-input mean: first compiler repair and full author readback

## Exact scope and actual validation state

The author source branch began clean at
`9d5dcd2cfbd6fc5df572234a85bf4957d0c32a21`, descending from the prepared
`204dba90967f11a2dfe186316bc85a29acbcc576` prefix. Before editing, both original
Uniform files were compared with the immutable central compiler candidate
`f673ee87195e4aaeef4b41767a7468c70ad6214f`: both matched byte for byte. Complete
before copies and the original 125-declaration inventory are retained here.

The central sixteen-target command (focused attempt6) actually closed with
exit **1**, elapsed **1157.3180223529998 seconds**, clean unchanged central HEAD.
Its complete full log is **48,390 bytes**, SHA-256
`4d18122cfbe8698979673c10b4bdf76b0fb7442d48f75882b95d89c6bae1aa95`.
The actual native result also records exit1, no timeout and no recorder error.
The complete Uniform diagnostic extraction contains **24 error headers in
192 lines**; all were read, retained in `diagnostics.txt`, and accounted for below.
Other targets' failures remain outside this author's assigned scope.

Only `Applications/Resources/UniformQuickSortMean.lean` is edited. The example
file remains byte-identical. No Lean/Lake/compiler/build/cache command was run.
This is a source repair ready for root's immutable compiler loop, **not a
successful successor build, inspected elaborated-type result, or acceptance**.
Independent review, the complete candidate check/audit, and immediate candidate
verification remain outstanding. The separate foundation Standards terminal
continuation remains held; this author repair does not touch or review F.

The existing implementation/review loop and complete approved five-stage plan
remain in force. I reread the complete original and corrected core, all 352
example lines, the complete original 125-row assessment, and every actual
Uniform diagnostic. Applicable AGENTS, implement/review instructions, and
example-driven statement/case guidance were retained. Exact pinned sources for
`ae_cond_of_forall_mem`, `Fin.sum_univ_eq_sum_range` (the additive theorem from
the recorded product theorem), and `Finset.sum_range_reflect` were inspected
read-only to make the applications explicit. No new framework, model, helper
axiom, or alternative execution was introduced.

## Source changes and preserved mathematics

Nine theorem proof bodies are adjusted. Twelve scoped `omit ... in` commands
remove unused measure/order/equality section assumptions. One written
proposition, `firstEvents_disjoint`, replaces the previously unelaborated `on`
notation with its intended explicit binary disjoint-event lambda. All other
explicit declaration headers are textually unchanged. All definitions and
named local instances, every example byte, the declaration names/order, and
all **125 intended declarations** are retained: **68 core** and **57 example**
declarations. This inventory is not a count of generated/kernel declarations.

The arithmetic changes expose the same existing natural counters before Real
casts; they do not change the counter or tariff. Explicit rewrite arguments
select the same finite rank and reflected prefix-sum identities. The corrected
zero branch derives `T.card = 0` from `hcard.trans hn`, preserving the fixed
environment and inherited key injectivity in the actual subset induction.
The occurrence bridge exposes its existing mapped list and actual execution
transport; no map/index evaluation cost is charged. The literal bounds still
compare two distinct observations on the same sample.

The conditional equation still comes from `observedCost_on_first`, derived
from the actual source cons equation and actual filters of the same tail.
The original and conditioned integrability declarations remain intact. The
conditional proof names the original `uniformOn univ` measure explicitly;
its positive finite head event, both actual child marginal laws, and original
head partition remain intact. No independence or assumed execution recurrence
is inserted. The downstream compiler-recovery admission diagnostic is retained
as an actual failure: it is addressed by repairing those antecedent proofs and
must be absent in the next real build. There is no source admission or gate
suppression.

## All signature and section-assumption changes

This is **not an assertion of equivalence with old elaborated types**. The old
complete core did not compile. The following explicit omissions intentionally
remove irrelevant automatically included instances and preserve the intended
minimal-domain contracts. Actual successor types still require compiler
inspection. The nine direct unused-section diagnostics are supplemented only
by the directly affected pure all-false/event prerequisites whose earlier
proof/header failures masked the same unnecessary measure scope.

| Declaration | Removed section assumption(s) | Mathematical reason and retained premises |
| --- | --- | --- |
| `meanBy_empty` | `MeasurableSingletonClass (Equiv.Perm I)` | The actual constant integral needs the ambient measurable space and complete finite environment, not singleton measurability. Nil cost remains1. |
| `meanBy_singleton` | `MeasurableSingletonClass (Equiv.Perm I)` | The selected singleton order and its constant mean5 retain nodup/complete positions and the arbitrary comparator. |
| `observedCost_of_all_false` | Both measure instances on `Equiv.Perm I` | This pointwise actual execution identity is pure. Nodup/complete positions and the all-false premise are retained. |
| `meanBy_of_all_false` | `MeasurableSingletonClass (Equiv.Perm I)` | Integrating the same pointwise constant polynomial retains its actual measurable space and complete environment. Removing the irrelevant measure arguments from its pure prerequisite must not retain them here. |
| `firstEvents_disjoint` | Both measure instances on `Equiv.Perm I` | Distinct optional heads imply disjoint sets before any measure is chosen. Its pairwise relation is now written explicitly; selected set and positions are unchanged. |
| `firstEvents_cover` | Both measure instances on `Equiv.Perm I` | The union equals the whole sample set from actual selected length, completeness, nodup positions and nonempty S. |
| `injOn_leftChild` | `LinearOrder κ` | Local key injection restricts along the actual left support inclusion for arbitrary key type and Boolean comparator. |
| `injOn_rightChild` | `LinearOrder κ` | The same pure restriction applies to the actual false-outcome child. |
| `restrictedOrder_keys_nodup` | `LinearOrder κ` | Nodup labels and local key injectivity preserve nodup mapped keys without ordering them. |
| `rankEquiv_key` | `DecidableEq I` | The existing finite key-image order equivalence already yields this key equality; its key order and local injection remain. |
| `occurrence_key_injective` | `LinearOrder κ` | Nodup mapped input keys imply injective key lookup on occurrence indices without a key order or payload equality instance. |
| `occurrenceInput_keys_nodup` | `LinearOrder κ` | The same full sampled occurrence permutation preserves nodup mapped keys. |

All key-order assumptions needed for the strict source comparator, rank, and
closed-form mean remain. Label, payload, and key universes remain independent.
No label order/default or payload equality/measurability/finite/default
assumption is added. No membership, nonemptiness, local injectivity, distinct-key,
subset, length, or scalar-bound threshold premise is removed from a claim that
uses it.

## Every actual compiler diagnostic

Each row is a source correction awaiting real compilation; none is silently
marked as a passing check. The full original diagnostic text, including every
context and goal, remains in `diagnostics.txt` and its exact root log.

| Finding | Declaration / actual problem | Source repair |
| --- | --- | --- |
| `U-ELAB-001` | `meanBy_empty`: Unused measurable-singleton section assumption. | Scope out MeasurableSingletonClass; the finite original constant integral still has its measurable-space parameter. |
| `U-ELAB-002` | `meanBy_singleton`: Unused measurable-singleton section assumption. | Scope out MeasurableSingletonClass; the actual singleton order and cost remain unchanged. |
| `U-ELAB-003` | `observedCost_of_all_false`: Cast tactic did not unfold the observedCost wrapper. | Unfold observedCost before the exact natural-to-real cast; also scope this pure pointwise theorem outside both measure instances. |
| `U-ELAB-004` | `conditional_mean`: ae_cond_of_forall_mem could not infer the original measure. | Pass the actual uniformOn univ measure explicitly, preserving the very same conditioning event. |
| `U-ELAB-005` | `conditional_mean`: The untyped heq have declaration failed after the missing measure. | The explicit original measure gives that same almost-everywhere source equality a determinate type. |
| `U-ELAB-006` | `conditional_mean`: The conditional integral goal remained unsolved after heq inference failed. | Retain the full integral-add/integrability/child-marginal proof after the corrected heq; do not replace the equation with an assumption. |
| `U-ELAB-007` | `firstEvents_disjoint`: Unknown on identifier in the source proposition. | Write the intended pairwise disjoint-event relation explicitly; remove its unrelated measure section instances. |
| `U-ELAB-008` | `firstEvents_cover`: Both measure section assumptions were unused. | Scope out both instances; the actual nonempty head-cover proof is purely a list/set statement. |
| `U-ELAB-009` | `meanBy_recurrence`: Compiler recovery produced a downstream declaration-uses-sorry diagnostic. | Repair conditional_mean and firstEvents_disjoint above; preserve the actual recurrence proof. This diagnostic must disappear in the next real compilation; no admission is inserted. |
| `U-ELAB-010` | `injOn_leftChild`: Unused key LinearOrder section assumption. | Scope out LinearOrder; restricting local key injectivity uses only actual child support. |
| `U-ELAB-011` | `injOn_rightChild`: Unused key LinearOrder section assumption. | Scope out LinearOrder; preserve the complementary source child and inherited injection. |
| `U-ELAB-012` | `restrictedOrder_keys_nodup`: Unused key LinearOrder section assumption. | Scope out LinearOrder; nodup mapped keys depends on nodup source labels and local injection only. |
| `U-ELAB-013` | `rankEquiv_key`: Unused DecidableEq I section assumption. | Scope out DecidableEq I while retaining the ordered finite key image and the same rank equivalence. |
| `U-ELAB-014` | `leftChild_key_image`: Bare rankEquiv_key rewrites left the rewrite pattern as a metavariable. | Supply key, S, hinj and each actual rank explicitly; the interval/image claim is unchanged. |
| `U-ELAB-015` | `sum_child_cards`: The second Fin-to-range rewrite could not match the reflected function. | Instantiate the first function f and the second function j ↦ f (S.card - 1 - j), then apply the same reflected-range identity. |
| `U-ELAB-016` | `meanBy_eq_closedForm`: subst n selected hcard and removed the name subsequently referenced. | Derive T = empty directly from hcard.trans hn without substituting n ambiguously. |
| `U-ELAB-017` | `meanBy_eq_closedForm`: closedForm_zero did not match an unreduced empty-set-card argument. | Rewrite T = empty, the actual empty mean, and hn : n = 0 explicitly before the numerical zero theorem. |
| `U-ELAB-018` | `occurrenceInput_perm`: The target occurrenceInput wrapper was not simplified to the mapped permutation. | Use change to expose its exact defining mapped list, then retain the original permutation and ofFn_get connection. |
| `U-ELAB-019` | `inputMeanBy_eq_meanBy`: The pointwise cost transport rewrite was hidden by lambda applications. | Beta-reduce with dsimp only, then use occurrenceInput_cost lt xs π explicitly. |
| `U-ELAB-020` | `occurrence_key_injective`: Unused key LinearOrder section assumption. | Scope out LinearOrder; actual occurrence lookup injectivity follows from nodup mapped keys. |
| `U-ELAB-021` | `occurrenceInput_keys_nodup`: Unused key LinearOrder section assumption. | Scope out LinearOrder; full sampled permutation preserves nodup mapped keys. |
| `U-ELAB-022` | `inputMean_eq_closedForm`: Finset.univ was supplied directly with an expected Set type. | Annotate Finset.univ as the finite set of occurrence labels, then explicitly coerce it to the corresponding Set. |
| `U-ELAB-023` | `inputLiteralMean_bounds`: The first real inequality cast was hidden by lambda applications. | Beta-reduce the actual pointwise integrands before casting exerciseCost_le_literalCost. |
| `U-ELAB-024` | `inputLiteralMean_bounds`: The upper real inequality cast was hidden by lambda applications. | Beta-reduce the same pointwise integrands before casting literalCost_le_twice; retain both actual cost metrics. |

## Full 125-declaration author readback

The complete actual source was read. The rows below retain each intended claim
and its connected cases, with the exact correction disposition. All rows have
no new mathematical statement/case finding after the disclosed repairs; they
remain **source assessments pending successful elaboration and actual type
inspection**. Unchanged rows retain their prior complete statement analysis,
not an inferred compiler pass. `source-inventory.json` preserves every complete
old/new source header, exact locations, omitted scope, and original case account.

### Applications/Resources/UniformQuickSortMean.lean

783 lines; 37880 bytes; SHA-256 `135066a5f434ddd99981212a739b165ccdacadbff1448e5f7c358ff04e33883f`.

| Declaration | Intended claim and retained connection | Correction/readback |
| --- | --- | --- |
| `leftChild` | Definition, arbitrary Boolean comparator and finite selected set; erases the exposed occurrence before retaining true outcomes. The low/middle/high child tables test empty, singleton and pair supports. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `rightChild` | Definition with the actual false outcome, not a strict-greater replacement; equal keys remain eligible for the right child. Equal-key quadratic family and all three child tables. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `mem_leftChild` | Exact membership iff: a different selected label whose Boolean comparison with the pivot is true. No order or distinct-key hypothesis. Used by disjointness, inherited injectivity and the key-image rank proof. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `mem_rightChild` | Exact membership iff for the complementary false comparison. Pivot exclusion is independent of the comparator. Used by complement/cardinality proofs; equal keys remain on the right. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `leftChild_subset_erase` | The actual left child is contained in the selected remainder, the mandatory conditional-marginal premise. Passed explicitly to source filter correspondence and child_integral_cond. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `rightChild_subset_erase` | The actual right child is contained in the selected remainder even for arbitrary Boolean operations. Passed explicitly to the same-sample conditional child law. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `children_disjoint` | True and false outcomes cannot both hold for one child occurrence. This is set disjointness, not random-variable independence. Supports the exact cardinality partition. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `children_union` | The two children exhaust exactly S.erase a for every Boolean comparator and pivot, including pivots outside S. Cardinality and empty-child examples. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `children_card` | For a member pivot, child cards sum to S.card minus one. Natural subtraction is guarded by membership. Used by the right-rank formula and fixed-environment induction. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `leftChild_card_lt` | For a selected pivot the left child is strictly smaller; no key-order hypothesis is needed. Justifies the actual induction call on the left subset. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `rightChild_card_lt` | Analogous strict decrease for the actual complementary child. Justifies the right induction call, including the all-right boundary. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `observedCost` | Real cast of the existing QuickSort.exerciseCost on restrictedOrder of the original sampled permutation. No new execution or recurrence model. Actual pair costs and the 25/21/25 event computations. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `left_filter_on_first` | On the actual optional-head event, the source tail filter equals restriction of the same permutation to leftChild. No unconditional tail identity. low_empty_actual_child and every on-event cost calculation. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `right_filter_on_first` | Same pointwise bridge for the source Boolean complement. The same original tail and permutation are retained. Right empty child and extreme-rank actual costs. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `observedCost_on_first` | The actual source cons equation, cast to Real, gives both child observations plus Nat toll 4*(card-1)+3 on the head event. Middle 5+5+11=21; extremes 1+13+11=25. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `meanBy` | Bochner integral of the actual real observation under uniformOn univ on Equiv.Perm I, before conditioning. Empty, named-label triple, and arbitrary payload transports. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `integrable_observedCost` | Completeness supplies a finite label enumeration locally; actual observation is integrable under the original probability measure. No nodup premise is needed for this fact alone. Legitimizes the finite event integral partition. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `firstEvent_positive_finite` | Selected head event has strictly positive and finite mass using the existing reciprocal-cardinality theorem and a member witness. Every conditioning normalization and the explicit 1/3 head masses. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `integrable_observedCost_cond` | Every fixed subset observation is integrable under conditioning on a selected head, on the same finite sample space. Subset containment is not needed merely for integrability. Both terms in conditional_mean use this before integral addition. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `meanBy_empty` | Actual empty selected order costs one under a finite original uniform environment. No head, nonempty label type, or label default is required. empty_labels_mean uses I=Empty; both empty-child means retain one. | Scoped omission of MeasurableSingletonClass (Equiv.Perm I). |
| `meanBy_singleton` | For complete nodup positions, the singleton order is the supplied label and the actual mean is five for any Boolean comparator. Arbitrary singleton boundary; no distinct-key or order premise. | Scoped omission of MeasurableSingletonClass (Equiv.Perm I). |
| `observedCost_of_all_false` | If every selected pair compares false in the needed orientation, every original sampled order has the actual all-right polynomial 2*n^2+2*n+1. Counterexample family separates distinct records from distinct keys. | Scoped omission of MeasurableSpace (Equiv.Perm I), MeasurableSingletonClass (Equiv.Perm I). Unfold the actual observation before lifting its proved natural cost equality to Real. |
| `meanBy_of_all_false` | Integrates that actual pointwise polynomial; no distinct-key assumption or invented expected recurrence. inputMean_of_equal_keys and taggedEqual_mean. | Scoped omission of MeasurableSingletonClass (Equiv.Perm I). |
| `child_integral_cond` | For fixed T contained in S.erase a, two public HasLaw records identify the same target order law. Their integral transports equate the conditional child mean with its original mean. Both recursive terms; empty-child means. The outside-subset counterexample remains imported. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `conditional_mean` | Integrates the proved on-event source equation under a positive finite head condition, with explicit integrability and actual child marginal transport. Three conditional means, subsequently used by three_mean_from_heads. | Specify the same original uniform measure in ae_cond_of_forall_mem; integrability, head conditioning and both child marginals are retained. |
| `firstEvents_disjoint` | Distinct optional heads give disjoint events. No probabilistic independence is inferred from event disjointness. Finite original head partition and the 2/3 union of extreme events. | Scoped omission of MeasurableSpace (Equiv.Perm I), MeasurableSingletonClass (Equiv.Perm I). Replace unknown on syntax by the explicit pairwise disjoint-event lambda; the old source header did not elaborate. |
| `firstEvents_cover` | Positive selected cardinality gives an actual head in S, so the finite event union is the entire original sample space. Prerequisite for recovering the unconditional integral; zero handled separately. | Scoped omission of MeasurableSpace (Equiv.Perm I), MeasurableSingletonClass (Equiv.Perm I). |
| `first_integral` | Normalizes a restricted integral by the actual reciprocal-cardinality head mass, proving the nonzero real cardinal before cancellation. Translates conditional source contributions to the original measure. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `meanBy_recurrence` | Derived original integral equation for arbitrary Boolean comparators and nonempty S; child observations are actual source projections. The three-head computation and the cardinal induction, never an assumed hypothesis. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `injOn_leftChild` | Restricts an explicit key InjOn premise from S to the actual smaller left set, using its support inclusion. Induction inherits distinct keys without requiring global key injectivity. | Scoped omission of LinearOrder κ. |
| `injOn_rightChild` | Analogous restriction to the right child. It does not replace the false filter by a new algorithm. Induction and the outside key-collision example. | Scoped omission of LinearOrder κ. |
| `restrictedOrder_keys_nodup` | Selected support, nodup labels and local key injectivity imply nodup actual observed keys for each permutation. Records the distinct-key invariant independently of probability and cardinal algebra. | Scoped omission of LinearOrder κ. |
| `mem_rightChild_key` | With local key injectivity and a selected pivot, the actual false comparison is strict greater-than on the erased support. Connects source complement to rank counting while leaving the generic definition unchanged. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `keyEquiv` | Private bijection from selected label subtype to its key-image subtype, constructed from local injectivity and image membership. No label order or key injectivity outside S; used only for rankEquiv. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `rankEquiv` | Composes the existing finite-key-image order isomorphism with the inverse key bijection, giving Fin S.card equivalent to selected labels. Named labels deliberately have no LinearOrder/default instance. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `rankEquiv_key` | The key of a rank-selected label equals the standard ordered key-image embedding at that rank. Establishes correspondence between rank order and actual key comparison. | Scoped omission of DecidableEq I. |
| `leftChild_key_image` | The actual left child key image is the embedding of the finite interval Iio k. Both membership directions are supplied. Supplies the lower cardinal law without a label-order instance. | Instantiate each rankEquiv_key rewrite with the fixed key, selected set, local injection and actual rank. |
| `leftChild_card_rank` | Injectivity on the left child and interval cardinality give left size k.val. Includes minimum-rank empty child and the middle-rank singleton. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `rightChild_card_rank` | Exact complementary cardinality gives right size S.card-1-k.val, including the maximum-rank empty child. Extreme-rank child tables and mean reindexing. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `sum_child_cards` | For any real size observation, reindex actual selected pivots by rank and reflect the complementary indices; both sides yield twice one prefix sum. Used with the independently proved numerical closedForm inside cardinal induction. | Instantiate both Fin-to-range sums, including the reflected natural-index function, before the same reflection theorem. |
| `meanBy_eq_closedForm` | Strong induction quantifies every selected subset in one fixed complete environment and inherits InjOn on each strictly smaller child. It substitutes into the proved actual integral equation and uses the numerical closed-expression recurrence. The separate 71/3 closed-form connection and arbitrary occurrence input theorem. | Use hcard.trans hn to derive T=empty without ambiguous subst n; explicitly rewrite empty mean and closedForm zero. |
| `meanBy_nonneg` | Actual distinct-key selected mean is nonnegative via its proved identification with the numerical expression. Source-specific mean, not an assumption about an arbitrary sequence. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `meanBy_le_nlogb` | For selected cardinal at least two, actual mean is at most 32*n*logb 2 n. Distinctness remains local. Zero/singleton excluded from this scalar bound; growing-family bound follows separately. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `occurrenceInput` | Uses Fin xs.length labels, standard complete positions and the original permutation, then maps List.get over the result. Duplicate payloads keep occurrences. arbitrary_payload_occurrences and tagged payload fixtures. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `occurrenceInput_perm` | Full list permutation of the original input, independent of comparator, payload equality, and key distinctness. The example retains full occurrences and length; not merely equal sets. | Expose the defining mapped occurrence list in the goal before applying the existing mapped permutation proof. |
| `occurrenceInput_length` | Exact occurrence preservation implies sampled payload length equals input length. Arbitrary payload occurrence case. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `occurrenceInput_cost` | The existing exerciseCost_map transports the actual execution observation under the pulled-back comparator. No charge for map/lookup and no map injectivity premise. The mean transport uses this pointwise equality. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `occurrenceMeasurableSpace` | Named local discrete measurable structure on each finite occurrence-permutation space. No structure on payloads is added. Makes the occurrence wrapper law explicit at every input length. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `occurrenceMeasurableSingletons` | Named local measurable-singleton instance for that same discrete finite sample structure. Finite integrability of occurrence observations. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMeanBy` | Integral of actual payload execution over its own finite occurrence environment for any Boolean comparator. Generic empty/singleton and keyed wrapper. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `integrable_inputCost` | Actual mapped-payload observation is integrable on the finite occurrence sample space. No payload measurability instance. Also supports the literal-cost inequality bridge. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMeanBy_eq_meanBy` | Integrates the pointwise map transport, preserving the same original permutation and pulled-back label comparator. Keyed arbitrary-input theorem; equal-key family uses the same generic bridge. | Beta-reduce the pointwise lambda goal, then apply the actual occurrenceInput_cost transport explicitly. |
| `inputMeanBy_nil` | Actual empty payload input has mean one without a comparator law or payload inhabitance premise. arbitrary_empty. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMeanBy_singleton` | Every sampled singleton occurrence order is that singleton, with actual mean five for any comparator. arbitrary_singleton. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMean` | Keyed specialization of inputMeanBy with the strict source key comparator. Payload and key universes are separate. Three arbitrary tagged payloads and taggedRange families. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `occurrence_key_injective` | Nodup mapped input keys imply injectivity of key composed with the actual occurrence lookup. No payload equality/finite/order/default assumption. Supplies the distinct-key hypothesis on the full occurrence-label subset. | Scoped omission of LinearOrder κ. |
| `occurrenceInput_keys_nodup` | Every sampled full-occurrence permutation retains nodup mapped keys under the explicit input hypothesis. Makes inherited sampled distinctness visible as a value invariant. | Scoped omission of LinearOrder κ. |
| `inputMean_eq_closedForm` | The actual arbitrary-payload mean equals closedForm of its length under explicit nodup keys; occurrence and integral transports precede rank induction. arbitrary_tagged_three and every taggedRange_mean. | Give Finset.univ the finite-set type before its explicit coercion to the occurrence-label set. |
| `inputMean_nil` | Keyed actual empty mean remains one, with no distinctness precondition. Actual zero-log scalar counterexample. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMean_singleton` | Keyed actual singleton mean remains five, with no distinctness precondition. Actual one-log scalar counterexample. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMean_of_equal_keys` | All input keys equal a supplied key implies the actual occurrence mean is the attained quadratic polynomial. It is deliberately outside the distinct-key theorem for n>1. taggedEqual_mean and the n=3 mean25 counterexample. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMean_nonneg` | Actual distinct-key payload mean is nonnegative via its exact formula. First half of taggedRange_scalar_bound. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMean_le_log` | Positive-length actual distinct-key mean has the explicit natural-log bound 16*n*(1+log n). Preserves the numerical theorem domain; does not assert n log n at size zero/one. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMean_le_nlogb` | Actual distinct-key mean is bounded by 32*n*log₂n for n at least two. taggedRange_scalar_bound and the literal upper bound. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputMean_family_isBigO` | Any Nat-indexed actual input family with length n and nodup keys has the standard filter Big-O. The sample environment varies with each list. arbitrary_payload_growth gives a nonvacuous unbounded tagged-range family. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputLiteralMean` | Actual append-inclusive cost integrated on the identical occurrence sample; no harmonic identity is defined or assumed for it. Optional approved literal bridge and tagged-range bound. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `inputLiteralMean_bounds` | Finite integrability and existing pointwise actual costs give exercise mean ≤ literal mean ≤ twice exercise mean for every input, without distinctness. Separates metrics while reusing actual observation transport. | Beta-reduce both pointwise inequalities before exact natural-to-real cost casts. |
| `inputLiteralMean_le_nlogb` | Under distinct keys and n≥2, the same-sample append-inclusive mean has constant64 binary-log bound. taggedRange_literal_bound; no exact harmonic assertion about literal work. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |

### Examples/UniformQuickSortMean.lean

352 lines; 16466 bytes; SHA-256 `83e4407bec884caeb3d1ff285a9e6932f52a9f84431f2a5874e322e18773aeb5`.

| Declaration | Intended claim and retained connection | Correction/readback |
| --- | --- | --- |
| `emptyMeasurableSpace` | Discrete measure structure only for permutations of Empty. The sample has its identity even though there is no label/default. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `emptyMeasurableSingletons` | Singletons are measurable in that discrete empty-label permutation space. Supports the finite original law, not a fabricated input element. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `empty_labels_mean` | Actual selected-empty integral equals1 with I=Empty and no possible pivot. Connects meanBy_empty to an uninhabited label type. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `arbitrary_empty` | Any Boolean comparator and arbitrary payload type yield actual empty mean1. Uses inputMeanBy_nil. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `arbitrary_singleton` | Any payload x and comparator give actual singleton mean5. Uses inputMeanBy_singleton; no equality/order requirement. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `actual_pair_cost` | Two source entries cost13 for either Boolean branch result: singleton5, nil1, toll7. Derived from exerciseCost_cons, independently of the closed form. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `two_orders` | Concrete increasing and decreasing two-key orders both have actual cost13. Both use actual_pair_cost, covering opposite empty-child orientations. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `two_input_means` | The two concrete distinct-key input means are13. Uses inputMean_eq_closedForm plus the separately proved numerical size2 value. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `observed_card_one` | Private arbitrary-label helper: actual selected order of length/card1 has cost5. Length law exposes singleton; used by middle_actual_cost. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `observed_card_two` | Private arbitrary-label helper: actual selected order of card2 has cost13, without key assumptions. Length law plus actual_pair_cost supports both extreme heads. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `Label` | Four named labels with decidable equality and finite enumeration only; no order/default deriving. Selected three plus one outside key collision test local assumptions. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `positions` | Complete unsorted priority enumeration middle,outside,high,low. Separates priority enumeration order from key rank. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `selected` | Finite set low,middle,high excludes the colliding outside label. Full mean is for three selected occurrences in a four-label environment. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `key` | Keys high=10, low=-5, middle=7, outside=10. Selected keys are distinct; global injectivity is false. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `comparator` | Exact strict Boolean comparator on those Int keys. Same source comparator throughout filters, costs and mean. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `labelMeasurableSpace` | Discrete measure on actual permutations of the named labels. No payload measure is introduced. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `labelMeasurableSingletons` | Measurable singleton witness for the same named-label sample space. Allows finite original/conditional integral facts. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `law` | The original uniformOn univ measure on label permutations. Every conditional mean explicitly conditions this same law. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `positions_nodup` | Concrete enumeration has no repeated labels. Discharges the source order/tail law hypothesis. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `positions_complete` | Every one of the four named labels occurs in positions. Supplies the finite complete environment without ordering labels. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `selected_keys` | Key map is injective only on the selected three-label set. Discharges the universal mean hypothesis despite outside_collision. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `selected_card` | Selected finite set has cardinal3. Fixes source toll11 and head masses1/3. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `outside_collision` | Outside is excluded, shares high key10, and disproves global key injectivity. Makes accidental global-injectivity assumptions unusable. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `low_children` | Actual low-pivot child sets are empty and {middle,high}. Independent finite source filter computation. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `middle_children` | Actual middle-pivot child sets are {low} and {high}. Independent finite source filter computation. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `high_children` | Actual high-pivot child sets are {low,middle} and empty. Independent finite source filter computation. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `middle_actual_cost` | On the actual middle-first event every original sample has cost21. Uses observedCost_on_first, actual singleton children, and toll11. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `low_actual_cost` | On the actual low-first event every original sample has cost25. Uses actual empty cost1, pair13 and toll11. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `high_actual_cost` | On the actual high-first event every original sample has cost25. Opposite empty-child orientation, same independently expected count. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `middle_first_mass` | The middle-first event under the original law has ENNReal mass1/3. Uses uniformOn_firstEvent and selected_card. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `low_first_mass` | The low-first event has mass1/3 under the same original law. No new conditional or rank distribution is postulated. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `high_first_mass` | The high-first event has mass1/3 under the original law. Completes the actual three-head distribution. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `extreme_first_mass` | Union of the two disjoint extreme-head events has mass2/3. Uses proved event disjointness and finite measure additivity. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `conditional_of_constant` | Private helper integrates an on-event constant under a selected positive-mass head condition. Conditioned probability is established before integrating c. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `middle_conditional_mean` | Actual middle-conditioned integral is21. Uses pointwise actual middle cost, not a numerical recurrence. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `low_conditional_mean` | Actual low-conditioned integral is25. Uses actual low-event execution and valid conditioning. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `high_conditional_mean` | Actual high-conditioned integral is25. Uses actual high-event execution and valid conditioning. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `three_mean_from_heads` | Actual original integral is71/3 from the source conditional terms25,21,25 and the proved head-partition integral equation. Does not reduce QuickSortMean.closedForm; retains the independent probability/execution connection. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `three_mean_from_closedForm` | The universal rank/cardinality mean theorem independently gives71/3 for the same selected environment. Uses local selected_keys and the separate numerical size3 value. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `low_empty_actual_child` | The actual tail source filter at a low-first sample is[]. Uses left_filter_on_first and the independently computed low child set. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `low_empty_child_mean` | Under low-first conditioning, actual left-child integral is1, not0. Uses child_integral_cond with its subset premise, then meanBy_empty. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `high_empty_child_mean` | Under high-first conditioning, actual right-child integral is1. Retains the opposite empty-child boundary through the same public law. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `arbitrary_payload_occurrences` | For arbitrary payloads, every sampled input is a full permutation of xs with equal length. Uses occurrenceInput_perm/length without an equality/order/default instance. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `arbitrary_tagged_three` | For any x,y,z in any payload universe, tags10,-5,7 give actual mean71/3. Nodup keys is established concretely; payloads may coincide or lack equality. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedEqual` | Length-n records (0,i) retain distinct occurrence tags while all sort keys are0. Independent attained-quadratic counterexample family. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedEqual_payloads_distinct` | These full records are nodup because their second components are distinct range indices. Shows that record distinctness is weaker than key distinctness. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedEqual_mean` | Actual sampled mean is2*n²+2*n+1 for every n. Uses inputMean_of_equal_keys and the exact length, rather than a separate recurrence. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `equal_key_counterexample` | At n=3 records are distinct, keys are not, actual mean25 differs from71/3. Checks the necessity and satisfiable failure boundary of the distinct-key premise. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedRange` | Unbounded length-n records (i,payload i) with arbitrary secondary payload function. Finite occurrence environment grows with n. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedRange_length` | Every member of that family has exact length n. Discharges the family theorem length hypothesis. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedRange_keys` | Its projected keys are the nodup natural range. Discharges distinct keys at every n without payload equality. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedRange_mean` | Actual family mean at each n equals the closed expression at n. Connects arbitrary payload family to exact execution means before asymptotics. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `arbitrary_payload_growth` | Standard Nat-indexed filter Big-O for the actual tagged input means. Uses inputMean_family_isBigO with proved length and key facts; no fixed finite-environment vacuity. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedRange_scalar_bound` | For n≥2, actual mean is nonnegative and at most32*n*log₂n. Both conclusions use public actual-input bounds. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `taggedRange_literal_bound` | For n≥2, actual append-inclusive mean is at most64*n*log₂n. Uses the same-sample inequality bridge, not the exact exercise harmonic formula. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `actual_zero_log_boundary` | No real C bounds the positive actual empty mean by C*0*log₂0. Retains the nil tariff1 and necessary scalar domain restriction. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |
| `actual_one_log_boundary` | No real C bounds the positive actual singleton mean by C*1*log₂1. Retains tariff5; eventual Big-O is a separate statement. | No source contract or proof change; complete source reread retains the intended claim and connected cases. |

## Independent expected cases and boundaries retained

The entire example file is unchanged. Its actual cost expectations remain nil1,
singleton5, pair13 in either orientation, and three-key head costs25/21/25 with
masses1/3 each. The actual-head integral proof and the separate rank/formula
proof both retain expected mean71/3. Empty recursive children retain mean1.
The selected-key injection is local: the outside label still shares key10 and
refutes a global injection premise. Labels still derive no order or default.

Arbitrary payload occurrence permutation and exact length remain connected to
public value/transport laws. The equal-key tagged family remains record-distinct
but has actual quadratic mean `2*n^2+2*n+1`, giving25 instead of71/3 at size3.
The tagged-range family retains arbitrary secondary payloads, exact length n,
distinct keys, actual mean identification, scalar constants32/64, and a genuine
Nat-indexed family Big-O. Zero/singleton scalar-log counterexamples remain.
Imported same-tail boundary and transport cases are unchanged, including the
outside-subset bias and the distinction between literal and exercise costs.
These are retained source cases awaiting the successful dependent example build;
the failed core compilation did not validate them.

## Static checks, integration boundary and handoff

`git diff --check` exited0. Static comparison confirms that only the owned core
changed; 124 written declaration headers are identical, and the one other
header is the disclosed explicit-event relation repair. Twelve separate scoped
instance omissions are accounted for above. All definitions and local instances
are unchanged; all 57 example declarations and their expected values are
byte-identical. No admissions, new axioms, unsafe/partial definitions,
`native_decide`, `letI`, warning relaxation, or linter-disabling text was added.
These static checks do not certify proof elaboration, mathematical semantics,
actual theorem assumptions, or exhaustive axiom safety.

The first inventory-recorder pass found a recorder-only mismatch: the retained
inductive header includes its constructors/deriving body. It exited1 before
writing the new inventory. The recorder was corrected to preserve that complete
header; the second pass exited0. This is recorded in `static-checks.json` and
is not misrepresented as a Lean/compiler outcome or a source finding.

The author branch still carries its historical prepared dependency sources.
Root must integrate only this scoped Uniform core successor into the current
central line, preserving the newer independently owned Tail, Order, numerical,
natural-operations and rank corrections. Do not replace the central checkout
with this older author prefix. The actual M2 failure establishes that the before
Uniform bytes were the ones compiled there; it does not freeze dependency proof
repairs owned by root.

The scoped commit, exact successor, source hashes, full diff, actual commit exit,
and clean final status are saved in `receipt.json`/`handoff.md` after commit.
All acceptance gates remain pending. After that receipt, all source/ref/control
writes are held for root's actual diagnostic loop. Foundation Standards remains
separate and pending its own real terminal evidence.
