# ListCalls and FunctionalNotation — bounded source readiness

Status: **source-only, uncompiled; no acceptance or chapter activation**.
Assessed prefix: `c80eec92f5458eccfd1c34c8314d666c2a1e3847`.
Date: 2026-11-02.

## Result and limits

No concrete mathematical, source-domain, connected-example, or inspected
pinned-API mismatch was identified in the two assigned units. No source
correction is proposed on the evidence of this reading. This is a substantive
source assessment, separate from the earlier narrow scan for the proof-script
failure patterns encountered in Chapter 1.

The result does **not** establish elaboration, warning cleanliness, successful
compilation, proof audit, or either independent acceptance axis. In particular,
source inspection cannot certify every simplifier result, tactic import,
`to_additive` generated declaration, or dependent-induction elaboration. These
remain matters for the already required validation of an immutable combined
candidate. No additional gate or implementation requirement is introduced.

The Chapter 1 acceptance prerequisite, the exact initial prefix, and the
existing history-preserving integration plan remain unchanged. Neither unit
accepts Chapter 2 or any later sequential chapter. XB01 covers only Appendix
B.1, not the remaining algorithm-specific subsections of Appendix B.

## Scope and evidence read

The complete assigned formal files were read:

- `Applications/Resources/ListCalls.lean` (190 lines).
- `Examples/ListCalls.lean` (124 lines).
- `Examples/FunctionalNotation.lean` (193 lines).

Their exact prefix sources were considered together with the complete frozen
`reviews/list-calls-requirements.md` and `reviews/notation-requirements.md`,
`research/list-calls-preflight.md`, `research/appendix-c-obligations.md`, and
`research/appendix-c-set-fold-reuse.md`. The complete 313-line
`docs/research/fdsa-notation-map.md`, the Appendix B.1 section of
`docs/research/fdsa-reconstruction-map.md`, and the relevant Appendix B inventory
rows were also read. Existing `FunctionalBasics` and the explicitly cited
standard/list-library bridges were consulted as dependencies of the notation
coverage; unrelated shared draft units were not assessed.

Primary source correspondence uses the retained Appendix B.1 extraction
(printed pp. 347–348) and complete Appendix C extraction (printed pp. 355–359),
plus the previously pinned primary-theory evidence in those records. Appendix C
contains notation and convention rows, not additional numbered theorems or
exercises. Its 90-item map is therefore the appropriate source inventory;
there is no requirement to create a theorem or parser for each editor glyph.

Retained identities:

| Evidence | Identity |
| --- | --- |
| Book, July 27, 2026 edition | SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645` |
| Lean 4.35.0 | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Isabelle supporting theories | `f86f290225eebcc52c1ae7dba2e098f405f51c21` |

The supporting Isabelle revision postdates the book edition, as the existing
notation map states. This report does not replace that provenance or silently
claim a contemporaneous companion-source pin. No new source retrieval,
compiler, project hash helper, Git mutation, cache action, or remote action was
performed for this assessment.

## XB01: actual operations, recurrences and domains

The core uses the existing `Resources.Measured`, `Resources.bind`,
`Resources.pure` and `CallCount.tick`. It introduces actual measured recursive
map, filter and optional lookup, and projections of the existing measured
split. It does not infer execution observations from an equality of ordinary
list values.

| Frozen obligation | Actual source contract and assessment |
| --- | --- |
| Existing append and length, each with count `n+1` | Reuses `Resources.ListReversal.appendRun_exact` and `Resources.SymmetricCosts.lengthRun_exact`; no replacement recursion is added. The append count depends on the left input length. |
| Measured map | `mapRun` at lines 20–23 evaluates the actual head callback, recursively processes the tail, then adds one entry. `mapRun_nil`, `mapRun_cons`, `mapRun_value`, `mapRun_cost` and `mapRun_exact` preserve the empty count 1, the callback value and the exact occurrence sum. |
| Measured Boolean filter | `filterRun` at lines 62–65 uses the returned Boolean for the output branch and executes the recursive tail in either case. The `filterRun_*` equations retain the same callback-plus-tail-plus-one tariff. Discarding an element does not discard its predicate work. |
| Exact callback sum | Both cost results are `(xs.map callbackCost).sum + xs.length + 1`. Repeated values remain repeated summands. `filterRun_cost_eq_mapRun` equates only the observations, not their different returned-list meanings. |
| Constant callbacks | `mapRun_cost_of_constant` and `filterRun_cost_of_constant` require constancy only for `x ∈ xs`, at the fixed supplied callback. They give `(c+1)*xs.length+1`, including `c=0`; no global constant-cost assumption is hidden. |
| Take and drop | `takeRun`/`dropRun` at lines 104–111 preserve one component and the observation of `splitRun`. Nil, zero and successor-cons equations are explicit; the exact results retain `min k xs.length + 1`. No second split executor is introduced. |
| Separate versus fused calls | `take_drop_separate` at lines 140–145 executes take and drop on the same original list, and adds both observations. It proves the fused value with twice the fused observation; it does not identify the observations merely because the values agree. |
| Valid sequential lookup | `lookupRun` at lines 150–153 actually recurses through the list. `lookupRun_value` gives zero-based `getElem?`; `lookupRun_cost_of_lt` and `lookupRun_valid` explicitly require `k < xs.length` and give `k+1`. |
| Invalid lookup extension | Empty lookup is `(none,1)`. Its total count theorem is `min k xs.length+1`; the source comment and reconstruction map explicitly identify the invalid-input portion as the chosen optional extension. The book's valid-domain assertion is not strengthened into a source claim about invalid input. |

For lookup, the first invalid position and every farther position traverse all
`n` cons cells and then the empty case, hence cost `n+1`. A valid last position
instead stops at its head case and costs `n`. That boundary is consistent with
both the displayed recurrence and the examples; no off-by-one issue was found.

The declarations introduce no payload equality, ordering, inhabitant, finite
universe, or random-access assumption. The map input and output universes are
independent. The count carrier is deliberately `Nat`; these are the stated
source-model observations, not a theorem about physical Lean execution or
callback memoization. No change to Knapsack's separate tariff is present.

### Connected XB01 cases

The examples consume the public recurrence/exact/valid-domain contracts. Their
expected values and arithmetic agree with those contracts:

| Client | Observation exposed |
| --- | --- |
| `duplicate_map` | Callback `(x+10,x)` on `[2,2,3]` returns `[12,12,13]` and costs `2+2+3+4 = 11`. |
| `discarded_last`, `discarded_head` | Both orders `[2,2,3]` and `[3,2,2]` retain `[2,2]` with cost 11, including the discarded occurrence's callback work. |
| `zero_and_unit_callbacks`, `discarded_values_still_pay` | Length three costs 4 with zero callback work and 7 with unit callback work, including the all-discarded filter. |
| `map_then_length`, `composed_callback_count` | The actual mapped output feeds the existing measured length. The general count is `sum callbackCost + 2*n + 2`; the concrete example costs `11+4 = 15`. Independent payload universes are retained. |
| `append_then_length` | The actual appended output feeds measured length, giving value `length xs + length ys` and cost `2*length xs + length ys + 2`. |
| `valid_lookup` | Position 2 in `[4,4,9]` returns `some 9` with count 3. |
| `first_invalid_lookup`, `farther_invalid_lookup` | Positions 3 and 20 both return `none` with count 4 under the explicitly extended model. |
| `take_drop_values`, `separate_vs_fused` | Taking and dropping 2 from `[1,2,3]` cost 3 each; their actual sequential composition costs 6 while the fused split costs 3. |
| `zero_and_overlarge`, empty-payload cases | Zero and excessive traversal bounds, and lookup/split on `List Empty`, work without choosing a default payload. |

These cases test value-sensitive callback behavior and composition, not merely
closed equalities between independently invented cost sequences.

## Appendix C: coverage and semantic boundaries

The complete notation map retains all AC-001–AC-090 rows. Its grouped checked
uses fit the frozen requirements without introducing a parallel notation
library or weakening source domains.

| Coverage | Assessment |
| --- | --- |
| AC-001–014, AC-025, AC-035–038 | Standard binders, function composition and formatting are distinguished. `boolean_truth` requires decidability only for its executable `decide` bridge; the source's HOL truth type is not conflated with unrestricted Lean `Bool`. The flattened comprehension retains generator order and duplicates. |
| AC-015–024, AC-026, AC-053–067 | Ordinary sets and products are reused. Proper subset keeps inequality, direct image keeps its witness, two-variable comprehension keeps both witnesses, and bounded quantifiers/unions/intersections are stated without blanket decidability. |
| AC-027–031, AC-039–045 | Typed arithmetic distinguishes natural and real division, floor and ceiling, and natural powers. Unrestricted integer floor division uses `Int.fdiv`; equality with default `/` has the explicit nonnegative-divisor premise. |
| AC-034, AC-046–052 | Standard lists, the existing Appendix A range/index/update clients, and the complete reconstruction map are reused. Valid indexing has a bound or an Option result. Invalid list update is the standard no-op, not arbitrary function update. |
| AC-068–077 | Native multiset cardinality/map/filter/list-coercion laws retain occurrences. `submultiset_is_not_support_subset` distinguishes multiplicity-sensitive `≤` from support-only `⊆`. |
| AC-032–033, AC-078–084 | Standard finite, multiset and ordered list folds are reused. The one new convention adapter tests finiteness of the entire index set; its infinite branch is neutral. |
| AC-085–090 | All six interval membership predicates are present. The printed upper-interval typo is corrected to `Set.Iic`, with checked Nat cases on both sides of endpoint 1. |

### Arithmetic and partial-operation boundaries

`floor_division_nonnegative` at lines 90–91 includes zero among nonnegative
divisors. `floor_division_zero` preserves the total zero-divisor convention.
The concrete negative-divisor example distinguishes `5 fdiv (-2) = -3` from
Lean's default quotient `-2`; it does not claim unrestricted equality of the
two operations. `floor_and_ceiling` uses integer-valued floor/ceiling at
negative `-3/2`, yielding `-2` and `-1`, rather than natural truncations.

The notation map preserves the source's zero-based indexing and separately
records the optional/proof-domain approach. It does not supply an inhabitant
for `Empty` to imitate an underspecified HOL operation. The existing update
bridge retains length and out-of-range no-op behavior. None of these value
correspondences asserts a list execution-cost recurrence; Appendix C has no
such recurrence.

The interval-sum row AC-080 is not silently narrowed to Nat. The map retains
the arbitrary `Set.Icc i j` interpretation with the finite/otherwise-neutral
convention. `closed_interval_fold` is explicitly the finite Nat client
`2..4`, including both endpoints, with sum 9 and product 24.

### Finite-index convention and minimum capabilities

`finiteIndexProduct` at lines 139–141 is an ordinary noncomputable adapter:
for `hs : s.Finite`, use `hs.toFinset.prod f`; otherwise return 1.
`to_additive` supplies the corresponding zero-valued sum convention. The
finite, infinite and supplied-Finset equations are all explicit. It is
finiteness of the whole indexing set, not support of the function, that selects
the branch.

The singleton index case gives 7, while the same single exceptional value over
all naturals gives sum 0 and product 1. Thus the retained examples would detect
a silent substitution of `finsum`, `finprod`, or a finite-support fold. The
local classical decision is acknowledged as noncomputable; no executable
finiteness algorithm or execution bound is claimed.

The index type has no public equality, enumeration, finiteness or inhabitant
requirement. Value types retain the required `CommMonoid` or additive
counterpart. `empty_index_type` uses **Empty indices and Nat values**; it does
not claim that every algebraic operation can be instantiated on an empty
value type. `ordered_list_folds` correctly needs only `Monoid`/`AddMonoid`,
while unordered finite and multiset folds require commutativity.

The concrete repeated-value fold example yields list/multiset sum 7 and
product 12 versus deduplicated Finset sum 5 and product 6. This connects the
container distinction to an observable mathematical consequence.

## Bounded pinned-API compatibility check

The following relevant signatures/uses were inspected in the pinned local
sources; no incompatible supplied argument or missing mathematical hypothesis
was identified:

- `Resources.Measured` is the ordinary value/observation pair. Existing `bind`
  runs its actual continuation and adds observations; `CallCount.tick` adds one.
- `SymmetricCosts.splitRun_value` and `splitRun_work` have precisely the value
  pair and `min k length+1` observation used by the take/drop adapters.
- `SymmetricCosts.lengthRun_exact` and `ListReversal.appendRun_exact` supply
  the exact pair equations used by the connected compositions.
- The retained Lean `Init/Data/List/Lemmas.lean` copy has
  `getElem?_nil`, `getElem?_cons_zero`, `getElem?_cons_succ`, and existing
  calls to `getElem?_eq_getElem` with a bound proof in the form used by the
  lookup bridge. Its `sum_append` (lines 1865–1867) and `prod_append`
  (1883–1885) require associativity and the relevant left identity; the
  `AddMonoid`/`Monoid` hypotheses in `ordered_list_folds` supply them without
  commutativity.
- `Mathlib/Data/Int/DivMod.lean`, lines 28–33, itself uses
  `Int.fdiv_eq_ediv_of_nonneg _ hn` with the same dividend/proof argument order
  as `floor_division_nonnegative`. The directly retained Int Basic file gives
  the operations; this inspection does not pretend that their bridge theorem
  is declared in that Basic file.
- `Mathlib/Algebra/Order/Floor/Ring.lean` supplies `Int.floor_eq_iff` and
  `Int.ceil_eq_iff` in the orientations used by the two negative-real proofs.
- `Mathlib/Data/Set/Basic.lean:303` supplies
  `Set.ssubset_iff_subset_ne` with the exact proper-subset conclusion.
- `Mathlib/Data/Set/Finite/Basic.lean:75–76` defines
  `Set.Finite.toFinset` without public `DecidableEq` or `Fintype` parameters;
  `Finset.finite_toSet_toFinset` at line 366 is the exact Finset round-trip
  used by `finiteIndexProduct_of_finset`.
- `Mathlib/Data/Multiset/Defs.lean` distinguishes support `Subset` from
  the multiplicity `Le` relation, matching the concrete counterexample.

The earlier Chapter 1 failure patterns were also kept in view. The core's
unqualified `bind`/`pure` occur inside `Resources.ListCalls`, while the
connected examples qualify them as `Resources.bind`/`Resources.pure`.
The relevant ordinary definitions are explicitly unfolded or consumed through
public exact equations. No demonstrated analogue of the Chapter 1 ambiguous
simp name or insufficient unfolding was found. This remains a source-level
assessment, not a prediction that all tactic scripts will compile unchanged.

## Disposition

There is no evidence-based repair to make before the already planned
integration and validation stage. Preserve these definitions, domains,
connected cases and documentation at the exact initial prefix. If later
compilation exposes an elaboration or warning failure, repair that concrete
failure without weakening these statements or expanding this readiness pass
into a new acceptance procedure.
