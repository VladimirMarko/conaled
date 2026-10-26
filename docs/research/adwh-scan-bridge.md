# Textbook scan and fusion reconstruction (#152)

`Applications.Parallel.InclusiveScan` connects the textbook's inclusive state
sequence to the existing parallel scanner. `Scanner.inclusive` runs the
scanner once, flattens its exclusive prefixes, and appends its final total.
`Scanner.inclusive_correct` proves that this is `List.scanl (· * ·) 1`.
The proof consumes `Scanner.correct`, so it applies to every `ScanPlan`,
including product, composition, empty and singleton plans. It does not replace
the shape-directed implementation with sequential evaluation.

`SquareKit.ListFusion` supplies the accumulator theory independently of
monoids. An invariant holds initially and is closed under the source step;
the interpretation need commute with that step only on invariant states.
`scanl_reachable` transports every state, and `foldl_reachable` transports the
final state. `foldr_reachable` and `foldr_iff` retain the source's right-fold
argument and exact reachable-context characterization. No commutativity,
associativity, identity, or equal input/accumulator types are needed there.

## Provenance and scope

The immutable source is [adwh-checkpoint-233](../history/algorithm-design-haskell/README.md),
using these members of the preserved archive. Hashes come from
[`checkpoint-233.files.sha256`](../history/algorithm-design-haskell/checkpoint-233.files.sha256).

| Archive member | SHA-256 |
|---|---|
| `project/adwh-lean/ADWH/Chapter01/Lists.lean` | `6f08454e2deeb5fe00df14e997b9d7f24bd53ba979546c8636bc3254e4a151b0` |
| `project/adwh-lean/ADWH/Chapter01/ScanFusion.lean` | `143eb5e6f216c89508bf161600ee56b3ca2512997a592cc40626d31a6b09d4a7` |

| Source declaration | Reconstruction and assumptions |
|---|---|
| `Lists.scanl`, `Lists.scanl_spec`, `Lists.foldl`, `Lists.foldl_eq_foldl`, `Lists.foldr`, `Lists.foldr_eq_foldr` | Use standard `List.scanl`, `List.foldl`, and `List.foldr` directly; no duplicate recursive foundations or compatibility wrappers are introduced. |
| `Lists.foldr_fusion_reachable` | `SquareKit.ListFusion.foldr_reachable`; preserves invariant, seed, closure, and restricted commuting hypotheses. Input, source state and target state have independent universes. |
| `Lists.foldr_fusion_iff` | `SquareKit.ListFusion.foldr_iff`; preserves the equivalence for all finite lists at a fixed seed, with the law required at exactly right-fold reachable contexts. |
| `Lists.foldl_fusion`, `Lists.foldl_invariant` | Combined into `foldl_reachable`; the commuting equation is required only on the supplied invariant, rather than all states. `scanl_reachable` extends this to intermediate states. Unrestricted final-state fusion already exists as Lean's `List.foldl_hom`; it is not copied. |
| `ScanFusion.foldl_inits_eq_scanl`, `ScanFusion.scanl_prefix_values` | `scanl_prefix_values` preserves the indexed-prefix conclusion for arbitrary accumulators, using Lean's `List.getElem_scanl` instead of copying recursive `inits` and fold/scan foundations. |
| `ScanFusion.replace`, `doubleStep`, `doubleStep_even`, `replace_step_reachable`, `restricted_replace_fusion`, `unrestricted_replace_fusion_false` | `Examples.ScanFusion.replaceOdd`, `doubleStep`, `doubleStep_even`, `replaceOdd_step`, `restricted_foldr`, `unrestricted_law_false`; same `Int` parity invariant and unreachable odd-state counterexample. Added scan and left-fold clients and an odd-seed failure. |

The inclusive/exclusive bridge and scanner interpretation theorem are new
connections to conaled. The preserved archive remains the reference for
unmigrated Chapter 1 material, including suffix scans, source-specific wrapper
derivations, and cost contracts. This change makes no whole-chapter parity,
parallel execution, runtime, or complexity claim. The current plan grammar
supports `.empty`; no size restriction is needed for this bridge.

## Checked development cases

The initial obligations were an ordered inclusive observation of a composed
pair-of-pairs plan, and interpreting that observation as cumulative word
lengths. Existing `Scanner.correct` produced a pair of exclusive prefixes and
total, so the missing connection was the inclusive decoder equation, not the
ability to reduce a concrete scan. `sequential_scanl` discharges that connection;
`inclusive_fusion` composes it with accumulator interpretation.

All cases live in `Examples.ScanFusion` and are imported by
`SquareApplications.lean`:

| Case | Independent expectation and public result used |
|---|---|
| `additive_four` | Input `1,2,3,4` gives states `0,1,3,6,10`; `Scanner.inclusive_correct` on a composed plan. Naturals use `Multiplicative` explicitly, so multiplication means addition. |
| `additive_seed` | Seed `5` and inputs `1,2` give `5,6,8`; `sequential_scanl`. |
| `empty_plan`, `singleton_plan` | Empty gives `[0]`, singleton `7` gives `[0,7]`; `inclusive_correct`. |
| `ordered_words` | Words `[1,2]`, `[3]`, `[4,5]`, `[6]` produce ordered concatenated prefixes including the empty word; `inclusive_correct`. Reversing chunk adjustment changes the expected values. |
| `word_lengths`, `composed_word_lengths` | Word-length interpretation of every plan is an inclusive sum of input lengths; `inclusive_fusion` and standard `List.length_append`. The composed example gives `0,2,3,5,6`. |
| `reverse_prefix_lengths` | List-valued accumulator and natural inputs; lengths of reversed prefixes grow by one. Uses `scanl_reachable`, with no monoid restriction on the transition. |
| `prefix_decimal` | Decimal digit accumulation gives `0,2,27,271,2718`; indexed-prefix scan lemma. |
| `restricted_foldr`, `restricted_foldr_via_context` | Replacing odd values leaves every fold result unchanged because reachable states are even. Uses `foldr_reachable` and `foldr_iff`, respectively. |
| `restricted_scanl`, `restricted_foldl` | The same parity invariant transports all left-fold states and the final state through their respective reachable-state theorems. |
| `unrestricted_law_false`, `odd_seed_scan_fails` | At input `1` and odd state `1`, the commuting equation compares `0` and `2`. Starting the scan from that odd seed also breaks fusion. |

## Statement review

The inclusive decoder appends exactly one final state. Its result has the
seed and all prefix folds, including the final fold, and the empty case is a
singleton. `sequential_scanl` quantifies over arbitrary seeds; certified
scanners retain their existing identity seed. Multiplication order is preserved
under a `Monoid` assumption only. The word example distinguishes the ordering
that additive examples cannot detect.

The fusion theorems quantify over finite input lists, arbitrary operations,
independent accumulator types, and a fixed interpretation. Their hypotheses
are local invariant closure and a one-step commuting equation, not the desired
whole-list equality. The even-state example proves these hypotheses while
refuting the global equation, demonstrating that the weaker interface is
usable. The odd-seed counterexample checks why the initial invariant is needed.
The `foldr_iff` equivalence refers to contexts reachable from its fixed seed;
it makes no claim about every accumulator value. `scanl_prefix_values` includes
indices from zero through the input length and reuses Lean's elementwise scan
semantics.

The only new operation on scanner output is decoding; existing scan recipes,
correctness statements and clients are unchanged. The generic `word_lengths`
application combines independently established word-length preservation,
reachable scan fusion and shape-directed scan correctness without inspecting
scanner internals. These declarations and their helper facts are included in
the normal fresh source build and exhaustive axiom audit.
