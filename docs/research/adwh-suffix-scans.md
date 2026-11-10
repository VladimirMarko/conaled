# Chapter 1 suffix scans and fusion

`scanr_suffix_values` specifies the complete ordered result by the right fold of
each indexed suffix, from index zero through the list length. The final value is
the seed, including for an empty input. `foldr_tails_eq_scanr` supplies the book's
suffix-list formulation using the standard list of suffixes.

`scanr_reachable` derives interpretation of every suffix state from the existing
`foldr_reachable` theorem. Input elements, source accumulators and interpreted
accumulators may have different types. Its assumptions are an initial invariant,
invariant closure under the source step, and a commuting equation only on those
invariant states. It needs no associativity, commutativity or monoid instance.

## Source identity and declaration correspondence

The selected source is the user-supplied `adwh-checkpoint-335` compact recovery
archive, SHA-256
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
The payload member is
`project/adwh-lean/ADWH/Chapter01/ScanFusion.lean`, SHA-256
`143eb5e6f216c89508bf161600ee56b3ca2512997a592cc40626d31a6b09d4a7`.
Its bytes agree with the previously recorded checkpoint-233 inventory; this
development reads the supplied successor. The source identifies Exercises 1.12
and 1.17 and their answers. This record claims no new consultation of the absent
book PDF.

| Source declaration | Destination and disposition |
| --- | --- |
| `ScanFusion.scanr_suffix_values` | Adapted as `SquareKit.ListFusion.scanr_suffix_values`, using `List.getElem_scanr` instead of copied recursive folds/scans. Same suffix order and empty suffix. |
| `ScanFusion.foldr_tails_eq_scanr` | Adapted as `SquareKit.ListFusion.foldr_tails_eq_scanr`, using standard `List.tails`, `map`, `foldr` and `scanr`. |
| `ScanFusion.tails`, `tails_spec`, `mem_tails_iff`, `tails_length` | Source-specific wrapper is omitted. The selected indexed specification and suffix equation use standard List observations directly; no whole-source-module replacement is claimed. |
| `Lists.foldr_fusion_reachable`, already represented by `foldr_reachable` | Reused to derive the new `scanr_reachable` theorem for every suffix; this is an extension, not a claim that a source right-scan fusion theorem exists. |
| `ScanFusion.doubleStep_even`, `replace_step_reachable`, `restricted_replace_fusion`, `unrestricted_replace_fusion_false` | Existing `Examples.ScanFusion` definitions/laws are reused. `Examples.SuffixScan.restricted_scanr` adds an all-suffix application; the existing unrestricted-law counterexample remains available unchanged. |

The earlier fold/prefix reconstruction is recorded in
[adwh-scan-bridge.md](adwh-scan-bridge.md). No change here claims Chapter 1
completion, infinite-list behavior, demand preservation, parallel execution or
runtime/cost improvement.

## Checked development cases

The missing connection was from a right scan to independently specified suffix
folds. Standard `List.getElem_scanr` already supplied its elementwise law, so no
artificial failing proof was introduced. The list-level theorem collects those
observations; suffix fusion then reuses the existing public right-fold result.

All new cases live in `Examples.SuffixScan`:

| Case | Independent expectation and connection |
| --- | --- |
| `word_suffixes` | Every suffix of a list of words is flattened in order. Connects `scanr_suffix_values` to the standard fold/flatten law. |
| `ordered_words` | Words `[1,2]`, `[3]`, `[4,5]` yield `[1,2,3,4,5]`, `[3,4,5]`, `[4,5]`, `[]`; uses `word_suffixes`. |
| `subtraction_suffixes` | Right-fold subtraction on `10,3,2` gives `9,1,2,0`; uses `scanr_suffix_values`. Its nonassociativity distinguishes the requested recurrence. |
| `seeded_empty` | Empty input with seed seven yields `[7]`; uses the indexed suffix theorem. |
| `word_lengths`, `word_lengths_example` | List length interprets concatenation as addition; `scanr_reachable` gives `5,3,2,0` in the concrete case. The words and their length observations remain distinct. |
| `suffix_folds` | The source tails/map equation recovers the same nonassociative result; uses `foldr_tails_eq_scanr`. |
| `restricted_scanr`, `restricted_negative_example` | Existing parity closure and commuting laws suffice on all suffixes. Input `-3,4,2` yields `6,12,4,0` after odd-state replacement. |
| `odd_seed_fails` | Starting from odd seed one violates fusion even for input `[1]`; checks the necessity of the initial invariant. |

## Statement review and validation scope

The suffix indices run from zero to length inclusive. The right fold retains
the supplied seed and the order of the source step. The final singleton empty
suffix is not dropped. The specification is about finite lists, and each list
position is retained even if several fold values coincide.

Fusion hypotheses concern one transition and the reachable-state invariant,
not the desired whole-scan equality. The parity client discharges those premises
and the existing odd-state counterexample refutes the stronger unrestricted
condition. Word and subtraction cases guard against accidental left-scan,
reversal, commutativity or associativity assumptions.
