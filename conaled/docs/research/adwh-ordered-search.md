# Ordered-function search reconstruction

[#179](https://github.com/VladimirMarko/conaled/issues/179) reconstructs the
complete finite and global binary-search module from checkpoint 233. The public
implementation is in `Applications/Search/Ordered/`, with checked consumers and
cases in `Examples/OrderedSearch.lean`.

`search2` searches a finite interval by binary recursion. `search4` first doubles
an upper bracket, finds its least threshold index, then tests equality. Both
return exactly the exhaustive preimage list for a strictly increasing
`Nat → Nat` function. The original lower midpoint and recovered upper midpoint
remain separate executable choices. Their results agree; comparison traces and
costs are outside this development.

## Contracts and reuse

`Exact` specifies an interval answer by filtering standard `List.range'` and
proves exact result equality for every policy selecting an in-range pivot.
`Increasing` is an abbreviation for `StrictMono`. Standard monotonicity,
injectivity and `StrictMono.le_apply` replace the three source order lemmas.
The latter fact gives `n ≤ f n`, needed for global exhaustive coverage and
doubling termination. The two short-list helpers now accept any element type;
the uniqueness length bound uses `List.Nodup.length_le_of_subset`.

`Threshold` separates a cut specification from its recursive implementation.
Its theorem requires only `Monotone`, so plateaus are supported. The result lies
between the interval start and its excluded endpoint. Values before it are
below the target; values after it within the interval reach the target. An
interval with no hit returns its excluded endpoint. The source strictly
increasing case follows by `StrictMono.monotone`.

`Global` retains the actual doubling executor, including its positive seed,
initial-seed exception and predecessor miss. `Bracket.lower = none` represents
the original fictitious negative-one sentinel. The upper endpoint is known to
hit. Both zero-start and trimmed lower-bracket searches may return that excluded
endpoint. `LeastThreshold` independently states a hit and leastness among all
natural indices. Neither result equality nor the bracket certificate identifies
execution traces.

`Consumers` reuses `Squares.Rep`, `Squares.Square` and `Squares.compose`:

- `preimageSquare` returns an optional index, specified by the head of the
  exhaustive preimage list. `preimageValue` composes it with `Option.map f`.
  The optional witness exists exactly when its index maps to the target; a miss
  means no natural index does so.
- `thresholdSquare` refines the standard least witness `Nat.find`, whose
  existence follows from `StrictMono.le_apply`. `roundUp` composes it with the
  observation `n ↦ (n, f n)`. Its public contract gives the actual value, a hit,
  and a strict miss at every smaller index. At positive indices it yields the
  predecessor sandwich inequality.

The implementation of each consumer uses the binary/doubling algorithms.
`Nat.find` is the independent specification of threshold selection. Existing
weighted graph search and finite occurrence-rank selection have different
contracts; this change does not introduce adapters between them.

## Checked cases and statement review

The initial source examples calculated answers but did not connect them to the
universal result refinements. The retained examples now rewrite through
`search2_eq_search` and `sourceSearch2_eq_search`; the midpoint example is paired
with the public variant-equivalence theorem. Consumer cases use public square
contracts and correctness results.

For `f n = 3*n+1`, target 16 has exact index 5 and observed value 16. Target 15
has no preimage, yet rounds to index 5 and value 16. The independently stated
`affine_threshold15` proves that five is the least threshold; the example then
uses the square's commutation law to identify its output. Sandwich inequalities
come from `roundUp_sandwich`.

Other cases cover identity and affine targets at zero, the optional lower
sentinel, a zero-length interval starting at seven, singleton hits and misses,
constant monotone functions at/below/above their value, both midpoint choices,
and an always-zero valid pivot policy. Identity targets seven and eight exercise
multiple actual doubling steps and exact upper-endpoint hits. Public bracket
fields establish the hit and predecessor miss. A constant function on two
indices supplies a counterexample to replacing strict monotonicity by
monotonicity in exact preimage-list equality: the exhaustive list has two
occurrences while the binary result has at most one. A String-list case checks
the generalized short-list helper.

Statement review checked every reconstructed and added claim by family:

| Family | Review |
|---|---|
| Exact interval/global preimages | Quantification includes every natural index and arbitrary finite start/count. Strictness supplies uniqueness; membership is tied to independent range/filter semantics. The source equality-test direction is harmless equality symmetry. |
| Pivot recursion | The only policy obligation is an in-range pivot for positive count. Each recursive count decreases. No efficiency claim follows for an arbitrary policy. |
| Threshold cuts | Monotonicity suffices; no injectivity is used. The excluded endpoint and empty interval are included in the result domain, while hit claims are restricted to indices inside the interval. |
| Doubling and brackets | The seed is positive. Natural subtraction is used in a decreasing measure justified by the standard index bound. The predecessor miss has the explicit initial-seed exception. Sentinel branches do not invent a natural lower index. |
| Global least thresholds | The upper hit discharges the excluded-endpoint case. Lower-bracket trimming uses a justified miss below the start. Leastness is universal, not just a recursive interval invariant. |
| Optional and rounding consumers | Exact inversion performs its final equality test; rounding may overshoot. The optional value consumer composes the actual optional index executor. Rounding preserves the actual function value and only claims a predecessor sandwich when the index is positive. |
| List helpers and cases | Helpers quantify over arbitrary element types. Concrete strictness/monotonicity assumptions are proved. Cases consume public results and retain independently justified expected answers. |

No outstanding statement-review defect was found. This review does not claim
that examples exhaust all possible specification mistakes.

## Provenance and validation

Reference: [preserved checkpoint documentation](../history/algorithm-design-haskell/README.md),
snapshot `adwh-checkpoint-233`, member
`project/adwh-lean/ADWH/Chapter04/BinarySearch.lean`, SHA-256
`2196b768f092426fa5cd0a7d5aadb316d3535f09872d5e19cf556e2261506ec7`.
The member bytes were checked against the preserved ZIP, member manifest and
inspected extraction. The [declaration ledger](adwh-ordered-search-provenance.tsv)
accounts for all 54 named declarations, including three standard theorem
replacements, the standard predicate alias, and four generalized statements.
The four original anonymous examples appear at the start of the example module.
No original import closure was copied; the source module imported only Std.

Targeted validation: `direnv exec . lake build Examples.OrderedSearch` passed
(436 jobs). Lake reports the existing style of Mathlib module-system import
advisories for legacy modules; no tactic/linter warning was suppressed. Whole
repository fresh compilation and exhaustive proof audit belong to the root
integration gate.

All `LinearSearch3` declarations remain deferred, including its linear first-hit
semantics and phase counters. Those counters exclude bound/doubling. Also
deferred are interval/guard/doubling/recurrence and comparison lower-bound costs,
grid search, node-labelled tree traversal, AVL construction/update/deletion/split
and set operations. This reconstruction makes no allocation, asymptotic,
processor, compiled-runtime or comparison-trace claim.
