# Chapter 2 mergesort case readiness

Status: bounded independent mathematical/source preparation, recorded
2026-11-02. This is neither Chapter 2 activation nor an implementation,
compilation, final Standards/Spec review, or acceptance result. Chapter 1
remains active; the existing gate 80227 was not touched.

## Scope and inspected evidence

Read in full:

- `mergesort-proof-plan.md`;
- `chapter02-reuse-plan.md`;
- `../reviews/chapter02-requirements.md`;
- `scope-reconciliation.md`.

Also read the relevant original and appended rows of
`chapter02-obligations.md`, the complete existing conaled sorting modules
`Stable.lean`, `Merge.lean`, `Sort.lean`, `SourceMerge.lean`, and
`Examples/StableSorting.lean`. Checked the retained `book-source/Sorting.thy`
merge/top-down definitions and comparison recurrences, and
`book-source/Natural_Mergesort.thy` actual mutual scanner, builder invariant,
and comparison recurrences. These were local source readings, not executions.

The frozen requirements intentionally retain their **107-row snapshot**.
The current reconciled Chapter 2 inventory has **112 rows**, including
C02-108–112, which unpack the already identified C02-088 source claims.
Neither the frozen requirements nor the old plans were edited. The later
operational obligations do not change the source comparison counters.

**Assessment:** no concrete mathematical correction to the retained
top-down value/stability/comparison route was found. Its principal
distinguishing cases and proof dependencies are already present. The
remaining work is to implement and connect those statements to actual
executions, and to retain the reconciled natural-run obligations explicitly.
No sharper universal merge bound, new exact best/worst formula, additional
asymptotic lower-bound theorem for top-down sorting, or new case campaign is
proposed here.

## 1. Existing odd-size cases already distinguish the two recurrences

Use the source's floor-left split, ordinary natural-number `<=`, and one
charge for each comparison of two nonempty merge heads. Both merge base
cases and both sort base cases have comparison cost zero. In particular,
returning a remaining merge tail incurs no further comparisons.

| Existing input | Source floor-left calculation | Source total | Ceil-left comparison recurrence total |
|---|---|---:|---:|
| `[]` | Sort base case | 0 | 0 |
| `[x]` | Sort base case | 0 | 0 |
| `[0,1,2]` | Sort `[1,2]`: 1; merge `[0]` with `[1,2]`: 1 | 2 | 3 |
| `[2,1,0]` | Sort `[1,0]`: 1, returning `[0,1]`; merge `[2]` with `[0,1]`: 2 | 3 | 2 |

The ceil-left counts describe the separately specified comparison
recurrence following the pinned logical Std split. They are not a theorem
about Lean's compiled runtime or an already available measured Std API.
Both lawful value recurrences return `[0,1,2]` on the last two inputs.
Thus value agreement cannot identify their comparison observations, and
neither split orientation always wins even at this one odd size.

The decreasing example must feed the returned `[0,1]` into the final merge.
This is the actual-child-value connection in C02-034: a measured sorter
must bind both recursive results and merge those results. A count attached
to an independently computed standard-sort output would not establish
that connection. The old plan already requires the correct construction.

The two source root merges also supply sufficient small best/worst
witnesses for the fixed lengths `(1,2)`: `[0]` against `[1,2]` takes one
comparison, while `[2]` against `[0,1]` takes two. The former exhausts the
singleton immediately; the latter exhausts the two-element right list.
These are hand traces of existing fixtures, not new general extremal
theorems. One-empty-input merges separately witness cost zero regardless
of the remaining list's length.

The required public estimate remains C02-037,
`Cmerge xs ys <= length xs + length ys`. It need not be attained in these
cases. The termination/count proof works for arbitrary Boolean comparators
and arbitrary input lists; sortedness, distinct keys, nonempty inputs, and
comparator laws are unnecessary for that estimate. A positive lower bound
proportional to total input length for every merge would be a different
claim: an empty side costs zero, and a winning singleton can cost one while
the other side grows. No such claim is needed here.

## 2. Stability connections and exact comparator assumptions

The existing public contracts support the intended proof, with distinct
premises for distinct observations:

| Observation | Existing interface and relevant premises |
|---|---|
| Merge/sort permutation and length | `List.merge_perm_append` / `sortBy_perm`; arbitrary Boolean comparator, no ordering or payload equality assumptions |
| Sorted merge | `merge_sorted_compatible_on`; preorder on keys, sorted inputs, and both true/false branch implications for actual cross-input members |
| Sorted whole-input result | The existing `sortBy_sorted_compatible_on` proof shows how child permutation transports membership back to the original input-local compatibility hypothesis |
| Equal-key filter preservation | `mergeBy_filter`; sorted inputs, preorder and decidable `<=` on keys, decidable key equality, and the actual left-tie `decide (key a <= key b)` comparator |
| Stable keyed sort | Existing `StableSort` observations; the retained source induction uses the ordered contiguous split and the previous merge filter theorem |
| Equality of two stable outputs | `StableSort.unique`; antisymmetry is needed on keys, not records. Producing the two complete sort specifications uses the relevant totality assumptions |

Input-local comparator compatibility alone does **not** force stability.
When two keys are equal, choosing the right head can satisfy the false
branch's inequality just as choosing the left head satisfies the true
branch's inequality. Therefore the generic comparator sortedness theorem
must not be promoted into a stability theorem without the intended tie
behavior. Likewise, `mergeBy_filter` must be applied with the recursive
sortedness hypotheses; a permutation result alone does not supply them.
The retained plan already keeps these dependencies separate.

Reuse `Examples.StableSorting.input` and its independent `expected_spec`:
`[(2,"first"),(-1,"negative"),(2,"last")]` must give
`[(-1,"negative"),(2,"first"),(2,"last")]`. Under the floor-left split,
the equal-key records lie in different children. The actual final merge
first takes the negative record and then must choose the left `2` on the
tie. Its whole-sort comparison count is three by the same recurrence.
Changing to a strict comparator would still use three comparisons here
but would put `"last"` before `"first"`; cost equality therefore cannot
replace the equal-key observation.

The existing `merge_equal_key_filter`, `merge_stable`,
`sorted_permutation_not_stable`, and `expected_spec` already provide the
right semantic boundaries. Connect the future floor-left `StableSort`
theorem to that independent witness, then connect the measured value to
the source value by erasure. No order or decidable equality on arbitrary
payloads should enter the generic statements. Decidable key equality is
the existing filter-observation interface, not a requirement on records.

The source-to-Std equality is the lawful keyed/value result obtained from
the two stable specifications and uniqueness. It is not an arbitrary-cmp
equality and gives no cost equality. C02-031's missing converse remains
the already recorded separate obligation: each input is a sublist of its
merge, so sorted output restricts to sorted inputs. It need not be made a
new prerequisite for the comparison bound.

## 3. Zero, singleton, logarithms, and positive-size conclusions

The old plan handles the necessary boundaries correctly:

- Both child lengths are strictly smaller only in the recursive case
  `n >= 2`. The split is `a = n/2`, `q = n-a`, with `a+q=n` and
  `a <= q <= a+1`; odd inputs do not have two floor-sized children.
- The proposed all-length support bound `Csort xs <= n * Nat.clog 2 n`
  has zero right side at `n=0` and `n=1`, matching the exact comparison
  bases. At `n=3` its bound is six, while the existing fixtures cost two
  and three. This is deliberately an upper bound.
- C02-038 assumes `n=2^k`. Its `k=0` case is a singleton with zero
  comparisons and bound zero; empty input is handled separately, since
  it is not a power of two.
- C02-039's unrounded real `n * log_2 n` corollary retains the same
  power-of-two premise. The all-length ceiling-log bound does not itself
  justify dropping the ceiling. This is a proof-dependency distinction,
  not a claim that a different stronger theorem is false.
- Any natural/real logarithm bridge must keep the planned explicit
  zero/singleton treatment and the precise totalized library convention.
  A positive lower-bound argument must state its positive-size threshold;
  it cannot be applied as a nonzero assertion at comparison-cost bases.

No asymptotic lower bound or sharp best/worst top-down formula is needed
to satisfy the source's upper-bound theorem. The ordinary `List.length`,
`take`, and `drop` work remains outside this observation, as do constructor
entries, comparator implementation work, and remaining-tail traversal.

## 4. The reconciled natural-run obligations remain necessary

The full reuse plan already covers ascending ties, strict descending
runs, arbitrary lawful difference-list workers, arbitrary descending
accumulators, odd/unequal/empty runs, and general merge-all bounds. These
are not newly discovered gaps. The later C02-108–112 clarification must
nevertheless be carried forward with them.

For C02-108, the exact scan identities are sound for the retained mutual
comparison recurrences:

`Casc a ys = length ys`, `Cdesc a ys = length ys`, and
`Cruns xs = length xs - 1` (natural subtraction).

The potentially misleading branch is where a run ends. On `b :: bs`, it
costs one comparison plus `Cruns (b :: bs)`; the latter is `length bs`,
so the sum is still `length (b :: bs)`. Continuing the same run costs one
plus the next worker on `bs`, giving exactly the same result. The
two-element dispatcher costs one plus its worker on the remaining tail.
The empty and singleton dispatcher cases give zero. This mutual proof
does not require the whole input to be sorted, nor a charge for builder
creation/materialization.

For nonempty sorted input, prove `runs xs = [xs]` through the actual
ascending worker and its builder invariant. Equality belongs to the
ascending branch; descending reversal must be strict. The merge-all
comparison base then gives zero, hence `Cnmsort xs = n-1`. Every input of
length `n` pays the same `n-1` scan comparisons and nonnegative additional
merge comparisons, so sorted inputs attain the comparison minimum. For
`n >= 2`, `n/2 <= n-1 <= n` over the reals supplies the eventual linear
reading; at `n=0/1` the exact minimum remains zero. The weaker printed
scan bounds remain corollaries, and the printed natural-sort upper bound
continues to use its intentional `n`, rather than silently replacing it.

C02-109–112 concern a **separate named operational observation**:

- The retained singleton-append construction pays the append subcost
  `1 + ... + n = n*(n+1)/2` under `appendTime prefix [x]=length prefix+1`.
  Loop/wrapper charges must be stated separately. Cons followed by the
  verified accumulator reverse must return the same ordered list; a
  reversed value alone is not the comparison target.
- Creating a composed builder has its own bounded local charge and does
  not invoke its stored functions. In the actual ascending update,
  `f` composed with singleton-prefix `a` represents `f [] ++ [a]`;
  reversing composition order changes the observation.
- Materialization is bounded in the finite construction representation,
  with a proved size relation for actual ascending-run builders. The
  arbitrary-D value invariant alone does not bound application cost in
  output length. The retained empty-prefix/extra-identity-composition
  boundary is the correct independence witness.
- The full scanner bound must assemble the actual construction and
  application charges across emitted runs, descending cons work, run-list
  construction, and empty/single-run merge dispatch. Its constants need
  not give zero operational work on inputs whose comparison count is
  zero. Do not infer an operational lower bound from an upper bound alone.

The general merge-all comparison bound uses total payload length `L` and
run count `m`: `L * Nat.clog 2 m`. Its existing `m=0/1` bases cost zero;
multiple empty runs can also have zero comparisons despite pass
dispatches. Uniform run-length doubling still needs an even run count;
the general total-length estimate does not. The retained reversed-pass
exercise proves ordinary correctness without automatically inheriting
keyed stability. Choosing the source floor-left sorter for C02-107 is
already enough for the stated non-insertion stable-sort adaptation.

## 5. Bounded implementation-readiness conclusion

The existing compact connected case set is sufficient: empty/singleton,
the two opposite odd-size traces, the retained keyed fixture and equal-key
filter boundary, and the already listed natural-run/accumulator cases.
Use each through the eventual public source, measured-erasure, stability,
and bound statements. Direct evaluation alone would not establish those
connections. C02-108's exact mutual scan proof and C02-109–112's actual
operational bridges remain explicit work beyond the old top-down plan.

This note adds no implementation, scope freeze, acceptance gate, new
exhaustive experiment, or replacement cost model. No compiler, checker,
project hash helper, Git/ref operation, cache/configuration change,
remote action, or gate manipulation was performed. Only this new note
was written; all source, old plans, requirements, inventories, and
tracking records were left untouched. Compilation and all applicable
independent final-review/acceptance obligations remain pending.
