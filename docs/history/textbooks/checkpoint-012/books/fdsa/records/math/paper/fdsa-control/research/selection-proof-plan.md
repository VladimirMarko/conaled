# Chapter 3: a concrete median-of-medians implementation and proof plan

Research date: 2026-11-02. **Queued preparation, not implementation or chapter acceptance.**
This note identifies reusable declarations and remaining proofs. No Lean files,
builds, Git refs, tickets, or acceptance states were changed. The primary chapter
gate remains under root's control.

## Evidence and scope

The source is the July 27, 2026 [FDSA PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
printed pp. 31–44 and Appendix B.1–B.2, pp. 347–348; its SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion [Selection.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Selection.thy)
is pinned at Isabelle `f86f290225eebcc52c1ae7dba2e098f405f51c21`, file SHA-256
`c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8`.
It names Manuel Eberl and imports `Complex_Main`, `Time_Functions`, and `Sorting`.
Isabelle's pinned `COPYRIGHT` supplies the BSD-3-Clause terms; preserve relevant
notices in a translation. These notes are original analysis, not manuscript text.

Reuse was checked against conaled's existing `Applications/Selection/{Rank,ThreeWay,Consumers}.lean`
and `Applications/Sorting/Sort.lean`; the shared insertion/list-call candidate is
frozen for this plan at `c80eec92f5458eccfd1c34c8314d666c2a1e3847` in the isolated
`conaled-insertion-costs` worktree. Its existence is not evidence of integration
or acceptance. Dependency pins are Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`, and Lean
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The [chapter inventory](chapter03-obligations.md) supplies C03 identifiers. This
plan primarily resolves the deterministic chain C03-001–046 and gives concrete
routes for the exercises. The affirmative randomized-selection mathematics on
p.35 must also remain in scope: worst-case quadratic and expected linear work
for a specified random-occurrence pivot policy, together with a precise boundary
for the cited tail claim. Root and the inventory owner are reconciling those
rows separately. The deterministic proof below neither establishes those
expectations nor permits deleting them as external discussion.

## 1. Preserve the existing semantic contract

Write `n = xs.length`, `L(xs,a) = xs.countP (fun x => decide (x < a))`, and
`G(xs,a) = xs.countP (fun x => decide (a < x))` in this note only. Counts include
occurrences. The main semantic and pivot-balance arguments use `[LinearOrder α]`
and **do not require `Nodup`, `Inhabited`, a bottom element, or a top element**.
Pure chunking and the generic call-count combinators need no order on payloads.

| Existing declaration | Exact reusable meaning | Boundary |
|---|---|---|
| `Applications.Selection.RankedAt xs k a` | A permutation witness `pre ++ a :: post`, prefix length `k`, prefix values at most `a`, suffix values at least `a`. | Zero-based, occurrence-sensitive, independent of an algorithm. |
| `pairwise_ranked` | Sorted permutation plus `ys[k]? = some a` implies `RankedAt xs k a`. | Its stated assumptions require only `LE`; sorting construction supplies stronger laws separately. |
| `ranked_iff_index`, `RankedAt.unique` | `RankedAt xs k a` iff `(ordered xs)[k]? = some a`; uniqueness of the value. | Linear order; ties need not designate a unique occurrence. |
| `ordered_perm`, `ordered_pairwise` | Canonical sorted result has the right occurrences and order. | This canonical sort is a specification witness, not the book's insertion baseline or its measured execution. |
| `selectWith_value`, `selectWith_some_iff`, `selectWith_none` | For a `PivotValid` policy, positive public rank `r` selects zero-based rank `r-1`; failure iff `r=0` or `n<r`. | The existing public selector is **one-based**. |
| `lowerMedian_ranked`, `lowerMedian_odd_index`, `lowerMedian_even_index` | Lower central occurrence, with explicit odd/even indices. | The nonempty arithmetic bridge is `(n+1)/2 - 1 = (n-1)/2`. |
| `RankedAt.map`, `selectWith_map` | A monotone relabeling preserves selected values, even if it merges keys. | No injectivity is needed; this is useful evidence that duplicate support survives composition. |
| `ranked_strict_counts`, `lowerMedian_strict_counts` | Exact strict counts on distinct input. | These theorems explicitly assume `Nodup` and cannot supply the book's general duplicate-aware bounds without new lemmas. |

### Small missing rank bridge

Add a theorem, not a second rank predicate or selector framework, with this
mathematical statement:

```text
RankedAt xs k a ↔ L(xs,a) ≤ k ∧ G(xs,a) < xs.length - k.
```

No separate in-bounds premise is logically needed: the right-hand strict
inequality itself implies `k < xs.length`. The forward direction reuses the
`pre/post` witness, `List.Perm.countP_eq`, `List.countP_append`,
`List.countP_cons`, `List.countP_eq_zero`, and `List.countP_le_length`. Those
same count operations are already used by `ranked_strict_counts`.

For the converse, put `ls/es/gs = partition3 a xs`. The filters identify their
lengths with `L`, the equal count, and `G`; `partition_lengths` gives
`length ls ≤ k < length ls + length es`. Every equal-block value is `a`, so
its in-bounds indexed value is `some a`. `sorted_partition` and standard
append indexing then give `(ordered xs)[k]? = some a`, allowing
`ranked_iff_index` to close the proof. This also yields exactly the middle-branch
helper needed below. It uses no assumption that `a` was initially known to occur.

Theorem 3.1 follows from this equivalence and `RankedAt.unique`. Theorem 3.2
follows from `pairwise_ranked`. The book/public-index adapter is simply
`selectWith choose (k+1) xs = (ordered xs)[k]?` for a valid policy. A source
algorithm returning zero-based `Option` results should retain that convention
and prove this adapter, rather than change `selectWith`.

## 2. Reuse three-way partition laws; supply its source execution separately

Existing `partition3` performs **two** `List.partition` operations. Its verified
laws are exactly useful: `partition3_eq_filters`, `partition3_perm`, the three
membership iff theorems, `partition_lengths`, `partition_strict_sizes`,
`sorted_partition`, and `dispatch_value`.

The book's implementation recursively processes the tail once and then adds
the head to one of three buckets. A new measured realization should therefore
have the following two independent contracts:

```text
(partitionRun p xs).1 = Applications.Selection.partition3 p xs
(partitionRun p xs).2 = xs.length + 1.
```

Define its empty case with work `1`, and its cons case with work equal to the
recursive-tail work plus `1`; comparisons and tuple/cons construction have zero
charge in this source model. Induction plus `partition3_eq_filters` proves the
value bridge. Thus all existing semantic laws transport without inventing a
second partition specification. The cost is proved from the actual one-pass
recursion; output equality does not assign `n+1` to the old two-pass operation.

`dispatch_value` is zero-based, but its equal branch indexes `es[k-length ls]?`.
The source branch returns `p` directly. Prove the helper

```text
length ls ≤ k → k < length ls + length es →
  es[k - length ls]? = some p
```

using `partition_equal_mem` and in-bounds indexing. Then the book's semantic
recurrence holds for an arbitrary pivot, with no membership hypothesis. For
termination, separately require `p ∈ xs` and reuse `partition_strict_sizes`.
Only a reached middle branch justifies a nonempty equal block; an arbitrary
pivot outside the input can have `es=[]`.

## 3. Chunking: standard value reuse and exact separate traversals

Batteries' `List.toChunks` exists in `Batteries/Data/List/Basic.lean`. It uses
arrays internally and returns `[xs]` when the chunk size is zero and `xs` is
nonempty. The book instead defines `chop 0 xs=[]`. No theorem equating this
implementation to the source's positive-size take/drop recursion was found in
the inspected list libraries. The adjacent `toChunksAux` definition is not
used by `toChunks`; its presence is not such a bridge.

A particularly small reference adapter can instead use Mathlib's
`List.splitLengths`, with the existing natural ceiling division:

```text
chopValue d xs := (List.replicate (xs.length ⌈/⌉ d) d).splitLengths xs.
```

`Nat.instCeilDiv` and `Nat.ceilDiv_eq_add_pred_div` in
`Mathlib.Algebra.Order.Floor.Div` give `n ⌈/⌉ d = (n+d-1)/d`, including the
zero-divisor convention `0`. `ceilDiv_le_iff_le_mul` and
`le_smul_ceilDiv` expose its rounding law for `0<d`. Do not introduce a parallel
ceiling operation. `Mathlib.Data.List.SplitLengths` already provides
`splitLengths_cons`, `length_splitLengths`, `length_mem_splitLengths`, and
`flatten_splitLengths`.

This adapter has the source's zero and empty cases, and its count is immediate
from `length_splitLengths`. Its positive nonempty recursion follows from

```text
n > 0 → d > 0 → n ⌈/⌉ d = 1 + (n-d) ⌈/⌉ d.
```

Prove this small natural arithmetic lemma, then use `splitLengths_cons`.
The same recursion gives nonempty chunks, the upper bound `length chunk ≤ d`,
and strict tail decrease. `flatten_splitLengths` applies because
`n ≤ d*(n ⌈/⌉ d)`; flattening also supplies membership and multiset bridges.
The optional positive-real bridge
`⌈(n:ℝ)/(d:ℝ)⌉₊ = n ⌈/⌉ d` follows by comparing the two `≤ k` characterizations
with `Nat.ceil_le` and `ceilDiv_le_iff_le_mul`.

The measured source operation still must perform **both** `take` and `drop`
calls. At the frozen shared draft, `Resources.ListCalls.takeRun` and `dropRun`
each cost `min d n + 1`; `take_drop_separate` explicitly distinguishes their
sum from the fused `SymmetricCosts.splitRun` cost. Define measured `chopRun`
with the source recursion and prove its value equals the standard adapter.
Do not charge the source for the reference adapter's preliminary length or
replicate operations; that adapter is its value specification, not its counted
execution.

The exact useful count for `d>0`, with `m=n ⌈/⌉ d`, is

```text
(chopRun d xs).2 = 2*n + 3*m + 1.
```

Each positive step pays `2*(min d n+1)+1`; the final empty call pays `1`.
This proves the book's uniform `≤5*n+1`, since `m≤n`; for `d=0` the count is
`1` directly. This exact formula is optional strengthening, but the separate
take/drop recurrence and the book's bound are required.

## 4. Insertion baselines and the short final group

Reuse `Resources.InsertionSort.sortRun (· ≤ ·)` rather than sorting by
`ordered` inside the executable baseline. Its inspected contracts are
`sortRun_value`, `sortRun_length`, `sortRun_quadratic`, the stronger
`sortRun_cost_le`, and `sortRun_stable`. `Applications.Sorting.sortOn_eq_insertionOn`
connects the insertion result to the existing canonical sorted observation.

Use `Resources.bind` to sequence sorting and `ListCalls.lookupRun`, with no
extra entry tick for the nonrecursive `slow_select` wrapper. For `k<n`,
`lookupRun_cost_of_lt` gives `k+1` and `lookupRun_valid` gives the actual indexed
value. Thus the required equations and bounds are

```text
TslowSelect k xs = Tsort xs + (k+1) ≤ n²+3*n+1
TslowMedian xs = (n+1) + TslowSelect ((n-1)/2) xs ≤ n²+4*n+2.
```

The second requires nonempty `xs`. `SymmetricCosts.lengthRun_exact` supplies the
length call, again with no extra wrapper tick. The source's `47` bound for each
nonempty size-at-most-five chunk follows. The shared triangular insertion bound
would improve this to `30` (sort at most `21`, length at most `6`, median lookup
at most `3`), but that improvement does not replace the displayed source
`47`, `483`, or `19*n+54` obligations.

Every final short chunk is retained and is nonempty. The size-five bound uses
its actual length; it does not silently replace a group of length one through
four by a full group. A Lean `Option` implementation must also avoid accidentally
sorting a `List (Option α)` or dropping failed medians. Use the proved nonempty
chunk domains to obtain payload-valued median results. This can be handled by
private proof-carrying chunk/median results and the standard attached-list
mapping interface; proofs erase from the source observation. A new value-level
cleanup traversal is not free and must not be hidden behind an `Option` bridge.

`Resources.ListCalls.mapRun_cost` is the exact shared map theorem:
the sum of callback costs on the actual input chunks plus `m+1` traversal calls.
Consequently

```text
Tmap slowMedian chunks ≤ 48*m+1 ≤ 10*n+48.
```

The last inequality is natural ceiling arithmetic, not a statement that
`ceil(n/5)=n/5` or that all groups have size five.

## 5. Duplicate-aware pivot balance

For a nonempty list of length `s`, the lower median has

```text
L(ys,median ys) ≤ (s-1)/2
G(ys,median ys) ≤ s/2.
```

Derive these from the general rank/count bridge, with natural division and
subtraction. They hold with repeated values. For either orientation `R = (<)`
or `R = (>)`, and `m` chunk medians, the number of medians related to the pivot
is **at most** `m/2`. The PDF's strict-half inequality is false; see section 10.

For the chunk-count proof, list sums and `countP` suffice; no new multiset
framework is necessary. Flattening gives

```text
countP (fun x => R x p) xs
  = sum (chunks.map (fun ys => countP (fun x => R x p) ys)).
```

Induction from `countP_append` proves this equality if the exact flatten-count
lemma is not already imported. Split the sum according to `R (median ys) p`.
A related-median chunk contributes at most `5`. An unrelated-median chunk's
related elements are a subset of those related to its own median, hence at most
`floor(length ys/2) ≤2`. Both orientations follow from linear-order laws;
there is no distinctness argument. Therefore

```text
strictSide ≤ 2*m + 3*(m/2),    m=(n+4)/5.
```

The final scalar inequality can be proved entirely in natural arithmetic:

```text
2*((n+4)/5) + 3*(((n+4)/5)/2) ≤ (7*n+39)/10.
```

The right side is exactly `⌈(7:ℝ)*n/10+3⌉₊`; bridge once using the ceiling
characterization. This proves Theorem 3.6 in the source's form while avoiding
unnecessary real casts inside the combinatorial proof. Constant-denominator
division is a suitable arithmetic goal for `omega`, after checking the precise
normal form. This is a proposed proof route, not a claim that it has compiled.

## 6. Construct the nested recursion without circular correctness

The recursive source branch first selects the lower median of the chunk medians
using **the same algorithm**. It then makes at most one strict-partition
recursive call. `runWith` and its fuel adequacy are useful semantic precedents,
but taking an opaque pivot policy in that executor does not account for this
nested pivot computation. Neither `selectWith_policy` nor equality to
`sortSelect` transports its cost.

Use well-founded recursion on the input length. A compact constructive route
is a private result certificate containing only what termination needs:

```text
successful returned values belong to the input;
a valid requested rank produces a successful result.
```

The public observation can remain `Measured (Option α) Nat`; the certificate
belongs to the construction/proof, not a second public selector interface.
A proof-domain `Fin xs.length` worker is another legitimate realization, but
its optional boundary adapter must preserve the counted length evaluation.

In a non-base call `n>20`, chunk count `m=(n+4)/5` satisfies `0<m<n` and
`(m-1)/2<m`. The first recursive call therefore terminates and returns a member
of `ms`. Each chunk median is a member of its nonempty chunk, and flattening
recovers `xs`, so this pivot belongs to `xs`. Now `partition_strict_sizes`
justifies both possible strict recursive calls. Branch arithmetic gives their
valid ranks:

```text
k < length ls                                  in the left branch;
k - length ls - length es < length gs           in the right branch,
```

using `k<n` and `partition_lengths`. None of these termination arguments needs
the sharp 70% balance theorem. Full `RankedAt` correctness is proved afterward
by well-founded induction and the existing partition semantic contract. This
separates elementary membership needed for construction from the stronger
order-statistic property, avoiding the circular claim that an unproved
recursive algorithm chooses a correct median.

An optional invalid-rank guard may return `none`, but use the length already
evaluated at the source entry. Do not add a second measured length pass for the
validity check. This guard's invalid-input behavior is an explicit Lean
totalization, not a specified HOL out-of-bounds value. The book's cost upper
bound remains restricted to valid ranks. Empty-payload types need no chosen
element.

## 7. Exact source costs and the scalar recurrence

Each `mom_select` entry is charged once. Let `t=partition3 p xs`, with lengths
`nl,ne,ng`. After nonempty chunks, `ms`, and pivot rank `i=(m-1)/2` have been
computed, preserve this recurrence, up to associativity/commutativity of Nat
addition:

```text
Tmom k xs = 1 + Tlength xs + TslowSelect k xs                 if n≤20;

Tmom k xs = 1 + Tlength xs + Tchop 5 xs + Tmap slowMedian chunks
  + Tmom i ms + Tpartition p xs + Tlength ls
  + (if k<nl then Tmom k ls
     else Tlength es +
       (if k<nl+ne then 0 else Tmom (k-nl-ne) gs))            if n>20.
```

The first recursive call occurs once. The equal-block length is evaluated only
after the left test fails. Returning the pivot adds no recursive-selection
call or lookup. The three partition lengths need not all be computed. These
details materially distinguish the book's count from an eager implementation
that computes all lengths or calls the old indexed-equal dispatch literally.

Define a natural scalar majorant using integer arithmetic:

```text
A n = (n+4)/5
B n = (7*n+39)/10
F n = if n≤20 then 483 else F (A n) + F (B n) + 19*n+54.
```

Prove `A n<n` and `B n<n` for `n>20` before defining `F`. Then establish
`483≤F n` by its induction principle and `Monotone F` by strong induction on
the larger argument. The latter uses monotonicity of `A` and `B` and their
strict decrease above the cutoff. A cost comparison to an upper bound on a
child's length **requires** this monotonicity; it is not implicit in the
definition of `F`.

For `k<n`, prove `Tmom k xs≤F n` by well-founded induction on `n`:

1. The base bound is `n²+4*n+3≤483` for `n≤20`.
2. The first recursive input has length `A n` and valid median rank.
3. Either strict child has size at most `B n` by the pivot balance theorem;
   combine its induction hypothesis with monotonicity of `F`. The equal branch
   contributes zero second-recursion work.
4. The remaining source calls have upper bound `19*n+54`: mapped medians at
   most `10*n+48`, chop at most `5*n+1`, and the other length/partition/entry
   work at most `4*n+5`. The last estimate uses the valid but deliberately
   coarse individual bounds `nl≤n`, `ne≤n`, matching the printed constants.

Sharper bounds are possible, but are additional results. They must not silently
change the source recurrence being covered.

## 8. Prove the complete affine bound, using existing rounding and growth APIs

Mathlib **does** have the full `AkraBazziRecurrence` API in
`Mathlib.Computability.AkraBazzi.SumTransform` and
`Mathlib.Computability.AkraBazzi.AkraBazzi`. Its inspected main theorems are
`isBigO_asympBound`, `isBigO_symm_asympBound`, and `isTheta_asympBound`.
The structure requires a finite nonempty branch set, positive branch weights,
strict contractions, nonnegative polynomially growing real toll, positive
base values, decreasing recursive sizes, and an `o(n/log²n)` perturbation law.
Its conclusion uses the critical exponent and an asymptotic sum transform.
The file still lists power-toll specializations as future work.

That result could eventually analyze this positive `F`, with branch weights
`1,1`, contractions `1/5,7/10`, and cutoff `21`. It is **not** a direct match
for Theorem 3.9: the latter permits arbitrary real base values, signed offsets
`b,d`, arbitrary real `C2`, and requires only `C1≥0`. Simplifying the full
Akra–Bazzi asymptotic sum and recovering an all-input affine bound would add
work. Do not introduce another general Akra–Bazzi framework to avoid those
existing APIs; add the small affine-induction lemma that the book actually
states, in the existing resource-growth domain.

Its exact target is:

```text
f : Nat → Real,
0<a, 0<c, a+c<1, 0≤C1,
∀ n>n0, f n = f ⌈a*n+b⌉₊ + f ⌈c*n+d⌉₊ + C1*n+C2
  ⇒ ∃ C3 C4 : Real, ∀ n, f n ≤ C3*n+C4.
```

No positivity of `f` or `C2` belongs in this theorem. It is a one-sided affine
bound; for arbitrary signed `f` it alone is not a norm-based `IsBigO` theorem.

Use `Nat.ceil` from `Mathlib.Algebra.Order.Floor.Defs/Semiring`; its FloorRing
instance already agrees with integer ceiling followed by `Int.toNat`.
`Nat.ceil_le`, `Nat.le_ceil`, `Nat.ceil_mono`, and `Nat.ceil_lt_add_one` are
the needed basic facts. For negative offsets, first replace `b,d` in upper
bounds by `b'=max 0 b`, `d'=max 0 d`; the affine arguments with those offsets
are nonnegative, so the natural-ceiling upper bound applies.

Choose a natural `N≥n0` with `N>(b'+d'+2)/(1-a-c)`. Let `C4` be the maximum
of `f` on the nonempty finite interval `0..N`, using standard finite extrema.
Choose

```text
C3 = max (C1/(1-a-c))
  ((C1*N+C2+C4)/((1-a-c)*N-b'-d'-2)).
```

The denominator is positive; `C3≥0` and
`C3*(1-a-c)-C1≥0`. The threshold also makes both natural-ceiling children
strictly smaller than `n` whenever `n>N`. Strong induction then gives

```text
f n ≤ C3*(a*n+b'+1) + C4 + C3*(c*n+d'+1) + C4 + C1*n+C2
    ≤ C3*n+C4.
```

The final step uses the nonnegative slope and its value at `N`; a **strict**
slope is unnecessary. `C4` may be negative in the real theorem. For natural
`f`, cast the recurrence to Real, then round the resulting constants upward
with natural ceilings to obtain natural constants. Instantiate at
`a=1/5`, `b=0`, `c=7/10`, `d=3`, `C1=19`, `C2=54` to obtain

```text
∃ C3 C4 : Nat, ∀ xs k, k < xs.length →
  (momRun k xs).2 ≤ C3*xs.length+C4.
```

This uniform statement is the required full linear source-cost theorem.
`Resources.isBigO_of_nat_bound` from `Applications/Resources/Growth.lean`
then supplies the scalar asymptotic corollary for `F`: for `n≥1`,
`F n≤(C3+C4)*n`. Families of valid inputs/ranks can consume the same bound.
There is no need to invent a worst-case supremum over an infinite payload type
merely to state the chapter's theorem.

## 9. Remaining exercises and connected evidence

The main selector does not discharge the exercises automatically. Their
minimal construction/proof routes are as follows.

| Inventory IDs | Concrete remaining work |
|---|---|
| C03-047–048,050 | A single-pass tail-recursive minimum accumulator and a second-occurrence selector; preserve repeated minima. Relate the actual second-occurrence implementation to the fixed-rank algorithm, as the exercise requests. |
| C03-049,051 | Maintain the smallest `k+1` values in a sorted bounded accumulator during one input traversal. Use existing ordered insertion and `take`; prove the prefix invariant and charge the bounded accumulator work. Retain the source bound `C1*k*n+C2*n+C3*k+C4`, including `k=0`. |
| C03-052 | For distinct integer input and valid `k,i`, construct a replacement at `i` that changes the selected value. Use occurrence ranks and checked update laws. This sensitivity theorem supports, but is not itself a complete machine/query lower-bound model. |
| C03-053–054 | Pad with input extrema to move rank `k` to the lower median: `A=max(0,n-1-2*k)` minimum copies and `B=max(0,2*k+1-n)` maximum copies. Prove odd result length at most `2*n-1`, central rank `k+A`, and duplicate-aware correctness. Count extrema search, lengths, padding, and appends. |
| C03-055 | Prove least actual cutoff `1`: a singleton recurses to itself at cutoff `0`; every larger input has a strictly smaller median list at cutoff `1`. The separate coarse scalar recurrence first strictly decreases for all `n≥14`, since `B 13=13`; minimum safe scalar cutoff is `13`. Cutoff `20` supports the printed simple `483` base, without asserting an undocumented author motive. |
| C03-056 | The explicit infinite family below proves strict failure of an exact 70% bound without the additive rounding allowance. |
| C03-057–058 | For fixed positive chunk size `l`, with `q=l/2`, retain `strictSide≤q*m+(l-q)*(m/2)`. The resulting fractional sum is `1/l+(l+floor(l/2))/(2*l)`, below `1` exactly when `l-floor(l/2)>2`: odd `l≥5` and even `l≥6`. Prove sufficient linear cases with offsets/cutoffs; equality at `l=3,4` is a failure of this sufficient argument, not a universal impossibility result for other algorithms. |

For Exercise 3.7 define, for every `i:Nat`,

```text
f i = flatten (replicate i [0,0,0,1,1] ++
               replicate (i+1) [1,1,1,1,1]) ++ [0].
```

The chunks have exactly `i+1` zero medians and `i+1` unit medians, so the lower
median of medians is `0`. Their input has length `10*i+6` and greater count
`7*i+5`; therefore `10*(7*i+5)-7*(10*i+6)=8>0`. Lengths strictly increase.
The final singleton matters. Source `chop_append`/`chop_concat` suggest the
small chunk alignment lemmas needed; these can be proved from the standard
adapter's source recursion. This is an analytical construction awaiting Lean
proof, not a finite-test substitute for the universal exercise.

### Suggested connected examples

The following numerical targets were independently recomputed from the exact
source recurrence in a small local Python model. They have **not** been checked
by Lean and should become focused examples only when the implementation exists.

| Input and zero-based rank | Result | Exact call count | Why this case matters |
|---|---:|---:|---|
| `[7]`, rank `0` | `7` | `7` | Entry, length, insertion, and lookup conventions all meet at the smallest valid input. |
| `List.range 20`, rank `19` | `19` | `83` | Last valid rank at the cutoff, with best-case insertion. |
| `(List.range 20).reverse`, rank `19` | `19` | `273` | Same result, different exact work; the source base bound remains `483`. |
| `List.range 21`, rank `0` | `0` | `269` | First recursive size, last singleton chunk, left branch. |
| `List.range 21`, rank `12` | `12` | `231` | Pivot equals requested value; equal length charged, no second selection call. |
| `List.range 21`, rank `20` | `20` | `266` | Right-rank subtraction and selected recursive call. |
| `replicate 21 4`, any valid rank | `4` | `239` | Duplicate collapse, empty strict partitions, and no `Nodup` requirement. |

For `n=21`, the five medians are `[2,7,12,17,20]`, pivot `12`; chopping costs
`58` and mapping slow medians costs `92`. The scalar majorant is
`F 21=F 5+F 18+19*21+54=1419`, deliberately much larger than these executions.
The empty case should test the chosen total `Option` boundary, with no claimed
source valid-rank cost. If the unguarded optional lookup extension is used, the
literal base sequence has work `4`; a cached invalid-rank guard has a different
explicit extension and should not be forced to match that number.

Add one symbolic consumer combining `RankedAt`, the affine bound, and a
noninjective monotone map. It should show that semantic transport may merge
values without losing correctness, while making no claim that the changed
input has equal measured work. These clients demonstrate composition beyond
literal `rfl` recurrence checks.

## 10. Source corrections that must stay visible

1. The weak replacement `G≤n-k` for (3.1)'s strict `G<n-k` is insufficient:
   `[0,2]`, rank `1`, candidate `1` passes the weak inequalities but is not the
   selected value. Retain the strict bound.
2. The displayed strict-half bound on p.37 is false. For `List.range 10`,
   chunk medians `[2,7]` have lower median `2`; one median is greater, while
   `m/2=1`. The companion theory correctly uses `≤m/2`.
3. The general recurrence contracts by coefficients `a,c`; `b,d` are offsets.
   The p.41 prose's coefficient letters must be corrected. A converse to the
   displayed sufficient theorem needs its own positivity/model hypotheses;
   do not silently claim it follows from Theorem 3.9's one-sided conclusion.
4. The p.43 constant choice guarantees `C3≥C1/(1-a-c)`, not strict `>`.
   With zero function/toll/offsets and `a=c=1/4`, the stated maximum can be zero.
   The non-strict inequality suffices, as in the pinned theory.
5. Even length means two central occurrences, which can have the same value;
   `[1,1]` is the minimal example. The lower-occurrence convention is exact.
6. The equal-block singleton-set assertion needs nonemptiness. An arbitrary
   pivot `2` for `[1]` has no equal entries; the reached middle branch supplies
   the missing premise.
7. Minimum pivots give a quadratic worst-case family on distinct inputs when
   repeatedly selecting a far rank, not quadratic work for every input/rank.
   Rank zero or an all-equal input can stop immediately.

## 11. Proposed module boundaries and implementation order

Keep domain ownership explicit and use existing abstractions rather than a
book-wide wrapper namespace:

| Placement | Responsibility |
|---|---|
| `Applications/Selection/Rank.lean` and `Consumers.lean` | General count/rank equivalence, median weak bounds, existing public-index bridges. No resource imports. |
| A small `Applications/Sequences/Chunks.lean` if the adapter needs a public name | The standard `splitLengths` adapter, positive source equations, flatten/membership/length and alignment laws. No order or cost assumptions. |
| `Applications/Selection/MedianOfMedians.lean` | Mathematical pivot and its count balance, consuming rank/chunk laws. No duplicate sort, partition, or rank specification. |
| `Applications/Resources/ListCalls.lean` or a small importing `Chunks.lean` in that resource domain | Measured source chunk recursion and bridge to the sequence adapter; keep unrelated list/count APIs small. |
| `Applications/Resources/Selection.lean` | One-pass partition realization, measured insertion baseline clients, the nested selector, value/rank correctness and exact source-cost equation. Split only at a real dependency boundary if the file becomes unwieldy. |
| Existing `Applications/Resources/Growth.lean` or a focused importing `AffineRecurrence.lean` | The reusable two-branch affine induction lemma and natural specialization; no full new Akra–Bazzi framework. |
| Selection resource bounds and `Examples/SelectionCosts.lean` | Scalar `F`, its monotonicity, uniform affine theorem, and connected clients. |

Import the existing selection, sorting, measured/call-count/list-count modules
and the specific standard list/rounding files needed. The elementary proof does
not require importing the full analytical Akra–Bazzi development. Keep the
real-arithmetic growth result out of value-only selection modules.

The smallest useful order is: rank/count bridge and standard chunk adapter;
measured helper bridges; duplicate-aware pivot bounds; member-certified nested
construction and correctness; exact recurrence and `F`; affine recurrence and
uniform linear theorem; then the exercises and the separately retained
probabilistic obligations. Proofs should expose valid-domain assumptions and
the actual execution path at every transition. None of the proposed names or
analytical calculations in this plan are an accepted theorem until the normal
conaled checks and independent statement review have completed.
