# Natural-run sorting: source invariants and future proof plan

Recorded 2026-11-02. Bounded, read-only source preparation within the existing
FDSA loop. Chapter 1 remains the strict prerequisite; Chapter 2 is queued.
This note neither freezes a new implementation unit nor supplies validation,
independent review, coverage acceptance, or permission to activate Chapter 2.
No Lean, Lake, project checker, hash helper, Git, cache, or gate was run here.
Only this previously absent research file was written.

The focus is C02-058–088, the natural-run application of Exercise 2.7
(C02-107), the relevant tail-pass exercise C02-105–106, and the already
retained operational qualifications C02-108–112. The existing
`chapter02-reuse-plan.md`, `mergesort-proof-plan.md`, and
`difference-list-cost-preflight.md` retain their scope. This note does not
duplicate top-down merge sort or quicksort planning.

## 1. Primary evidence and a retained provenance defect

All paths below are relative to `/workspace/scratch/845aa1048b05`.

| Source | Exact inspected scope and identity |
| --- | --- |
| `book-source/functional_data_structures_algorithms.pdf` | July 27, 2026 edition, printed pp.21–25 / PDF pp.27–31: §2.6, equations (2.21)–(2.32), Lemmas 2.7–2.8. Printed p.29 / PDF p.35: Exercises 2.6–2.7. Saved PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| `book-source/Natural_Mergesort.thy` | AFP **Efficient-Mergesort**, dated archive `https://isa-afp.org/release/afp-Efficient-Mergesort-2026-10-26.tar.gz`; archive member `Efficient-Mergesort/Natural_Mergesort.thy`. Author Christian Sternagel. The archive member's theory header, import, scanner and `ascP` definitions were read directly during this pass. Recorded archive SHA-256 `148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708`; theory SHA-256 `2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51`. |
| `book-source/Sorting.thy` | Isabelle `src/HOL/Data_Structures/Sorting.thy` at `f86f290225eebcc52c1ae7dba2e098f405f51c21`; SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. The actual `merge_adj`, `merge_all`, their correctness laws, and comparison recurrences are at declarations beginning on lines 220, 229, 243, 268 and 273. |
| `book-source/LeanListSort-{Basic,Lemmas}.lean`, `LeanList-{Basic,Lemmas,Pairwise}.lean` | Saved Lean 4.35.0 primary source copies; revision recorded in the earlier reuse plan is `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Only the ordinary merge/list APIs below are used in this plan. |
| `conaled/.lake/packages/batteries/Batteries/Data/DList/{Basic,Lemmas}.lean` | Actual local files, pinned in `conaled/lake-manifest.json` at `66e469188fe07963e5cf666c7d4433f45b8131c5`. |
| `conaled/Applications/Sorting/{Stable,Merge,SourceMerge}.lean` | Existing `KeySorted`, `Stable`, `StableSort`, `mergeBy`, source recurrence bridge, and precise merge assumptions. Source inspected, without a new validation claim. |
| `conaled-builder-costs/Applications/Resources/DifferenceListCosts.lean` | Uncompiled shared candidate `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8`, recorded core SHA-256 `567683626b9a46d07c465ceb44faaafc941e2dc1c83491b093599ca7f8c698a5`. `Rep`, `AppCost`, creation/application operations, seed-general build laws and DList bridges were read in full. This is pending reuse, not accepted Chapter 2 coverage. |

The SHA identities above are retained provenance from the existing inventory
and candidate handoff, not a newly run project integrity gate. The saved AFP
entry `book-source/Efficient-Mergesort-entry.html` explicitly lists
`Natural_Mergesort`, the dated download and the BSD license. Isabelle's
separate source license is BSD-3-Clause. Preserve the respective notices on
translation. The dated AFP archive postdates the book; matching recurrences
do not establish an exact July 2026 source revision.

**Documentation finding NR-P01, subsequently tracked by root as
XD01-DOC-001:**

- `fdsa-control/research/difference-list-cost-preflight.md`, lines 8–9,
  attributes `Natural_Mergesort.thy` to Isabelle revision `f86f290...`.
  Its retained original SHA-256 is
  `a0bd75c09ea1208c880dc87d5e8abe88be207c1e411b118519e7cf6237984232`.
- `conaled-builder-costs/docs/research/fdsa-difference-list-costs.md`, lines
  14–16 in the originally inspected candidate, repeats that attribution in
  its companion-theory paragraph. The original SHA-256 is
  `635f53c8823e2d6f0d54939b5966a90661e54c5861094bf70aa09bec9b7f43a1`.

The inspected natural-merge theory is the AFP archive member above. Its
header imports `HOL-Data_Structures.Sorting`; that dependency is the Isabelle
theory pinned at `f86f290...`. Those are distinct provenance identities.
Use the dated AFP archive/theory identity for the scanner, and the Isabelle
identity for the ordinary merge passes. Neither affected prior document was
edited by this preparation.

**Coordinator-supplied disposition after this file's initial write:** root
independently verified the AFP archive member bytes and committed a correction
to the builder documentation at
`62809ced86c561c7a6cce8b71e727177a3f17fb8`, parent `ffeaf8a...`. The reported
corrected note SHA-256 is
`fd01432541c9b27ad83def6192e4a3b75d6b77ae7490ec11a2bf665324f1246e`.
Root reports the Lean core, examples and reconstruction map unchanged, and
the original control preflight preserved byte-for-byte. The retained erratum
is `fdsa-control/reviews/difference-list-provenance-correction.md`;
implementation is recorded, with final confirmation pending. This author did
not review that new commit and makes no finding-closure or acceptance claim.

## 2. Preserve the scanner, including its restart boundary

The exact source algorithm is mutually recursive. For keyed clients, replace
each source comparison `b < a` by `key b < key a`, retaining full records.
Its important state convention is:

- In `asc a d ys`, the builder contains the already consumed prefix **before**
  the current element `a`. The final call is `d.apply [a]`.
- In `desc a acc ys`, `acc` stores the previously consumed descending prefix
  in reverse order. The current element is not yet in it; final emission is
  `a :: acc`.
- `runs (a :: b :: xs)` compares the first pair once, starts descending only
  on strict decrease, and supplies a singleton seed `[a]` or `singleton a`.
- A worker that stops on the next element `b` emits its completed run and
  restarts with **`runs (b :: bs)`**. It neither discards `b`, duplicates the
  previous current element, nor includes the failed boundary in both runs.
- Ascending continuation is `d.push a`, whose underlying function is
  `fun suffix => d.apply (a :: suffix)`. This is exactly the source
  composition `f ∘ List.cons a`, in that order.

The value implementation can use one mutually recursive scanner over existing
`Batteries.DList`; no new difference-list carrier or generic scanner framework
is needed. The raw-source contract is still quantified over every valid
function `f`, not only functions generated by this particular scanner.

Let `D f := ∀ xs ys, f (xs ++ ys) = f xs ++ ys`. Prove once:

```text
D f ↔ ∀ suffix, f suffix = f [] ++ suffix.
```

Forward: specialize `xs=[]`. Reverse: rewrite both sides and use associativity.
Thus `Batteries.DList.mk f h` is the source adapter for any `D f`; it retains
the actual function. Do not implement the adapter by evaluating `f []` and
rebuilding `ofList (f [])` on every scanner step. The standard extensional
`ofList_toList` theorem is a value fact, not a cost-preserving optimization.

The same minimal measure handles all mutual edges:

| Call | Natural measure |
| --- | ---: |
| `runs xs` | `xs.length` |
| `asc a d ys` | `ys.length + 1` |
| `desc a acc ys` | `ys.length + 1` |

Starting a worker decreases from `xs.length+2` to `xs.length+1`.
Continuation removes one element of the worker tail. Restart decreases from
`bs.length+2` to `bs.length+1`, even though it calls `runs (b::bs)`.
No measure uses the growing builder prefix or accumulator. No fuel, default
element, `Inhabited α`, payload equality, or quotient of executions is needed.

Value/permutation and comparison-count arguments need only the chosen
decidable branch relation; sortedness and the source specialization use the
order laws. A `LinearOrder` on keys is a straightforward source-faithful
specialization, without strengthening the existing generic merge APIs or
ordering the payloads.

## 3. Exact correctness invariants

Write `F xss := xss.flatten`, `p := f []`, and `S xs := KeySorted key xs`.
Use existing `List.Perm` and its multiset bridge, rather than a new
sorting-specification type. The mutual induction must retain all worker
parameters universally.

| Observation | Required worker invariant / target |
| --- | --- |
| Ascending permutation | `D f → (F (asc a f ys)).Perm (p ++ a :: ys)` |
| Descending permutation | `(F (desc a acc ys)).Perm (acc.reverse ++ a :: ys)`; reverse-permutation then gives the source's multiset of `a`, `acc` and `ys` |
| Initial permutation | `(F (runs xs)).Perm xs` |
| Ascending sorted blocks | `D f`, `S p`, and `∀ x∈p, key x ≤ key a` imply `∀ run∈asc a f ys, S run` |
| Descending sorted blocks | `S acc` and `∀ x∈acc, key a ≤ key x` imply `∀ run∈desc a acc ys, S run` |
| Initial sorted blocks | `∀ run∈runs xs, S run` |
| Ascending flattened length | `D f → (F (asc a f ys)).length = p.length + 1 + ys.length` |
| Descending flattened length | `(F (desc a acc ys)).length = acc.length + 1 + ys.length` |
| Initial flattened length | `(F (runs xs)).length = xs.length` |

These are the source's `mset_asc`, `mset_desc`, `mset_runs`, `sorted_asc`,
`sorted_desc` and length laws (`Natural_Mergesort.thy`, declarations at lines
81–93 and 133–135). The source multiset display orders its summands
differently; commutativity accounts for that difference, not a changed
chronological prefix.

For ascending continuation, `¬ key b < key a` supplies `key a ≤ key b`;
append the current element to the sorted prefix and transport its upper bound
by transitivity. Descending continuation prepends `a` to the sorted accumulator
and obtains the new lower bound from `key b < key a`. At a restart, only
within-run sortedness is needed: there is no cross-boundary ordering premise.
`F (runs xs)` need not itself be sorted before merging.

The source invariant is necessary for raw `f`: a valid builder may represent
an arbitrary prefix, including an unsorted one. For example, `f suffix =
[2,1] ++ suffix` is valid but `asc 3 f [] = [[2,1,3]]` is not sorted.
Even a sorted prefix `[2]` gives an unsorted `[2,1]` if the upper-bound premise
is dropped. Conversely, `D f` alone suffices for the permutation and length
claims; do not silently narrow these to reachable, sorted builder histories.

Each emitted run is nonempty for valid builders: `f [a] = p ++ [a]`, and a
descending emission begins with `a`. Thus:

```text
runs [] = [];                     runs [a] = [[a]];
runs xs = [] ↔ xs = [];
∀ run∈runs xs, run ≠ [];
length (asc a f ys) ≤ 1 + length ys;
length (desc a acc ys) ≤ 1 + length ys;
length (runs xs) ≤ length xs.
```

The worker output-count bounds do not count the size of the already supplied
prefix/accumulator. Indeed those two count bounds and nonemptiness of the
*outer* worker result do not depend on builder validity at all; the source
includes `D f` in some of its sufficient premises. Inner-run nonemptiness and
the flattened-length law do depend on validity. In particular, do not assert
one initial run for the empty input, or take a positive logarithm of a run
count before excluding it.

## 4. Stability requires a stronger descending history invariant

The existing contract is precisely

```text
Stable key input output :=
  ∀ k, output.filter (fun x => decide (key x = k))
       = input.filter (fun x => decide (key x = k)).
```

Use it for the **flattened scanner output**, then compose with stable merging
of the already sorted blocks. The appropriate mutual targets are:

- `Stable key xs (F (runs xs))`.
- For any `D f`, `Stable key (f [] ++ a :: ys) (F (asc a f ys))`.
  Prefix sortedness is not needed for this filter-preservation claim.
- `Stable key (acc.reverse ++ a :: ys) (F (desc a acc ys))` under
  `acc.Pairwise (fun x y => key x < key y)` and
  `∀ x∈acc, key a < key x`.

The last two strict conditions say exactly that `a :: acc` has strictly
increasing keys. They hold at every actual descending entry, are preserved
by continuation, and imply the weaker source sortedness hypotheses. For
each key, a strictly ordered block's filter has at most one element, so
reversal preserves that filtered record list. This supplies the descending
emission step; `List.filter_reverse` and `List.filter_append` do the transport.
One small local lemma about equal-key filters of a strict block suffices;
there is no need for a new run-provenance datatype or stability definition.

**Do not infer this claim from the source's weak descending invariant.** If
`acc=[(2,A)]`, `a=(2,B)` and `ys=[]`, both weak sortedness premises hold.
The chronological input is `[(2,A),(2,B)]`, while emission is
`[(2,B),(2,A)]`. That arbitrary worker is sorted and a permutation, but is
not stable. The real scanner never starts that descending state from a tie.

Likewise, replacing strict descent by nonincrease is not an innocuous branch
rewrite. Equal-key records must remain ascending or end a descending run.
Exercise 2.7 permits a selected collection of non-insertion algorithms; a
stable natural sorter is a useful additional client, but the exercise does
not claim that every tail-accumulator variant is stable.

For merge passes, use `mergeBy_filter key xs ys hx hy k`, whose result is the
left equal-key sublist followed by the right one. Prove that ordinary
adjacent passes preserve `Stable key (F xss) (F (merge_adj xss))` under
sorted-block hypotheses, then iterate. `mergeBy_stable` alone cannot repair
an earlier permutation of equal-key records by the scanner or the pass order.

## 5. The exact comparison observation

Keep the book's comparison-only tariff separate from function entry,
construction, materialization, key evaluation and machine time. A worker
with a nonempty tail pays one for testing the next pair, regardless of which
branch is chosen. Empty worker tails and initial empty/singleton lists pay
zero. Negating the strict comparison in `asc` does not test a second pair.

Use existing `Measured`/`bind` for a measured scanner whose value projection
is the actual `runs`/worker value, and put the one-unit increment at that
comparison site only. A generic function-entry tick on every invocation
would count a different metric. The measured natural sorter must bind the
actual returned run list into the measured repeated merger, so its derived
cost equation is the source equation

```text
C_nmsort xs = C_runs xs + C_merge_all (runs xs).
```

There is a useful exact strengthening of `Natural_Mergesort.C_runs`,
`C_asc`, and `C_desc` (source lines 104–123):

```text
C_asc a ys  = ys.length;
C_desc a ys = ys.length;
C_runs xs   = xs.length - 1.       -- natural subtraction
```

Prove them simultaneously. Continuation gives `1 + bs.length`. Restart on
`b::bs` gives `1 + ((bs.length+1)-1)`, the same number. Starting a worker
adds the first pair's comparison. The empty and singleton cases both cost
zero; the expression must not be recast as a negative integer at length zero.
No sortedness or builder-cost premise is used by this comparison identity.

Thus a sorted **nonempty** input gives `runs xs=[xs]`, zero merge comparisons
and total comparison count `length xs-1`. Empty input has `runs []=[]` and
total zero. Strictly descending nonempty inputs also form one reversed run.
Weakly descending inputs with ties need not form one run. The source's
linear best-case conclusion is asymptotic; a positive linear lower bound is
not asserted at lengths zero or one. For `n≥2`, `n-1≥n/2` supplies the usual
comparison lower estimate if needed.

## 6. Merge only the interface needed by natural runs

Reuse the future common bottom-up pass and the measured merge from
`mergesort-proof-plan.md`; do not create another merge implementation here.
For arbitrary lists of runs, including empty inner lists, retain:

```text
length (merge_adj xss) = (length xss + 1) / 2;
length (F (merge_adj xss)) = length (F xss);
C_merge_adj xss ≤ length (F xss);
C_merge_all xss ≤ length (F xss) * Nat.clog 2 (length xss).
```

The first identity gives strict descent of the run count when it is at least
two. The final bound needs no sortedness hypothesis: it uses merge length
and its comparison upper bound, not sortedness. Natural-run correctness
separately supplies the sorted-block premises for the value theorem.

For the final bound, let `m=length(F xss)`, `r=length xss`, and
`q=(r+1)/2`. One pass costs at most `m`, preserves `m`, and leaves `q` runs.
For `r≥2`, the existing `Nat.clog_of_two_le` specializes to
`Nat.clog 2 r = Nat.clog 2 q + 1`. The induction closes with
`m + m * Nat.clog 2 q`. Handle `r=0` and `r=1` separately, both with cost zero.
The exact pinned logarithm APIs and the positive-input real-ceiling bridge
are already documented in `mergesort-proof-plan.md`, §§7 and 9; reuse them.

For natural scanning, `m=n` and `r≤n`, giving the sharper comparison bound

```text
C_nmsort xs ≤ (n-1) + n * Nat.clog 2 r
             ≤ n + n * Nat.clog 2 n.
```

Retain the printed integer/real logarithm version through its explicit
coercion bridge. The `n=0` case is proved by its algorithm equation, not by
assuming a positive logarithm domain. Empty inner lists are allowed by the
generic merger even though the real scanner does not generate them.

## 7. Deferred builder work and the remaining operational theorem

The stopped builder candidate supplies exact public statements in namespace
`Resources.DifferenceListCosts`:

| Declaration | Relevant contract |
| --- | --- |
| `Rep f prefix`, `AppCost f k` | Respectively value `prefix ++ suffix` and cost `k`, each quantified over **every** suffix |
| `compose_value`, `compose_cost` | Actual application of `g` first, then `f` at that returned value; cost `cost(g suffix)+cost(f(value(g suffix)))+1` |
| `pushRun_eq a f` | `(compose f (singleton a), 2)` for creation |
| `pushRun_rep`, `pushRun_appCost` | Prefix grows on the right by `[a]`; uniform application cost grows from `k` to `k+2` |
| `buildFrom_cost items f` | Construction observation `2 * items.length`, excluding the supplied seed's prior creation |
| `buildFrom_rep`, `buildFrom_appCost` | Prefix `prefix ++ items` and application cost `k + 2 * items.length` under the respective seed contracts |
| `toDList_apply`, `toList_toDList`, `toDList_pushRun` | Value bridges to existing DList application, materialization and fused push; no fused-push cost theorem |

For an actual ascending source run of length `r≥2`, the singleton seed is
followed by `r-2` compositional pushes, then application to `[last]`.
The candidate's tariff therefore predicts creation including the seed and
one application each equal to

```text
1 + 2*(r-2) = 2*r-3,   for r≥2.
```

This is a future scanner-to-builder correspondence, not a consequence of
extensional DList equality. Use `1+2*m` with `m=r-2`, or the division-free
successor identity `cost+3=2*r`, before simplifying natural subtraction.
At `r=2`, both observations are one; at `r=3`, both are three. Empty and
singleton initial inputs bypass that ascending-builder path. Applying a
builder to `[last]` is not the identity-seeded `build` program, and pushing
`last` before calling `toList` is a different measured program even though
its list value agrees.

An arbitrary valid raw `f` receives no application bound from `D f`. An
arbitrary measured seed can retain the weaker, explicit `Rep f p` and
`AppCost f k` contracts; its later worker bound must include `k`. The
candidate's existing padded-empty and shared-self-composition examples
already refute output-length bounds for arbitrary builders and bounds on
unfolded invocations by distinct closure-creation events. Reuse those cases;
do not duplicate a second builder theory or silently restrict the semantic
worker theorems to simple construction histories.

C02-112 still requires an observation over the **actual scanner**. The small
proof route is to bind the actual builder operations at the source branches,
keep their erasure theorem, and account separately for scanner entries,
descending cons, emitted outer-list cells and the chosen final dispatch.
There is only one recursive scanner successor per nonterminal invocation;
each consumes the same comparison boundary as §5. Thus scanner entries are
bounded by `n+1`. Actual ascending creation/application sums are bounded
linearly by the lengths of their disjoint runs, descending construction is
linear in its run lengths, and emitted run count is at most `n`. These facts
support `W_scan xs ≤ A*n+B` for an explicit fixed tariff. The exact constants
belong to that future tariff, not to this plan. On sorted input, merge-all's
singleton dispatch adds constant control work and no comparisons.

The book's language-dependent performance remark is not a verified claim
about Lean's runtime. Batteries' complexity comments likewise do not prove
the new observation. Constant-size closure capture, later invocation,
repeated independent materialization, and actual source scanner traversal
must remain distinguishable. The count bound for general merge phases is
not silently promoted to a machine-time theorem.

## 8. Exercise 2.6: cons-only pass with deliberately reversed run order

The exercise leaves the accumulator orientation open and explicitly does not
require equality with the ordinary pass. A minimal permissible future choice
is the following value recurrence, with the existing left-tie merge:

```text
adj2 acc []                  = acc
adj2 acc [xs]                = xs :: acc
adj2 acc (xs :: ys :: zss)   = adj2 (merge xs ys :: acc) zss
```

It is tail recursive in the pass and uses no append. The useful exact
*proof* equation is `adj2 acc xss = (merge_adj xss).reverse ++ acc`;
an append in a theorem is not an append in the executable pass.
Structural descent of `xss` proves termination. Derive the literal exercise
support statements:

```text
length (adj2 acc xss) = length acc + (length xss+1)/2;
multiset (F (adj2 acc xss)) = multiset (F acc) + multiset (F xss);
sortedBlocks acc ∧ sortedBlocks xss → sortedBlocks (adj2 acc xss).
```

Its comparison observation equals the ordinary pass observation for the
same `xss`, independently of `acc`: it merges the same pairs in the same
left/right orientation. With entry/cons work also observed, the pass has
linear control overhead in the number of run-list cells; comparison equality
alone would not justify an arbitrary costly implementation of its control.

Define `merge_all2` using this pass at empty accumulator and the same
empty/singleton stopping cases. Run-count descent, multiset, sorted-block
and flattened-length preservation give correctness and the same
`m * Nat.clog 2 r` comparison bound. They **do not** give the same complete
comparison count or keyed stability as ordinary `merge_all`.

For three singleton runs with distinguishable equal-key records `A,B,C`,
the ordinary first pass gives `[[A,B],[C]]`; the cons-accumulator pass gives
`[[C],[A,B]]`. The ordinary complete merge uses `1+2=3` comparisons and
returns `[A,B,C]`; the reversed variant uses `1+1=2` and returns `[C,A,B]`.
After forgetting payloads both return the same three equal keys. This is a
non-tautological witness that extensional ordinary correctness, equal pass
cost and the same complexity do not imply total-cost equality or stability.

If a later client specifically needs stable tail passes, an additional
order-restoration design and its own value/control observation can be proved.
That is not required merely to solve Exercise 2.6, and it should not change
the ordinary source pass used by natural mergesort. The book's premature
`merge_adj2`/`merge_all2` names on printed p.19 remain the already inventoried
source-label defect; prove both the intended basic laws and these literal
exercise laws, without assuming equality of the two passes.

## 9. Independent expected cases for later connected examples

These are hand-derived expectations from the displayed source recurrences,
not executed tests or accepted Lean examples. Each eventual example should
use the public scanner/merger value and observation theorems, not merely
prove an unrelated numerical identity. Letter suffixes distinguish records
whose keys may coincide.

| Input / call | Expected observation | Defect or boundary exposed |
| --- | --- | --- |
| `runs ([] : List Empty)` | `[]`, zero comparisons, zero runs | No payload inhabitant; do not invent an empty run |
| `runs [7]` | `[[7]]`, zero comparisons, one run | Singleton bypasses builders and merging |
| `runs [1,1,2,3]` | `[[1,1,2,3]]`, three comparisons, zero merge comparisons | Nondecreasing ties remain ascending; sorted best case |
| `runs [4,3,2,1]` | `[[1,2,3,4]]`, three comparisons, zero merge comparisons | Actual descending reversal; flattened input equality would be false |
| `runs [1,3,2,4]` | `[[1,3],[2,4]]`, scan three; merge three; total six | Failed boundary restarts at `2`; flatten is not yet sorted |
| `runs [(3,A),(2,B),(2,C),(1,D)]` | `[[ (2,B),(3,A) ],[ (1,D),(2,C) ]]`; scan three; merge three; result `[(1,D),(2,B),(2,C),(3,A)]` | Tie stops descent, and stable left-tie merge retains `B` before `C` across two runs |
| `runs [(3,A),(3,B),(2,C)]` | `[[ (3,A),(3,B) ],[ (2,C) ]]`, scan two | A weakly descending input need not be one source run |
| Raw `f suffix=[1,3]++suffix`, `asc 5 f [4,6]` | `[[1,3,5],[4,6]]`; flattened length five, run count two, comparisons two | Arbitrary valid raw builder and nonempty restart; no required construction history |
| Raw `f suffix=[2,1]++suffix`, `asc 3 f []` | `[[2,1,3]]`, comparisons zero | `D f` does not imply sortedness or impose the sorted-prefix invariant |
| Raw `desc (2,B) [(2,A)] []` | `[[ (2,B),(2,A) ]]`, comparisons zero | Weak source sortedness premises do not prove worker stability |
| `merge_all [[],[2],[],[1,3]]` | `[1,2,3]`, two comparisons; four input runs and total length three | Generic pass bound permits empty inner lists; actual scanner does not |
| Cons-only `adj2 [[9]] [[1],[3],[2]]` | `[[2],[1,3],[9]]`, pass comparison count one, three output runs | Accumulator suffix orientation and literal length formula |
| Complete ordinary/tail merges of `[[A],[B],[C]]`, all keys equal | Ordinary three comparisons / `[A,B,C]`; tail variant two / `[C,A,B]` | Same pass complexity is neither complete-cost equality nor stability |
| Actual ascending source run of length two / three | Builder creation and application each one / three in the declared compositional tariff | Singleton seed, final `[last]` suffix, and natural-subtraction domain |

The empty-inner-list merge case uses first-pass merges with an empty side,
each costing zero, followed by merging `[2]` and `[1,3]` with two comparisons.
The arbitrary accumulator example costs only the merge of `[1]` with `[3]`;
neither `[2]` nor the already supplied `[9]` is merged during that pass.

## 10. Exact library reuse and smallest future implementation steps

Relevant existing signatures, rather than proposed new abstractions:

- `Batteries.DList.invariant : ∀ l, apply l = apply [] ++ l`;
  `singleton`, `push`, and `apply` in `DList/Basic.lean`.
  `toList_push (x) (l) : toList (push l x) = toList l ++ [x]`,
  `toList_append`, and `ofList_toList` in `DList/Lemmas.lean`.
- `List.cons_merge_cons cmp a b xs ys` is the actual conditional merge
  equation; `List.merge_perm_append cmp` and `List.length_merge cmp xs ys`
  do not require comparison laws. The pinned declarations are in
  `book-source/LeanListSort-Lemmas.lean` at lines 149, 260 and 161.
- `List.pairwise_append`, `List.pairwise_reverse`, `List.Pairwise.filter`,
  `List.pairwise_map`, `List.filter_append`, `List.filter_reverse` and
  `List.filter_flatten` supply the ordinary list transports. The reverse
  pairwise law reverses the relation; it must not be read as saying that
  reversing an ascending list remains ascending.
- `Applications.Sorting.mergeBy_perm`, `mergeBy_sorted`, `mergeBy_filter`,
  `mergeBy_stable` and `mergeBy_spec` supply the existing local contracts.
  In particular `mergeBy_filter` requires both input blocks key-sorted,
  `Std.IsPreorder` and decidable equality on keys; it preserves complete
  records and needs no equality or order instance on payloads.
- `Resources.ListReversal.appendRun_exact xs ys` returns
  `(xs++ys, xs.length+1)` and `accumulator_exact xs acc` returns
  `(xs.reverse++acc, xs.length+1)` for the named measured realizations.
  These connect C02-109's repeated-append triangular subcost versus
  cons-and-reverse; they say nothing about the runtime of arbitrary list
  functions. That already retained obligation is not replaced by DList work.

Smallest dependency-respecting implementation order, after Chapter 1 and the
applicable future scope/review decisions:

1. Reuse the one measured merge and ordinary adjacent/repeated passes from
   the Chapter 2 common work. Prove their arbitrary-run-count interface in
   §6, including empty cases; no top-down sorter is needed by the scanner.
2. Implement the literal mutual scanner with existing DList, the raw `D`
   adapter, and the one tail-length termination measure. Prove worker
   permutation, sorted-block, length, nonempty-run and run-count statements
   together with their initial-list specializations.
3. Add the exact comparison observer and erasure to those same returned
   values. Derive the three exact scan counts, then bind the real run list
   into common measured merging and discharge Lemmas 2.7–2.8 and the sorted
   best case with explicit zero/log boundaries.
4. For a selected keyed natural-sort client, prove the strict descending
   history/filter lemma and the scanner's `Stable` property, then compose
   with stable ordinary passes. Keep arbitrary raw-worker correctness and
   the weak sortedness statements independently available.
5. Connect the stopped builder draft only after its applicable validation
   and integration. Prove singleton-seeded actual-run correspondence and the
   separately declared full scanner work bound; preserve C02-109's ordinary
   append/reverse comparison. This is the outstanding operational gap, not
   something supplied by `D f` or by `C_runs=n-1`.
6. Solve the cons-only tail-pass exercise with its own orientation invariant,
   correctness and complexity, retaining the equal-key counterexample to
   automatic stability/total-count transfer. Connect the cases in §9 to the
   new public statements during that future implementation.

The existing proposed placement remains sufficient:
`Applications/Sorting/NaturalRuns.lean`, common
`Applications/Sorting/BottomUp.lean`, and the corresponding observation code
under `Applications/Resources` if file size warrants the split. No new
sorting specification, DList type, writer type, executor, logarithm library,
or whole-language/runtime formalization is needed for these obligations.
All of the implementation and acceptance steps above remain future work.
