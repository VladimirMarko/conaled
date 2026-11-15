# Sorting cost lemmas: pinned reuse reconnaissance

2026-11-02. **Read-only preparation, not implementation or chapter acceptance.**
Signatures were checked in provider source; no Lean invocation or new formal
proof was attempted. The derived arguments below remain implementation obligations.
This note follows `specs/1003-Sort.md` and
`source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md`; their identities appear below.

Inspected conaled HEAD: `1da24c77d10fe03296dbf117e4249283139f5021`.
Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Core: `leanprover/lean4:v4.35.0` from `lean-toolchain`.
VFA: version 2.1, release `2026-08-24 10:11`; source recurrences are
`Sort.v:30–40` and `Merge.v:47–54`, not later moving website versions.

## 1. Triangular upper bounds without division

Write `T(n) = ∑ i ∈ Finset.range n, i` as mathematical notation in this note.
`Finset.sum_range_succ` gives `T(n+1) = T(n)+n`; the exact existing theorem
`Finset.sum_range_id_mul_two` gives **`T(n)*2 = n*(n-1)`**, including `n=0,1`.
Thus induction from `C(0)=0` and `∀ n, C(n+1) ≤ C(n)+n` proves
`C(n) ≤ T(n)`, then multiplication by two and commutation give
`2*C(n) ≤ n*(n-1)`. Equality recurrences give equality. This route avoids
division and truncated-subtraction manipulations inside the induction.
`Finset.sum_range_id` supplies the divided formulation afterward if desired.
These are proposed deductions, not names of an existing recurrence solver.

For actual insertion sort, establish the stronger input-indexed facts first:
the measured insertion's comparison count is at most its input length;
sorting a cons adds that insertion count to the tail's measured count;
and the sorted tail has the original tail's length. The last fact can reuse
`List.length_insertionSort` only after the source/value-erasure bridge.
Structural induction then supplies the triangular bound for every input.
A polynomial defined independently of execution is only a specification.

## 2. A reachable descending witness at every size

Let `D(n) = (List.range n).reverse` as note notation. Existing range/reverse
facts give its length, membership `x ∈ D(n) ↔ x<n`, permutation with
`range n`, and strict descending order. `range_succ` and `reverse_append`
yield `D(n+1)=n::D(n)`. These establish an actual family, with no existence
assumption or finite-machine representability claim.

After the exact source bridge, `perm_insertionSort`, `reverse_perm`,
`pairwise_insertionSort`, and `pairwise_le_range` identify the sorted value
as `range n` via `Perm.eq_of_pairwise'`. Antisymmetry is available for Nat;
this argument must not be transferred unchanged to distinguishable payloads
ordered only by a noninjective key.

The missing operational lemma is substantive: when every member `x` of a
list satisfies `x<a`, the **actual measured** source insertion of `a` takes
every false `a≤x` branch, returns `xs ++ [a]`, and counts `xs.length`
comparisons. Apply it to `a=n`, `xs=range n` to derive the witness equality
recurrence. Value permutation alone says nothing about these branch counts.
Empty/singleton witnesses have zero comparisons. Ascending and all-equal
inputs provide contrasting early-stop cases, not further quadratic witnesses.

## 3. Alternating halves and logarithmic depth

VFA's split handles zero, one, and two leading elements separately and sends
alternating positions to the two outputs. Prove from that recursion that for
input length `n` the lengths are `a=(n+1)/2` and `b=n/2`, that `a+b=n`, and
that `b≤a`. Two-step list induction and `Nat.add_div_right` at divisor two
give a direct arithmetic route. For `n≥2`, `Nat.add_pred_div_lt` gives `a<n`;
then `b<n`. No verified alternating-split length theorem was found in the
inspected providers; this remains a source-specific obligation.

Core `List.MergeSort.Internal.splitInTwo` has exactly those length indices,
but its implementation uses **contiguous** `splitAt`. It does not prove the
VFA split's value, permutation, stability, or traversal count. Its matching
sizes do not permit replacing the source algorithm.

Prefer `h(n)=Nat.clog 2 n` for the size argument. For `n≥2`,
`clog_of_two_le` gives `h(n)=h((n+1)/2)+1`; monotonicity bounds both child
depths by the ceiling-half depth. If an actual measured cost has zero
zero/singleton base charges and satisfies
`W(xs) ≤ W(left)+W(right)+k*n`, these facts support an induction to
`W(xs) ≤ k*n*h(n)`. First prove the split sizes, length-preserving recursive
values, and the combined split/merge/local-overhead bound `k*n`. Positive
base charges need an explicit additional bound; handle the empty case
separately. This is a proof plan, not a proved mergesort complexity theorem.

`Nat.log_div_base` and core `Nat.log2_def` concern floor division, so they
cannot silently account for the odd-size ceiling child. `Nat.size` is bit
length: `size (2^n)=n+1`, while `clog 2 (2^n)=n`. Its power bounds and
bits-length theorem are reusable alternatives, but any size/log/depth bridge
needs its own rounding and zero-case proof.

## 4. Existing resource seam and remaining limits

Use `Resources.Measured (List α) Nat`, or `Nat × Nat` observations to separate
comparisons from constructor requests; compose with the existing `bind`.
Prove first-projection erasure to the source recurrence and then the independent
cost statements. `bind_erases` composes existing erasure proofs.
`Resources.run` executes a left-fold state history: using it for this source's
tail-first/right-fold sort requires a proved reversed-input/recursion bridge.
It is not automatically the source execution order.

After proving a count bound, `Resources.isBigO_of_nat_bound` transports it
to real-cast asymptotics. It does not establish the count bound itself or turn
a natural logarithm proxy into an unproved real-log equivalence.
No new cost framework is needed. Comparator bit costs, physical sharing,
allocation, GC, backend substitutions, and wall-clock performance remain
separate realization claims. Preserve the Sort plan's four-comparison versus
five-literal-constructor distinction. No source algorithm, Lean file, cache,
configuration, ticket, or previous note was modified in this reconnaissance.

## Verified signature table

Implicit types/universe binders are suppressed; section hypotheses are expanded.
`r,R : α → α → Prop`; `xs,l,l₁,l₂ : List α`; arithmetic variables are Nat.
`M` below denotes an arbitrary additive result type only in the sum row.
Provider prefixes: `P` = `/workspace/scratch/0c54f2db1fdf/conaled`;
`ML` = `P/.lake/packages/mathlib/Mathlib`;
`LC` = `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data`.
Line pointers identify declarations, not proposed new names.

| Existing declaration | Signature / required hypotheses | Provider |
|---|---|---|
| `Finset.sum_range_succ` | `[AddCommMonoid M] (f : ℕ → M) (n : ℕ) : (∑ x ∈ Finset.range (n+1), f x) = (∑ x ∈ Finset.range n, f x) + f n` | `ML/Algebra/BigOperators/Group/Finset/Basic.lean:560`; generated by `to_additive` from `prod_range_succ` |
| `Finset.sum_range_id_mul_two` | `(n : ℕ) : (∑ i ∈ Finset.range n, i) * 2 = n * (n-1)` | `ML/Algebra/BigOperators/Intervals.lean:172` |
| `Finset.sum_range_id` | `(n : ℕ) : (∑ i ∈ Finset.range n, i) = n * (n-1) / 2` | `ML/Algebra/BigOperators/Intervals.lean:182` |
| `List.length_range` | `{n : Nat} : (List.range n).length = n` | `LC/List/Range.lean:162` |
| `List.range_succ` | `{n : Nat} : List.range (Nat.succ n) = List.range n ++ [n]` | `LC/List/Range.lean:182` |
| `List.mem_range` | `{m n : Nat} : m ∈ List.range n ↔ m < n` | `LC/List/Nat/Range.lean:244` |
| `List.pairwise_lt_range`, `List.pairwise_le_range` | `{n : Nat} : List.Pairwise (· < ·) (List.range n)`; respectively `(· ≤ ·)` | `LC/List/Nat/Range.lean:251,254` |
| `List.length_reverse` | `{as : List α} : as.reverse.length = as.length` | `LC/List/Lemmas.lean:2431` |
| `List.mem_reverse` | `{x : α} {as : List α} : x ∈ as.reverse ↔ x ∈ as` | `LC/List/Lemmas.lean:2440` |
| `List.reverse_append` | `{as bs : List α} : (as ++ bs).reverse = bs.reverse ++ as.reverse` | `LC/List/Lemmas.lean:2540` |
| `List.reverse_perm` | `(l : List α) : l.reverse.Perm l` | `LC/List/Perm.lean:174` |
| `List.pairwise_reverse` | `{l : List α} : l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a)` | `LC/List/Pairwise.lean:202` |
| `List.perm_insertionSort` | `(r) [DecidableRel r] (l) : (List.insertionSort r l).Perm l` | `ML/Data/List/Sort.lean:113` |
| `List.mem_insertionSort` | `(r) [DecidableRel r] {l} {x : α} : x ∈ l.insertionSort r ↔ x ∈ l` | `ML/Data/List/Sort.lean:117` |
| `List.length_insertionSort` | `(r) [DecidableRel r] (l) : (List.insertionSort r l).length = l.length` | `ML/Data/List/Sort.lean:121` |
| `List.pairwise_insertionSort` | `(r) [DecidableRel r] [Std.Total r] [IsTrans α r] : ∀ l, List.Pairwise r (List.insertionSort r l)` | `ML/Data/List/Sort.lean:218` |
| `List.Perm.eq_of_pairwise'` | `{r} [Std.Antisymm r] {l₁ l₂} : List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂ → l₁ = l₂` | `ML/Data/List/Sort.lean:303` |
| `Nat.add_div_right` | `(x : Nat) {z : Nat} (H : 0 < z) : (x+z)/z = x/z + 1` | `LC/Nat/Div/Basic.lean:325` |
| `Nat.div_le_div_right` | `{a b c : Nat} (h : a ≤ b) : a/c ≤ b/c` | `LC/Nat/Lemmas.lean:920` |
| `Nat.add_pred_div_lt` | `{b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n+b-1)/b < n` | `ML/Data/Nat/Log.lean:300` |
| `Nat.clog_of_right_le_one` | `{n : ℕ} (hn : n ≤ 1) (b : ℕ) : Nat.clog b n = 0` | `ML/Data/Nat/Log.lean:351` |
| `Nat.clog_of_two_le` | `{b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : Nat.clog b n = Nat.clog b ((n+b-1)/b) + 1` | `ML/Data/Nat/Log.lean:412` |
| `Nat.clog_mono_right` | `(b : ℕ) {n m : ℕ} (h : n ≤ m) : Nat.clog b n ≤ Nat.clog b m` | `ML/Data/Nat/Log.lean:444` |
| `Nat.clog_le_iff_le_pow` | `{b : ℕ} (hb : 1 < b) {x y : ℕ} : Nat.clog b x ≤ y ↔ x ≤ b^y` | `ML/Data/Nat/Log.lean:386` |
| `Nat.clog_pow` | `(b x : ℕ) (hb : 1 < b) : Nat.clog b (b^x) = x` | `ML/Data/Nat/Log.lean:432` |
| `Nat.log_div_base` | `(b n : ℕ) : Nat.log b (n/b) = Nat.log b n - 1` | `ML/Data/Nat/Log.lean:279` |
| `Nat.log2_def` | `(n : Nat) : n.log2 = if 2 ≤ n then (n/2).log2 + 1 else 0` | `LC/Nat/Log2.lean:62` |
| `Nat.log2_eq_log_two` | `{n : ℕ} : Nat.log2 n = Nat.log 2 n` | `ML/Data/Nat/Log.lean:308` |
| `Nat.size_le`, `Nat.lt_size_self` | `{m n : ℕ} : Nat.size m ≤ n ↔ m < 2^n`; `(n : ℕ) : n < 2^(Nat.size n)` | `ML/Data/Nat/Size.lean:75,68` |
| `Nat.size_pow`, `Nat.size_eq_bits_len` | `{n : ℕ} : Nat.size (2^n) = n+1`; `(n : ℕ) : n.bits.length = n.size` | `ML/Data/Nat/Size.lean:94,100` |
| `Resources.Measured` | `(α : Type u) (C : Type v) := α × C` | `P/Applications/Resources/Measured.lean:13` |
| `Resources.bind` | `[Add C] (r : Resources.Measured α C) (f : α → Resources.Measured β C) : Resources.Measured β C`; value `(f r.1).1`, observation `r.2 + (f r.1).2` | `P/Applications/Resources/Measured.lean:17` |
| `Resources.bind_erases` | `[Add C] (f : α → Resources.Measured β C) (g : β → Resources.Measured γ C) (f₀ : α → β) (g₀ : β → γ) (hf : ∀ x, (f x).1 = f₀ x) (hg : ∀ y, (g y).1 = g₀ y) (x : α) : (Resources.bind (f x) g).1 = g₀ (f₀ x)` | `P/Applications/Resources/Measured.lean:40` |
| `Resources.run_state` | `[Zero C] [Add C] (step : ι → σ → Resources.Measured σ C) (is : List ι) (s : σ) : (Resources.run step is s).1 = is.foldl (fun t i => (step i t).1) s` | `P/Applications/Resources/Workload.lean:24` |
| `Resources.isBigO_of_nat_bound` | `(f g : Nat → Nat) (C N : Nat) (bound : ∀ n, N ≤ n → f n ≤ C * g n) : Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ)) (fun n => (g n : ℝ))` | `P/Applications/Resources/Growth.lean:10` |

## Source identities (SHA-256)

`W` = `/workspace/scratch/0c54f2db1fdf`; other prefixes are defined above.

| Input/provider | SHA-256 |
|---|---|
| `W/work-state/specs/1003-Sort.md` | `fcc06acf05245de79637600479006e3d4a98f8bdf85c2537f5e7451cf3042955` |
| `W/work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `W/reference/vfa/vfa/Sort.v` | `aeaf646d3b7e4dd88cb5d6dba9d35ae5714e5451c154d90de499bb09a32a7d33` |
| `W/reference/vfa/vfa/Merge.v` | `090c5afc3a95750336b8b57ed2169b8d77c790266f231bf096be55761c20378b` |
| `ML/Algebra/BigOperators/Group/Finset/Basic.lean` | `45b548e8d8491da4820c71eb29b0a2c92786f98e300d947e677f6fbe16e6f78a` |
| `ML/Algebra/BigOperators/Intervals.lean` | `01e871093ddfe48538ad95497747fe522f2debe51e99dc9bb6e72bfa462a711b` |
| `ML/Data/List/Sort.lean` | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |
| `ML/Data/Nat/Log.lean` | `66bb65d1a1cabeb2ee3d8c88c55fd3cf6e48e910ea40322173d79e5ed66a0c3e` |
| `ML/Data/Nat/Size.lean` | `ab4306e1e29d9b254dd41af7e206591130414598403577921c7877e9919c249b` |
| `LC/List/Range.lean` | `74561923c148bb19e8cbcfbbd30f81dcb1302bb395925e7d06d107eb90e6a29a` |
| `LC/List/Nat/Range.lean` | `06325fdc2c100a4b20eff48e227419259e0749eb82b156b17a1c57b35a5649e3` |
| `LC/List/Lemmas.lean` | `9365fb1c6da0313a4c73e8cf096377e69c28ece28d38290a0423e5f8cc1fdfdb` |
| `LC/List/Perm.lean` | `d91620e1c9767119095b48601266b8c5267ed4ab0afb7fe31a4780209b9751fb` |
| `LC/List/Pairwise.lean` | `fcc984c70a81216c178d42a858dea5e3640201023a9a4d2837e76f138fd9b0f4` |
| `LC/List/Sort/Basic.lean` (contiguous split, line 60) | `a100c2a753aae0dda38a6e3afaca64f7ea70f4eba73d007ac29b5889fbf842ac` |
| `LC/Nat/Div/Basic.lean` | `0c8fc51180b0d4fb6319e8a44acd7999f3a1b3aad21d8da5c0ad575914f9d120` |
| `LC/Nat/Lemmas.lean` | `c4530be5c96b507c13823378db43912a3ba577a2a23944ce222aaa7d193d2581` |
| `LC/Nat/Log2.lean` | `8a4f220b2ef46bf434e0bafd4274e9a897674d665f1863024c77e74ae16766d4` |
| `P/Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `P/Applications/Resources/Workload.lean` | `5db2ef8f7a504b33b4dfbb26ed39de1a194fa59568ba16702f3ba2359b46b4f5` |
| `P/Applications/Resources/Growth.lean` | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
