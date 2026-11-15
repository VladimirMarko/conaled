# Actual random-pivot quicksort: harmonic and growth consumer plan

Status: source-only preparation. No new Lean source, merge, ref, compiler, cache,
coverage or acceptance change is made by this plan. The implementation requires
the coordinator's release after the actual rank and numerical dependencies have
been inspected at their exact checked identities.

## 1. Fixed inputs and current validation boundary

The author worktree remains clean at
`c19a85f8f5e256e87b0001f3e98afb2c7c1b08cc` on
`work/fdsa-ch02-random-pivot`, with parent
`1f315fdbb40288d99921164bb3fd8afcbd756e58`.
The rank draft consists of exactly the two files below. Its author assessment,
all 30 public and seven private source claims, and the root's independent
coordinator source readback report no concrete mathematical finding. This is a
source assessment, not either independent acceptance review or a compiler pass.

| Exact source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/RandomQuickSortRank.lean` at `c19a85f8` | 393 | 19615 | `22960885c968620b957e7e2381baa8b887d9dc80a54fb72fe9644c3ace2890b4` |
| `Examples/RandomQuickSortRank.lean` at `c19a85f8` | 151 | 6427 | `a0f5fbd6b3d41cad08193a371228bede1b869a773608b21906e85f2848d747bf` |
| `Applications/Resources/RandomQuickSortMean.lean` inherited from `1f315fdb` | 335 | 16517 | `2c7976bf52a2dbed2eb6eb959055acc7ae0df8319c167f0128b63e5c482bd5d3` |
| `Applications/Resources/QuickSortMean.lean` at `012ff45e` | 215 | 9714 | `6ac46b57a39ad60eaae10d6b90ac4c46c9cbdc02d5caf214097b1e794d03794b` |
| `Examples/QuickSortMean.lean` at `012ff45e` | 68 | 2488 | `924ce55ee6af374b55cea67ee6f2da25997b5a81ad098e2e3789622bd793b904` |

The exact numerical commit is
`012ff45e3bd34a36b67e62a8cc2ee00125613e53`. I read its complete
215-line resource and 68-line example files, including every proof body: 283
lines in total. Both worktree hashes were checked against `git show` of this
immutable object; its worktree was clean and its HEAD matched that commit.
The numerical module assumes no probability or execution model.

The root has now reported that central nine-target attempt4 at `e4965499`
closed with aggregate exit1. The mean resource and example modules each built;
failures concerned root-owned XU02 and a natural sorting proof. Its closed log
has 21245 bytes and SHA-256
`10d22668f7040a1802fbac453a6c8880fe1482b663751055f780cdcf934e2df0`.
This paragraph records the coordinator's actual terminal report; it does not
replace the secured full/native evidence or claim an aggregate pass.

The root has merged exact rank `c19a85f8`, numerical/Tail additions and two
separate proof corrections into central
`c0440a99c2a503b7816a44367f7e4168378dbbf1` and started a recorded
12-target attempt5, including the rank pair's first compilation. No terminal
result, rank pass or rank elaborated-type pass has been supplied at this plan's
preparation boundary. Actual diagnostics take priority over implementing this
consumer. Any proof-only successor must be recorded explicitly before release;
neither the author nor a future consumer follows a moving branch implicitly.

The unchanged dependency restrictions include official Lean/Lake 4.35.0,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, the exact repository
pins, and the disclosed native adapter. The accepted Chapter 1 commit
`07e480f6ec9958d4975bb90151005b84f2907614` is preserved. No foundation
acceptance is supplied here for dependency
`f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.

## 2. Two-file boundary and import direction

Proposed new files only:

1. `Applications/Resources/RandomQuickSortGrowth.lean`.
2. `Examples/RandomQuickSortGrowth.lean`.

The resource imports `Applications.Resources.RandomQuickSortRank` and
`Applications.Resources.QuickSortMean`. An explicit
`Mathlib.Order.Filter.AtTopBot.Tendsto` import provides the inspected eventual
length interface for arbitrary filters. The numerical dependency already
provides the standard asymptotics definitions, real logarithms and harmonic
bounds. The example imports this resource. Keep imports specific; do not add a
root `Mathlib` import, new expectation framework or new execution definition.

The dependency direction is actual run -> actual finite means -> actual
rank/size recurrence -> this consumer <- probability-independent numerical
solver. The rank module must continue to have no harmonic import. The solver
must continue to have no actual random execution import. No circular proof of
the recurrence is permitted.

Keep the public namespace `Resources.RandomQuickSort`. The input theorem
universes are independent `α : Type u` and `κ : Type v`; only `[LinearOrder κ]`
is required. A family index has independent universe `ι : Type w`. The
predicate is exactly `(xs.map key).Nodup`. No payload order, equality,
inhabitation, finiteness, countability or measurable-space instance is added.
The existing four-universe rank transport remains unchanged; this consumer's
single-input assertions do not weaken that result.

This slice introduces no new sampler, cost observation, recursive operation,
expectation definition or harmonic-number definition. A private proof helper is
acceptable only if it removes repeated norm-bound reasoning; no new public
generic asymptotics API is needed.

## 3. Existing actual interfaces to consume

The exact mean is already defined as a genuine real integral of the actual Nat
cost marginal: `exerciseMean lt xs` and `literalMean lt xs`. The two marginal
integrals are genuinely integrable, with finite ENNReal bounds proved before
conversion to Real. The current mean module supplies unconditional
`exerciseMean_nonneg`, `literalMean_nonneg`, and the same-run result
`literalMean_comparison lt xs`:

```lean
exerciseMean lt xs ≤ literalMean lt xs ∧
  literalMean lt xs ≤ 2 * exerciseMean lt xs
```

The rank draft supplies:

```lean
sizeMean n =
  exerciseMean (fun a b : Nat => decide (a < b)) (List.range n)

sizeMean_zero : sizeMean 0 = 1

sizeMean_recurrence (n : Nat) (hn : 0 < n) :
  sizeMean n = (2 / (n : ℝ)) *
    (∑ k ∈ Finset.range n, sizeMean k) + 4 * (n : ℝ) - 1

exerciseMean_eq_sizeMean [LinearOrder κ] (key : α → κ)
    (xs : List α) (hd : (xs.map key).Nodup) :
  exerciseMean (fun a b => decide (key a < key b)) xs =
    sizeMean xs.length
```

The recurrence was derived from the original recursive PMF's actual mean
equation. The proof uses an occurrence-to-rank permutation, the lengths of the
actual `eraseIdx`/filter children, inherited mapped-key distinctness and
four-universe strong induction on those actual children. This consumer must
apply that theorem directly. It must not take a recurrence as a new public
hypothesis about the algorithm or replace the PMF by a rank-resampling model.

## 4. Exact numerical interface and first bridge

At `012ff45e`, namespace `Resources.QuickSortMean` defines:

```lean
closedForm n =
  8 * ((n : ℝ) + 1) * (harmonic n : ℝ) - 12 * (n : ℝ) + 1

eq_closedForm (A : Nat → ℝ) (hzero : A 0 = 1)
    (hrec : ∀ n : Nat, 0 < n →
      A n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, A k) +
        4 * (n : ℝ) - 1)
    (n : Nat) : A n = closedForm n
```

The first consumer proof is the direct application
`Resources.QuickSortMean.eq_closedForm sizeMean sizeMean_zero
sizeMean_recurrence n`. Thus the solver's numerical premises are discharged by
already declared actual execution theorems. This is the only route by which the
closed form receives an algorithmic interpretation.

The proposed first five public claims, in order, are:

| Name | Exact mathematical conclusion | Proof dependency |
| --- | --- | --- |
| `sizeMean_eq_closedForm` | `sizeMean n = Resources.QuickSortMean.closedForm n` for every Nat n | Direct solver application above |
| `sizeMean_eq_harmonic` | `sizeMean n = 8*((n:ℝ)+1)*(harmonic n:ℝ)-12*(n:ℝ)+1` | First claim and the existing definition |
| `exerciseMean_eq_closedForm` | Actual exercise mean of arbitrary distinct-key xs equals `closedForm xs.length` | Actual `exerciseMean_eq_sizeMean`, then first claim |
| `exerciseMean_eq_harmonic` | Actual exercise mean equals `8*((xs.length:ℝ)+1)*(harmonic xs.length:ℝ)-12*(xs.length:ℝ)+1` | Previous claim and the existing definition |
| `literalMean_harmonic_comparison` | The displayed harmonic expression is ≤ actual literal mean, which is ≤ twice that expression | Actual `literalMean_comparison` with the exercise equality rewritten |

The two input equalities and comparison all take only `[LinearOrder κ]`,
`key : α → κ`, `xs : List α`, and `hd : (xs.map key).Nodup` beyond ordinary
implicit types. They apply at sizes zero and one as well as positive sizes.
Parenthesize the complete harmonic expression when multiplying it by two.
Do not claim an exact harmonic formula for the append-inclusive observation.

## 5. Scalar logarithmic bounds

The numerical module provides, with the exact domain shown:

| Existing theorem | Bound on `closedForm n` | Domain |
| --- | --- | --- |
| `closedForm_le_log` | `16*(n:ℝ)*(1+Real.log (n:ℝ))` | `1 ≤ n` |
| `closedForm_le_nlog` | `(16*(1+1/Real.log 2))*((n:ℝ)*Real.log (n:ℝ))` | `2 ≤ n` |
| `closedForm_le_nlogb` | `32*((n:ℝ)*Real.logb 2 (n:ℝ))` | `2 ≤ n` |

Use the actual input equality to expose these unchanged inequalities. Add the
six public input theorems in the following table. Every row retains the key
order and mapped-key distinctness premises from Section 4.

| Proposed theorem | Right side, with n = xs.length | Additional premise |
| --- | --- | --- |
| `exerciseMean_le_log` | `16*(n:ℝ)*(1+Real.log (n:ℝ))` | `1 ≤ xs.length` |
| `literalMean_le_log` | `32*(n:ℝ)*(1+Real.log (n:ℝ))` | `1 ≤ xs.length` |
| `exerciseMean_le_nlog` | `(16*(1+1/Real.log 2))*((n:ℝ)*Real.log (n:ℝ))` | `2 ≤ xs.length` |
| `literalMean_le_nlog` | `(32*(1+1/Real.log 2))*((n:ℝ)*Real.log (n:ℝ))` | `2 ≤ xs.length` |
| `exerciseMean_le_nlogb` | `32*((n:ℝ)*Real.logb 2 (n:ℝ))` | `2 ≤ xs.length` |
| `literalMean_le_nlogb` | `64*((n:ℝ)*Real.logb 2 (n:ℝ))` | `2 ≤ xs.length` |

For each literal bound, first use the existing upper half of the same-run
comparison. Multiply the corresponding exercise bound by the nonnegative real
constant two and normalize ring arithmetic. This retains the actual two append
occurrences and their right-associated implementation. A generic numerical
comparison of unrelated marginal distributions would not justify this step.

The constants are deliberately inherited, not claimed optimal. The natural
logarithm is the real logarithm, and `Real.logb 2` is the book's binary
logarithm. No `Nat.log`, `Nat.clog`, rounded merge-tree height or runtime claim
is substituted for these expressions.

## 6. Genuine filter-based growth, including arbitrary input families

Add `sizeMean_isBigO_log` and `sizeMean_isBigO_logb`, with conclusions

```lean
Asymptotics.IsBigO Filter.atTop sizeMean
  (fun n : Nat => (n : ℝ) * Real.log (n : ℝ))

Asymptotics.IsBigO Filter.atTop sizeMean
  (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ))
```

Derive function equality with `Resources.QuickSortMean.closedForm` by
`funext sizeMean_eq_closedForm`, then use the exact existing
`closedForm_isBigO_log` and `closedForm_isBigO_logb`. These are now asymptotic
theorems about the canonical actual execution mean, rather than only a sequence
that conditionally satisfies a recurrence.

For arbitrary families, use an independent index type and an arbitrary filter.
The binary exercise claim is precisely the following proposed shape:

```lean
theorem exerciseMean_family_isBigO_logb
    {ι : Type w} [LinearOrder κ] (key : α → κ)
    (l : Filter ι) (xs : ι → List α)
    (hd : ∀ᶠ i in l, ((xs i).map key).Nodup)
    (hlen : Filter.Tendsto (fun i => (xs i).length) l Filter.atTop) :
    Asymptotics.IsBigO l
      (fun i => exerciseMean (fun a b => decide (key a < key b)) (xs i))
      (fun i => ((xs i).length : ℝ) *
        Real.logb 2 ((xs i).length : ℝ))
```

Add `literalMean_family_isBigO_logb` with the same hypotheses and actual
`literalMean` in the conclusion. Add both corresponding natural-log claims,
`exerciseMean_family_isBigO_log` and `literalMean_family_isBigO_log`.
These four statements permit arbitrary input order, arbitrary growth of
length, arbitrary payload values and arbitrary finitely many exceptional
inputs; eventual distinctness is sufficient. The theorem does not silently
assert that the means grow as the external index when length is not that index.

The proof uses the already inspected pinned definitions rather than a new
growth predicate:

1. Obtain `∀ᶠ i in l, 2 ≤ (xs i).length` from
   `Filter.tendsto_atTop.mp hlen 2`, or the equivalent inspected
   `hlen.eventually_ge_atTop 2`.
2. Combine that event with `hd` using ordinary filter reasoning.
3. Supply the appropriate scalar constant to `Asymptotics.isBigO_iff.mpr`:
   `16*(1+1/Real.log 2)` or `32*(1+1/Real.log 2)` for natural log, and 32 or 64
   for binary log.
4. Rewrite real norms as absolute values, then remove them using actual mean
   nonnegativity and logarithm nonnegativity at lengths at least two. Apply
   the corresponding scalar input bound.

The exact pinned `isBigO_iff` is existence of a real constant with an eventual
norm inequality. `Real.log_nonneg`, `Real.logb_nonneg`, `Real.norm_eq_abs` and
`abs_of_nonneg` provide the same sign bridge already used in the numerical
source. No convergence/integrability of a family of payload-valued random
variables is required: each real cost mean was justified separately before
this slice. No extra `[l.NeBot]` premise is necessary for the standard filter
statement. Concrete Nat/atTop examples are nontrivial and expose its intended
asymptotic interpretation.

In the natural-index specialization `xs : Nat → List α`, with distinct keys
at every n and `(xs n).length = n`, the result is exactly Big-O of
`fun n => (n:ℝ)*Real.logb 2 (n:ℝ)` (and analogously for natural log).
Use the family theorem and prove length tends to infinity by rewriting to the
identity. No extra public wrapper is needed: an arbitrary-family example will
exercise this complete signature. A second example with length `n+2` prevents
confusing an input family's index with its size.

The planned public resource inventory is 17 theorems: five exact identities or
comparisons, six scalar inequalities, two canonical actual-sequence Big-O
theorems and four arbitrary-family Big-O theorems.

## 7. Connected examples and independently fixed results

The following 14 example claims are the bounded intended example scope. They
should consume the actual resource results and existing actual zero/singleton/
constant-key mean laws; they must not prove only properties of a detached
numerical sequence.

| Proposed example | Fixed expected result and consequential case |
| --- | --- |
| `empty_payload_means` | For `List Empty`, actual exercise and literal means are both 1; harmonic transport has value 1 without constructing a pivot or requiring an inhabited payload. |
| `singleton_payload_means` | For an arbitrary payload and key map, actual means are 5 and 8; the harmonic exercise value is 5 and the literal sandwich is `5 ≤ 8 ≤ 10`. |
| `empty_log_boundary` | For every real C, both positive empty means fail a scalar bound `C*(0*logb 2 0)`. |
| `singleton_log_boundary` | For every real C, both singleton means fail `C*(1*logb 2 1)`; the size-two threshold is meaningful. |
| `two_distinct_harmonic` | On actual `[1,0]`, exercise mean 13, literal mean between 13 and 26, and the binary scalar bounds at n=2 are 64 and 128. Do not relabel either loose bound as an exact literal mean. |
| `three_reordered_harmonic` | Actual `[2,0,1]` has exercise mean `71/3`; literal mean lies between `71/3` and `142/3`. This agrees with the independently established actual cost masses `1/3` at 21 and `2/3` at 25. |
| `four_tagged_harmonic` | Payloads `(3,a),(1,b),(0,c),(2,d)` with arbitrary tags have exercise mean `109/3`; literal mean lies between `109/3` and `218/3`. No equality/order/measurability on the tag type is added. |
| `five_sizeMean` | Actual canonical `sizeMean 5 = 253/5`, calculated independently before source proof. |
| `arbitrary_length_indexed_growth` | For arbitrary `xs : Nat → List α` with mapped-key distinctness and exact length n, both actual means have genuine binary-log Big-O in n. |
| `function_tagged_family_growth` | Inputs obtained by attaching arbitrary function-valued tags to `List.range n` have both actual mean bounds. Full payload equality, enumeration and a payload measurable space remain absent. |
| `shifted_range_family_growth` | `List.range (n+2)` has both actual family bounds expressed in length `n+2`; prove length tends to infinity directly, without assuming index=length. |
| `equal_key_three_not_harmonic` | Three equal-key occurrences have exercise mean 25, unequal to distinct-key harmonic value `71/3`; this distinguishes the actual distinctness premise even though size and raw tagged-payload distinctness can coincide. |
| `equal_key_family_means` | For arbitrary constant-key tags of length n, actual exercise mean is `2*n^2+2*n+1` and actual literal mean is `2*n^2+5*n+1`, with Real casts of the Nat tariffs. |
| `equal_key_binary_bounds_fail` | At n=256 under a constant key, actual means are 131585 and 132353. Since `logb 2 256=8`, the distinct-key bounds would give 65536 and 131072 respectively; both inequalities fail. Raw payloads may be `List.range 256`, so payload Nodup alone cannot supply the missing premise. |

Independent exact-rational arithmetic was calculated during preparation:

| n | H_n | `8*(n+1)*H_n-12*n+1` |
| ---: | ---: | ---: |
| 0 | 0 | 1 |
| 1 | 1 | 5 |
| 2 | 3/2 | 13 |
| 3 | 11/6 | 71/3 |
| 4 | 25/12 | 109/3 |
| 5 | 137/60 | 253/5 |

These Fraction calculations and source-level expectations are not Lean checks.
Use the existing rational `harmonic`/`harmonic_succ` interface to establish
small values, or consume the already proved actual recurrence where shorter.
For the n=256 duplicate counterexample, rewrite `256=(2:ℝ)^8`, then use the
inspected `Real.logb_pow 2 2 8` and `Real.logb_self_eq_one (by norm_num)`.
Obtain the actual quadratic means from `exerciseMean_of_all_false` and
`literalMean_of_all_false`; do not unfold or enumerate 256 recursive PMF runs.
The logarithm equality and two numerical comparisons remain theorem goals.

The duplicate cases refute removing the mapped-key hypothesis from these exact
formulas and fixed scalar bounds. No general theorem `¬ IsBigO` is claimed by a
single finite counterexample. The retained all-equal exact quadratic family is
the meaningful infinite-family boundary; a separate non-Big-O theorem is not
needed to establish the requested distinct-key upper bounds.

## 8. Probability and cost qualifications retained

The probability space remains the existing execution on a fixed input. Every
nonempty recursive call chooses a fresh uniform valid occurrence index, erases
that occurrence and recursively binds the actual two returned filter lists.
The same joint run supplies the exercise and literal marginals. There is no
deduplicated pivot set, silent child-input resampling, assumed global priority
coupling or uniform-input experiment in this slice.

The exact harmonic identity observes the Exercise 2.4 tariff: empty cost 1;
two measured filters and actual recursive calls; nonempty local toll `4*n-1`
for original size n. The literal observation additionally charges both actual
right-associated append occurrences. It is controlled by the proved same-run
factor-two comparison, not assigned the exercise's exact formula.

Neither observation charges uniform sampler implementation, random bits,
valid-index access, pivot lookup, occurrence deletion, payload/key evaluation,
allocation, or Lean wall time beyond the already specified call-count model.
Those are explicit observation boundaries. A claim adding an implementation's
extra linear selection/removal toll requires a separate proved comparison and
is not silently obtained by relabeling either mean in this plan.

The separate deterministic first-pivot/uniform-input average remains mandatory
under frozen C02-024. Sharing the numerical solver does not identify the two
probability experiments. This consumer also does not close the other frozen
Chapter 2 obligations, source stability qualifications, full-book coverage or
foundation acceptance.

## 9. Pinned API readback and implementation release gates

Only the supplied local source trees were used for API inspection. Exact
supplementary inspected source identities are:

| Pinned Mathlib path | Relevant inspected interface | SHA-256 |
| --- | --- | --- |
| `Mathlib/Analysis/Asymptotics/Defs.lean` | `Asymptotics.isBigO_iff`, `IsBigO.of_bound`; existence of an eventual norm bound | `68ef9c1b2d13f99770bcd0c679a23f078f634ea344ff914d7d634ba1682104ed` |
| `Mathlib/Order/Filter/AtTopBot/Tendsto.lean` | `Filter.tendsto_atTop`, `Tendsto.eventually_ge_atTop` | `0ec2f390f3a7c9648018b095b58735895d75f7895635ffaedd02baa5e6db5301` |
| `Mathlib/Analysis/SpecialFunctions/Log/Base.lean` | `Real.logb_nonneg`, `logb_pow`, `logb_self_eq_one` | `85a4b68a9ec0f6cf2fbb706f42a9136d23c4b11f1092b2e88c820c9e26421bbf` |

I also inspected the existing `IsBigO.comp_tendsto`/congruence alternatives in
`Mathlib.Analysis.Asymptotics.Basic`; the proposed direct scalar-bound route
does not need that additional import. `Filter.Eventually.of_forall` and
`Filter.eventually_ge_atTop` were located/read for the natural-index examples.

Before implementation, the root must release the two-file slice and name an
exact author base containing the required source identities or their explicitly
reviewed proof-only successors. Preserve the author worktree and pins. No
unreviewed numerical dependency may be silently merged for convenience.

Implementation assessment must compare every public theorem's full elaborated
statement against the intended contract above, including universes, mapped-key
distinctness, eventual length hypotheses, exact actual means, constants and
zero/one restrictions. Read every proof and private helper. Use the enabled
linters; no suppressions, `sorry`, `admit`, new axioms or native evaluation may
replace proof. Keep any required compiler correction minimal and separately
recorded, with original failures and terminal outcomes retained.

The parent exclusively runs focused compilation and complete statement
inspection on fixed central candidates. A focused module pass does not replace
the complete candidate check, exhaustive axiom audit, independent Standards and
Spec reviews, or immediate `--verify-candidate HEAD` before an accepted
fast-forward. No acceptance or coverage closure is authorized by this plan.

After saving this plan the author holds all source/ref/control/provenance
writes, with read-only diagnostic preparation available. Actual rank/mean
compiler findings take priority when supplied by the coordinator.
