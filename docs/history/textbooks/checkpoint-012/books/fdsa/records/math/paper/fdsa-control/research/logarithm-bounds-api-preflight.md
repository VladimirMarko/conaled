# FDSA-XL01 — Logarithm bounds: pinned API and reuse preflight

Status: **report-only preparation; no implementation, chosen base, scope freeze, compilation, validation or acceptance**. This is the assigned API assessment within the existing book workflow, not a new review axis. Only this report was written. C1 attempt 3 remains the sole validator; no active output, compiler, checker, project hash helper, cache, worktree, index or ref was touched. The exact initial C2 integration prefix remains `c80eec92f5458eccfd1c34c8314d666c2a1e3847` after repaired C1 acceptance. No existing obligation or historical outcome changes.

## 1. Recommendation and bounded conclusion

There is a small genuine common mathematical fact: the **sharp base-2 two-argument logarithm bound**, used directly by pairing analyses and through its strict `+1` consequence by splay analyses. The pinned library supplies all its ingredients, but the bounded source search did not find a named theorem with this complete statement. A short ordinary Real proof from `4*x*y ≤ (x+y)^2`, monotonicity and product/power logarithms is sufficient. There is no need for a new logarithm, potential, evaluator, typeclass or weighted-mean framework.

If root selects a shared unit later, the minimum useful public surface is the sharp bound and its strict arithmetic consequence. Both are about ordinary `Real.logb 2`; the latter is worth naming because an actual independent source consumer repeatedly needs that strict margin. This recommendation does not select an implementation base or authorize either theorem. The two other `Lemmas_log` statements remain explicitly accounted for below; they need not become public aliases solely to reproduce the Isabelle names. In particular, the shifted-product statement has a stronger immediate library proof, and the shifted-minus-one helper has no named consumer found in the saved theory corpus. Skew's arbitrary-base weak bound is a direct application of two existing monotonicity lemmas.

A possible future arithmetic-only path is `Applications/Resources/LogarithmBounds.lean`, with a small connected example file. That is a **path proposal**, not an edit or agreed scope. The pure inequalities require the pinned Mathlib logarithm module, not XP01, a tree draft or a later algorithm import. Existing XP01 and tree modules are later consumers; ancestry and planned imports confer no validation. Root can defer this addition without losing any source obligation.

No concrete mathematical or API obstruction was found. Remaining uncertainty concerns ordinary uncompiled Lean proof elaboration and the later algorithm-specific cost/potential bridges, not the validity of the five inequalities on their stated domains.

## 2. Exact inputs and inspected source boundary

The ticket was read in full: `fdsa-control/tickets/FDSA-XL01.md`, 2,422 bytes / 39 lines, SHA-256 `5fd712cf74d2fbd0aaae5246054c7087a1e9081592da0e9a8f8b4daae4bf3758`. The assigned report path was absent before authoring. Applicable existing AGENTS, architecture/domain and implementation/EDD guidance was retained; this report does not start an implementation or review loop.

Primary sources are the retained local files under `book-source/`, not a fresh internet edition. `Lemmas_log.thy` was read completely; the actual consumer definitions and call sites listed in Section 7 were inspected. The parallel source report owns the complete source/license assessment and does not change this report's API findings.

| Retained primary file | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| `Lemmas_log.thy` | 1,768 / 55 | `efac8b7ffdbdad1cdc9a825475d9a0ac9558025a092fcfd02f6b8881e2be8d41` |
| `Skew_Heap_Analysis.thy` | 7,443 / 199 | `e1b224bf9d210bd3c8cd78508adab3444515b60d4162a903436d4add45f24b7b` |
| `Splay_Tree_Analysis_Base.thy` | 4,591 / 119 | `3f8cc3fd475bf40bed0eff7f2442370eb326e140c90e66600fea220fc22cfe17` |
| `Splay_Tree_Analysis.thy` | 20,301 / 432 | `fd6ac8ae8b48e18e4dc8622e49f527ea7ce7fa8fa557f2af4231fd90e268f012` |
| `Splay_Tree_Analysis_Optimal.thy` | 21,840 / 495 | `511162539e9b8cab7bf804db673c82d2d534d6365098cc81525914506df0b73d` |
| `Pairing_Heap_Tree_Analysis.thy` | 9,817 / 251 | `0e7f8008a2d06c7dbc2f8647b05f87324dafab5ff96daa96097bb2722cfdc368` |
| `Pairing_Heap_Tree_Analysis2.thy` | 9,180 / 236 | `a04e140d2ff71d11bafd9e16e39359bcf132b194d7cbfe9a27206f261e53d191` |
| `Pairing_Heap_List2_Analysis.thy` | 9,794 / 271 | `edf22de9e51028eac4a7936a12b06903c9b1b7fce101e9342da596f9b3aa70db` |

The relevant unchanged Chapter 19/21/22/23 inventory rows and reuse boundaries were inspected, including C19-016; C21-074/085/091/092/098; C22-056/061/062/065; C23-039/042/044/046/055/056/058/061/072/073. This was a targeted read of relevant obligations, not a claim to have re-reviewed every chapter. Their recorded identities are respectively `1d9d22ca8d801d7c0ba47910d0f6519dd7c76acd787164be3a382ad818c220c6`, `e9ec73c1de2835060646f62fd7d675b192b4f1960742f917952a4fbf78265a51`, `805b5d297ee9088a01ed4adf7f3816debd7e9a4f02777364fc85f522a1935939`, and `01c1184e372e574b0487822e844ff5f2abecd6c7e05fa3d59961972d785ea700`.

Pinned Mathlib is commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, read at `/workspace/scratch/845aa1048b05/conaled/.lake/packages/mathlib`; the retained Lean pin is v4.35.0 / `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Project sources were read through the installed pinned Nix shell and read-only `git show`/search with optional Git locks disabled. No checkout was recreated.

| Exact retained project input | File and inspected role | Ordinary file SHA-256 |
| --- | --- | --- |
| C1 candidate `07e480f6ec9958d4975bb90151005b84f2907614` | `Applications/Resources/Growth.lean`, complete 17-line Nat-to-Real asymptotic bridge | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
| XP01 draft `c28ba71863d2a35ee1c3a089caa90464e4cca692` | `Applications/Resources/Potential.lean`, complete 238 lines | `fa33b209a7c8cd700e7a33a6d3ee11ef9ad572c2d2e8406dfbabf6468ebf7d8c` |
| Same XP01 draft | `Examples/MappedPotentialAccounting.lean`, complete 165 lines | `aa57790203c7dbc800586464c46366fcd7e6da6965fdbc3c260285e9c8d693c3` |
| XT01 original `64c6b777d828ecfe83234fc2aed94600a1f24297` | `Applications/Trees/Observations.lean`, retained ordinary fold/count/inorder interface | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| XT02 tip `974a97321a8ec174b56104c7e6efaaca881b6639` | `Applications/Trees/Shape.lean`, retained discrete bounds | `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3` |
| Same XT02 tip | `Applications/Trees/ShapeLog.lean`, complete 69-line Real corollary file | `35c0555383fc3d03bcac4f368d41b2c8f744a49e18ef72b192c3753b7ef4497b` |

These are inspection identities, not selected dependencies or accepted bases. In particular c28 is the later potential addition, not the initial c80 C2 prefix.

## 3. Exact five source statements and minimal-domain assessment

Write `L x = Real.logb 2 x` only as notation in this report; no new Lean definition is proposed.

| Primary declaration | Exact source premises and conclusion | API/reuse assessment |
| --- | --- | --- |
| `Lemmas_log.ld_sum_inequality`, lines 5–16 | `0 < x`, `0 < y`; `L x + L y + 2 ≤ 2 * L (x+y)` | Genuine common sharp inequality. Positive inputs may be below 1. Neither `x ≥ 1`, distinctness, natural-valued inputs nor tree assumptions are needed. |
| `Lemmas_log.ld_ld_1_less`, lines 18–20 | Same positive premises; `1 + L x + L y < 2 * L (x+y)` | Strictness comes from one unit of slack in the preceding `+2` bound, including `x=y`. Do not add `x ≠ y` as if using strict AM–GM. |
| `Lemmas_log.ld_le_2ld`, lines 32–41 | `0 ≤ x`, `0 ≤ y`; `L (1+x+y) ≤ 1 + L (1+x) + L (1+y)` | Product monotonicity actually proves the stronger statement without the leading `1` on the right. Retain the source's exact weaker target and constants in source correspondence. |
| `Lemmas_log.ld_ld_less2`, lines 43–53 | `2 ≤ x`, `2 ≤ y`; `1 + L x + L y ≤ 2 * L (x+y-1)` | All three logarithm arguments are positive. These are sufficient source premises, not a claim that each is individually minimal. Merely positive arguments are insufficient. No named consumer was found in the saved theory corpus. |
| `Skew_Heap_Analysis.plus_log_le_2log_plus`, lines 52–54 | `0 < x`, `0 < y`, `1 < b`; `Real.logb b x + Real.logb b y ≤ 2 * Real.logb b (x+y)` | Direct increasing-log monotonicity twice. No nonnegative-log premise is needed; no new common wrapper is required merely for the source name. |

All five operate on `ℝ`. There is no payload universe, measurable space, finiteness, decidable equality or inhabitance assumption to add. A later tree specialization should keep its arbitrary payload universe and prove only the numeric size premises. A generalized base version of the sharp bound would have margin `2 * Real.logb b 2`, not the constant `2`; that extension is mathematically feasible but not required by the actual common base-2 consumers identified here.

The fourth helper can, for example, be proved under the weaker asymmetric sufficient assumptions `2 ≤ x` and `0 < y`, or symmetrically. That observation prevents an inaccurate minimality claim; it is not a recommendation to enlarge the public scope with several variants. The positive source domains of the first, second and fifth statements must not be weakened to nonnegative arguments through the totalized logarithm.

## 4. Exact pinned logarithm API

The main import is `Mathlib.Analysis.SpecialFunctions.Log.Base`. It publicly imports `Mathlib.Analysis.SpecialFunctions.Pow.Real` and `Mathlib.Data.Int.Log`; the file is Apache-2.0 with its own retained copyright/authorship header. Its source identity is 25,117 bytes / 632 lines, SHA-256 `85a4b68a9ec0f6cf2fbb706f42a9136d23c4b11f1092b2e88c820c9e26421bbf`.

The following are **existing declarations**, with implicit `b x y : ℝ` where appropriate, not proposed wrappers:

```lean
Real.logb (b x : ℝ) : ℝ := Real.log x / Real.log b

Real.logb_self_eq_one (hb : 1 < b) : Real.logb b b = 1
Real.logb_mul (hx : x ≠ 0) (hy : y ≠ 0) :
  Real.logb b (x * y) = Real.logb b x + Real.logb b y
Real.logb_div (hx : x ≠ 0) (hy : y ≠ 0) :
  Real.logb b (x / y) = Real.logb b x - Real.logb b y
Real.logb_inv (b x : ℝ) : Real.logb b x⁻¹ = -Real.logb b x
Real.logb_pow (b x : ℝ) (k : ℕ) :
  Real.logb b (x ^ k) = k * Real.logb b x
Real.logb_rpow_eq_mul_logb_of_pos (hx : 0 < x) :
  Real.logb b (x ^ y) = y * Real.logb b x
```

Locations: definition 44; self 65; multiplication 85; division 88; inverse 92; real power 122; natural power 125. `logb_pow` needs neither input positivity nor a base premise; `logb_mul` needs nonzero factors but no base premise. These algebraic generalities do not remove the positivity/base requirements of the monotonicity step.

For `hb : 1 < b`, the leading `hb` is an explicit argument to the following declarations in the `OneLtB` section:

```lean
Real.logb_le_logb hb (hx : 0 < x) (hy : 0 < y) :
  Real.logb b x ≤ Real.logb b y ↔ x ≤ y
Real.logb_le_logb_of_le hb (hx : 0 < x) (hxy : x ≤ y) :
  Real.logb b x ≤ Real.logb b y
Real.logb_lt_logb hb (hx : 0 < x) (hxy : x < y) :
  Real.logb b x < Real.logb b y
Real.logb_lt_logb_iff hb (hx : 0 < x) (hy : 0 < y) :
  Real.logb b x < Real.logb b y ↔ x < y
Real.logb_le_iff_le_rpow hb (hx : 0 < x) :
  Real.logb b x ≤ y ↔ x ≤ b ^ y
Real.le_logb_iff_rpow_le hb (hy : 0 < y) :
  x ≤ Real.logb b y ↔ b ^ x ≤ y
Real.logb_nonneg hb (hx : 1 ≤ x) : 0 ≤ Real.logb b x
Real.logb_neg hb (hx : 0 < x) (hx' : x < 1) : Real.logb b x < 0
```

Locations: 190/194/198/203/207/213/237/231. `Real.logb_pos_iff hb hx` (219) and `Real.logb_nonneg_iff hb hx` (234) explicitly distinguish positive arguments from arguments at least one. The strict log/exponential forms at 210/216 are also available. This makes a proof with natural powers possible without converting the whole inequality to `rpow`; natural-power product algebra is simpler for the present quadratic bounds.

Totalization is part of the pinned operation, not an omitted side condition:

- `Real.logb_zero` (51): `logb b 0 = 0`.
- `Real.logb_one` (54): `logb b 1 = 0`.
- `Real.logb_zero_left` / `Real.logb_one_left` (56/60): bases 0 and 1 give zero.
- `Real.logb_abs` (75) and `Real.logb_neg_eq_logb` (82): negative arguments use the same value as their absolute values.
- Base in `(0,1)` reverses order: `Real.logb_le_logb_of_base_lt_one b_pos b_lt_one hx hy` (284) is equivalent to `y ≤ x`, and `Real.logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy` (287) concludes `logb b y < logb b x`.

The Lean/source correspondence therefore stays on the source's stated positive-log domains. No assertion of identical out-of-domain totalization between Isabelle and Mathlib is needed or made.

The inspected natural-log module `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` has the analogous existing `Real.log_mul`, `log_div`, `log_pow`, `log_le_log`, `log_lt_log`, `log_nonneg`, and `log_neg`. Its `Real.log_le_sub_one_of_pos` (307) is the tangent inequality `log x ≤ x-1`, not the required two-input sharp statement. Changing the source notation to natural logarithms merely introduces division by positive `Real.log 2`; it does not discover a different missing object.

## 5. Concrete short proof routes; no duplicate analytic framework

### 5.1 Sharp base-2 bound

For `hx : 0 < x` and `hy : 0 < y`, establish the ordinary polynomial inequality

```text
4*x*y ≤ (x+y)^2
```

from `sq_nonneg (x-y)`. Its left side is positive, so

```lean
Real.logb_le_logb_of_le (b := 2) (by norm_num) hleft hpoly
```

is the correct pinned monotonicity application. Expand the left logarithm with `Real.logb_mul` using nonzero proofs from positivity, and expand the right using `Real.logb_pow 2 (x+y) 2`. Derive `Real.logb 2 4 = 2` from `4 = (2 : ℝ)^2`, `logb_pow` and `logb_self_eq_one`. Reassociate by ordinary Real algebra. Every call is on the actual argument whose positivity was proved; no nonnegative-log assumption is used.

This is a source proof plan, not compiled Lean. `Mathlib.Tactic.Linarith` supplies the proposed `linarith`/`nlinarith` arithmetic tactics and `Mathlib.Tactic.NormNum` supplies numeric normalization; both exact module paths were checked. They may be explicit imports if later proof authoring uses them. The analysis dependency need not grow beyond `Log.Base`; no Jensen, integral, derivative, finite probability or additional execution module is needed.

The strict statement follows from this result by linear arithmetic, since the sharp left side is exactly one larger than `1 + logb 2 x + logb 2 y`. Equality in sharp AM–GM at `x=y` does not obstruct this strict consequence.

### 5.2 Nonnegative shifted product

For `0 ≤ x` and `0 ≤ y`, prove positivity of `1+x`, `1+y`, `1+x+y` and

```text
1+x+y ≤ (1+x)*(1+y)
```

using `0 ≤ x*y`. Apply `logb_le_logb_of_le` and `logb_mul`. This proves

```text
logb 2 (1+x+y) ≤ logb 2 (1+x) + logb 2 (1+y).
```

Then weaken by the source's extra `1`. There is no need to appeal to the sharp AM–GM result, assume strict positivity of x/y themselves, or define another logarithm. If selected later as a public result, the stronger product statement would be more informative than a name-only copy; it is not required for the minimal two-statement common surface. Improving this local numerical estimate does not automatically improve all recorded pairing-operation constants.

### 5.3 Source shifted-minus-one bound

For the exact source premises `2 ≤ x` and `2 ≤ y`, prove `0 < x+y-1` and

```text
2*x*y ≤ (x+y-1)^2.
```

A transparent polynomial certificate is

```text
(x+y-1)^2 - 2*x*y = (x-1)^2 + (y-1)^2 - 1.
```

Apply the same positive-argument monotonicity and product/power equations; `logb 2 2 = 1` supplies the source constant. The two ≥2 premises can also be used directly to establish the source's `2*x ≤ x*x` and `2*y ≤ y*y` argument. Neither route assumes a tree invariant. No named saved consumer requires promoting this statement to a new common API now; it stays an explicitly understood source helper, not a dropped claim.

### 5.4 Arbitrary-base skew bound

For `hb : 1 < b`, `hx : 0 < x`, `hy : 0 < y`, apply

```lean
Real.logb_le_logb_of_le hb hx (show x ≤ x+y from ...)
Real.logb_le_logb_of_le hb hy (show y ≤ x+y from ...)
```

with the other input's nonnegativity, add the two inequalities, and rewrite two equal summands as `2 * logb b (x+y)`. This needs no AM–GM, positivity of logarithm values, natural count restriction or dedicated source-named wrapper. It is also weaker than the sharp generalized-base statement, but selecting that generalization is unnecessary for the actual source call.

### 5.5 Existing concavity/AM–GM alternatives, with exact namespaces

The pinned library already has the broader mathematics. In `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:66`, **root-namespace**

```lean
strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Set.Ioi 0) Real.log
```

is available. It is not named `Real.strictConcaveOn_log_Ioi`. `StrictConcaveOn.concaveOn` at `Mathlib/Analysis/Convex/Function.lean:400` gives the non-strict form. The definition's second conjunct takes memberships `hx`, `hy`, nonnegative weights, and the weight-sum-one equation; weights `1/2,1/2` give the usual logarithmic Jensen inequality. Product/division algebra and division by positive `log 2` recover the sharp bound.

The two-input AM–GM API is in `Mathlib/Analysis/MeanInequalities.lean:390`:

```lean
Real.geom_mean_le_arith_mean2_weighted
  {w₁ w₂ p₁ p₂ : ℝ}
  (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
  (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁+w₂=1) :
  p₁^w₁ * p₂^w₂ ≤ w₁*p₁ + w₂*p₂
```

The finite variants `Real.geom_mean_le_arith_mean_weighted` (129) and `Real.geom_mean_le_arith_mean` (152) carry their actual weight-sum/nonnegativity premises. These are valid reuse options if a later client needs weighted families. For the present two-variable square inequality, invoking real powers, finite products or a new Jensen wrapper adds proof/interface work without serving another selected consumer. Their allowance of zero arguments before taking a logarithm does not validate the desired log statements at zero.

The bounded declaration/text search covered the log modules and the relevant Analysis concavity, Jensen and mean-inequality sources, plus an Analysis-wide combined-log pattern search. It found no complete sharp base-2 result; this is a scoped search finding, not a universal theorem-absence claim. `Real.posLog` bounds and ENNReal logarithms concern different operations/domains and are not interchangeable substitutes.

## 6. Natural casts, actual tree observations and existing accounting

### 6.1 Explicit cast and nonempty argument bridges

Exact pinned existing declarations include:

```lean
Nat.cast_add (m n : ℕ) : ((m+n : ℕ) : R) = m+n
Nat.cast_succ (n : ℕ) : ((Nat.succ n : ℕ) : R) = n+1
Nat.cast_add_one (n : ℕ) : ((n+1 : ℕ) : R) = n+1
Nat.cast_add_one_pos (n : ℕ) : 0 < (n : α)+1
Nat.cast_pos {n : ℕ} : (0 : α) < (n : α) ↔ 0 < n
Nat.cast_sub {m n : ℕ} (h : m ≤ n) : ((n-m : ℕ) : R) = n-m
```

The ambient algebraic/order assumptions belong to each existing declaration as follows; these formulas are not assumptions about arbitrary R. `cast_add`/`cast_succ`/`cast_add_one` are at `Mathlib/Data/Nat/Cast/Defs.lean:100/87/105` with `[AddMonoidWithOne R]`. `cast_add_one_pos` is at `Data/Nat/Cast/Order/Basic.lean:46` under its ordered additive assumptions and `[NeZero (1 : α)]`. The commonly used `Nat.cast_pos` specialization at `Data/Nat/Cast/Order/Ring.lean:55` has `[Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]`. `Nat.cast_sub` is in **`Mathlib/Data/Int/Cast/Basic.lean:36`**, namespace Nat, with `[AddGroupWithOne R]`; it requires the actual no-underflow premise. All needed instances exist for ℝ.

Consequently `(n : ℝ)+1` is positive even at n=0, and at least one. For `(n : ℝ)` itself, positivity requires `0<n`. For the skew identity with `ell₁+ell₂-1`, prove the Nat subtraction domain and cast it correctly, or first use the established positive integer identity; never silently identify truncated Nat subtraction with Real subtraction. Cast actual work into Real **before** forming signed potential differences. An expression such as `(T + Φout - Φin : Nat)` would describe truncation and is not the source amortized charge.

Pinned `BinaryTree.numLeaves_pos` and `BinaryTree.numLeaves_eq_numNodes_succ` already supply positive external-leaf counts and their exact node-count offset, including nil. XT01's ordinary `Trees.fold`, `fold_map`, `fold_fusion`, `fold_numNodes` and `inorder` remain usable observations if a later concrete potential is defined over that carrier. No logarithm-specific tree carrier or generic potential cache is missing.

### 6.2 ShapeLog reuse has precise limits

At XT02's original tip, `Trees.minHeight_le_logb_numLeaves` and `Trees.logb_numLeaves_le_height` apply to every raw binary tree. Their strict versions assume incompleteness; `height_eq_logb_numLeaves` requires completeness, and `minHeight_eq_floor_logb_numLeaves` / `height_eq_ceil_logb_numLeaves` require `AlmostComplete`. They already use `Real.le_logb_iff_rpow_le`, `logb_le_iff_le_rpow`, `rpow_natCast` and `Nat.cast_pos`.

`Real.natFloor_logb_natCast (b n : ℕ)` and `Real.natCeil_logb_natCast (b n : ℕ)` at Base.lean:401/412 identify the rounded Real logarithms with `Nat.log`/`Nat.clog`; the declarations themselves have no extra base/nonzero premise. This is a rounding bridge, not permission to replace an unrounded signed Real potential with a Nat logarithm. Splay and skew trees need not be almost complete; a logarithmic amortized charge is not a logarithmic worst-case height statement. No new shape or log-rounding lemma is needed for the five pure inequalities.

### 6.3 XP01 already supplies the real/signed telescoping mechanism

The saved XP01 API is more general than the historical Nat-only descriptions still present in some inventories. No inventory was rewritten. Its `Resources.budget` follows the same actual `step : ι → σ → σ × C` trajectory as `Resources.run`; it is not a second arbitrary execution. Its mapped boundary accepts `h : C →+ D` and a state potential in D.

The exact principal public call orders read in `Applications/Resources/Potential.lean` are:

```text
run_potential_map_of_invariant
  step charge potential h P closed hstep is s hs
run_cost_le_map_of_invariant
  step charge potential h P closed hstep nonneg is s hs
budget_amortized step potential h is s
```

For the first, `hstep` is the actual invariant-local inequality

```text
h (step i s).2 + potential (step i s).1
  ≤ potential s + charge i s.
```

The conclusion retains the final potential on the left and the initial potential plus actual-trajectory budget on the right. Its ordinary additive ordered observation assumptions admit ℝ; actual Nat work can use the existing `Nat.castAddMonoidHom ℝ`. The exact equality theorem is also present. `budget_amortized` works in an additive commutative group and gives exactly

```text
Σ-on-actual-trajectory [h(actualWork)+Φ(next)-Φ(current)]
  = h(totalActualWork)+Φ(final)-Φ(initial).
```

It allows negative individual charges and negative potential values. `run_cost_le_map_of_invariant` additionally requires `nonneg : ∀ s, P s → 0 ≤ potential s` to drop the reachable final potential. A positive log argument alone cannot supply that premise. The full existing `MappedPotentialAccounting` examples already connect actual counters, fractional Real credit, negative Int charges, invariant-restricted cost laws and noncommutative exact observations; a new evaluator/telescoping framework would duplicate them.

The pure log bound only helps prove an algorithm's `hstep`. It supplies neither an actual measured transition nor invariant closure, ownership of multiple input heaps, permission to spend a discarded output potential, or the source tariff. Skew and pairing merge charges subtract two input potentials; matching those to a global machine state or retained-heap ownership remains an algorithm-specific step. The generic state type could encode an appropriate state later, but this report does not select or implement one.

Finally `Resources.isBigO_of_nat_bound f g C N bound` at C1's `Growth.lean:10` consumes an eventual Nat inequality `f n ≤ C*g n` and yields the usual real-cast `Asymptotics.IsBigO`. It is neither a Real logarithm theorem nor a signed amortized-history theorem. An exact state-dependent log budget must first be established; merely naming that existing asymptotic interface does not prove it.

## 7. Actual consumers and meaningful connected checks

The repeated consumers make the sharp bound genuinely common, rather than an invented cross-cutting abstraction:

- `Splay_Tree_Analysis_Base.thy:14–18` defines rank `φ t = log₂(size1 t)` and a sum-of-ranks potential. `Splay_Tree_Analysis.thy` has live `ld_ld_1_less` uses at 40, 113, 143, 164 and 313. The occurrence at 187 is inside the commented alternative at 177–192 and is not counted as a live proof. Each use has actual positive external-leaf arguments. C21-074 retains the mathematical helper; splay cost/value/invariant proofs remain separate.
- `Pairing_Heap_Tree_Analysis.thy:93`, `Pairing_Heap_Tree_Analysis2.thy:76`, and `Pairing_Heap_List2_Analysis.thy:113` use `ld_sum_inequality` on actual pass-one size expressions. C23-046 retains that sharp inequality. The binary variants also use `ld_le_2ld` at 63 and 61 respectively. Their logarithm offsets differ from splay: a binary nonempty node rank uses node count, and the list/forest potential includes sibling-tail sizes. A shared Real inequality does not identify those potentials.
- `Skew_Heap_Analysis.thy:52–54` has the weak arbitrary-base helper. Its actual local amortized combination at 96–110 uses positive external-leaf counts and the shifted merged count. C22-056 retains both this log step and the required size/positivity facts. The potential is Int-valued, and its signed charge is then compared in Real; Nat truncation is not equivalent.
- `Splay_Tree_Analysis_Optimal.thy:14–24` is a parameterized unweighted external-leaf analysis assuming three polynomial/powr inequalities with size variables at least one. Its interpretation at 296–305 uses base ∛4 and coefficient 1/3, yielding the `3/2 * log₂(size1 t)` access/splay-max estimates at 317–330. This is not a named consumer of the four `Lemmas_log` helpers and is not the weighted static-optimality theorem. It is not an excuse to add a weighted Jensen or general amortized-analysis framework here.

If a later small unit is selected, meaningful connected mathematical checks are these, without inventing an algorithm execution:

1. Specialize the sharp and strict bounds to arbitrary actual binary-tree external-leaf counts, using the existing count positivity, and retain the exact splay local residual expression that consumes the strict margin. This has no balance or payload-type assumption; nil has one external leaf.
2. Specialize the same sharp result to the pairing pass-one expressions `n₁+n₂+1` and `n₃+1`, then perform the existing arithmetic cancellation. Include the exact node/forest offset in the statement. The local numerical check is not the full pass-one execution/cost theorem.
3. Consume the skew weak bound directly for positive counts; separately show the actual signed potential boundary when the algorithm transition is eventually implemented. Do not manufacture a result-cost pair or derive runtime from value equivalence.

The independent case report additionally keeps precise boundary witnesses: `x=y=1/4` makes logarithms negative while the sharp and strict results remain true; `x=y=1` shows the `+2` sharp bound cannot be made strict; `x=0,y=1/4` refutes weakening positive domains; `x=y=1` refutes the shifted-minus-one result despite all its displayed log arguments being positive. At `x=y=2`, that last result is the nontrivial polynomial comparison `8 ≤ 9`. Base 4 at x=y=1 refutes carrying the base-2 margin unchanged; base 1/2 refutes increasing-log use for the skew bound. These calculations test the actual mathematical premises and constants, not compilation.

C21-085's source insertion fact `log₂(s+1) ≤ log₂ s + 1` for `s ≥ 1` is another direct product/monotonicity client: `s+1 ≤ 2*s`. Preserve its empty/nonempty split instead of changing it to an all-sizes statement. C21-091/092 still require the actually retained output state and original-size, state-dependent budgets. C22-062 retains initial potential. C23-058 retains its literal empty/singleton pass costs. C19-016's telescoping statement and all chapter algorithm/cost/correctness obligations remain queued and unchanged.

## 8. Proposed minimum statements, import boundary and limits

The following signatures are **proposals only**, to make the recommendation concrete; these names do not exist and are not frozen public API:

```lean
-- Possible namespace Resources.LogarithmBounds; ordinary Real statements only.
theorem logb_two_sum_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  Real.logb 2 x + Real.logb 2 y + 2 ≤ 2 * Real.logb 2 (x+y)

theorem logb_two_sum_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  1 + Real.logb 2 x + Real.logb 2 y < 2 * Real.logb 2 (x+y)
```

They require only the concrete Real domain and two positive inputs. The second is a meaningful consumer corollary, not another independent proof. No new operation, record, global instance, finite sum abstraction or theorem family is proposed. A later chosen module should retain normal project warning policy and source attribution, with the exact original theory provenance/license from the stopped source report. This preparation neither copies a source implementation nor changes any existing notice.

Do not add wrappers for `logb_mul`, positivity of `n+1`, Nat casting, monotonicity, `logb_nonneg`, `Nat.log`/`clog`, or XP01. If the shifted-product source law is included in a future bounded scope, decide explicitly whether it is a checked application or a stronger named product bound; its source's extra `1` must stay visible in correspondence. The fourth helper is understood and retained as later-source preparation rather than promoted merely because it shares a source file. No base, file list, acceptance gate or implementation release is chosen here.

The exact proof scripts remain uncompiled. Expected routine proof work is grouping products/additions, supplying positive/nonzero premises, and distinguishing natural from real powers and natural from signed subtraction. No result relies on tactic success as evidence; the mathematical certificates and exact existing theorem shapes above are the justification for feasibility. Source bridge/cost obligations are substantive remaining work, not elaboration details.

## 9. Readback and inspection record

The source assessment used only pinned/local primary inputs and read-only project commands. In addition to the full files and ranges noted above, the exact logarithm, concavity, AM–GM and cast declaration ranges were read directly; no statement was inferred from a search hit alone. Source identities for those larger pinned modules are:

| Pinned Mathlib file | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| `Analysis/SpecialFunctions/Log/Basic.lean` | 28,165 / 713 | `11c6334aeb0f1a4919fce9e9b4b3a4cc65d53e3f19e65b02ae79d215f07aee4d` |
| `Analysis/Convex/SpecificFunctions/Basic.lean` | 10,888 / 239 | `809d8e40e5ab931ec4254ae9068e9fb5a4a7c19e95d3fddcc9f4ad81028faef1` |
| `Analysis/Convex/Function.lean` | 52,116 / 1,144 | `909dc29c14a92dfe5519a0388d58dad48abe02b4947a4c7afb3d473b43d98320` |
| `Analysis/MeanInequalities.lean` | 68,632 / 1,237 | `a64a0dd3f9a361d07f223cfccca52f4255a927cf29d7ed1d484c57c0c51765fd` |
| `Data/Nat/Cast/Defs.lean` | 6,965 / 190 | `5656ed14933f402c33cbe3f1cc3eb7b26e4df670c573187fb7d0972eef4e3118` |
| `Data/Nat/Cast/Order/Basic.lean` | 4,608 / 162 | `6522497dba7222b8b2eee227c661bd774c302ee5fdd57c0d62e79633e8557876` |
| `Data/Nat/Cast/Order/Ring.lean` | 3,513 / 108 | `005f95e3c0d18bc11034eff9c7f726e719d61cac7d8fafa1e739096d6d4da255` |
| `Data/Int/Cast/Basic.lean` | 4,073 / 129 | `6a29d27ee152978ab13cd59ce30764b0e301f060e2790263b71a800be88d9588` |

Ordinary file digests identify the inspected bytes; they authenticate neither a compiler run nor a mathematical acceptance decision. The complete report received source/mathematical readback, followed by a final complete read of the corrected text before the stopped handoff for root's assessment/checkpoint. All other files, source drafts, refs, caches, active C1 outputs and original inventories remain unchanged by this task.
