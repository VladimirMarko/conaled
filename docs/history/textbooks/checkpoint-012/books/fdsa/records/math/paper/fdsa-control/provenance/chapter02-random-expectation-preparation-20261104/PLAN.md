# Random quicksort: bounded finite-expectation and actual bind-mean plan

Prepared 2026-11-04 after checkpoint 0088 was saved and exposed. **Plan only;
no new Lean source, compiler attempt, source/ref/cache write, or acceptance.**
Root must review and release this saved plan before implementation. The exact
inputs, dependency pins, source/API hashes, evidence and independent arithmetic
are recorded in [identity.json](identity.json).

## 1. Current checked boundary and minimum implementation files

The held clean author base is `bb4fb243bb7b16ae8bef921fec479a86f2b01c90`.
The identical initial random resource/example bytes passed the closed focused
attempt at central `dfaf68114d1dda4e15628c94c3d988c3f5457c49`. All 62 random
public declarations passed explicit type inspection, and the complete 509+203
source lines/proofs and 1,188-line type section received author readback.
See [the readback and terminal-evidence record](../chapter02-xd01-random-types-20261104/random-author-readback.md).
This preserves the prior actual failures; it is not full-candidate acceptance.

After a separate code release, add exactly this bounded source pair:

| Proposed file | Purpose |
| --- | --- |
| `Applications/Resources/RandomQuickSortMean.lean` | Finite lower expectations and genuine real integrability of the existing cost laws; actual occurrence-average mean equation; same-run append-inclusive mean comparison; base and all-false mean laws. |
| `Examples/RandomQuickSortMean.lean` | Independent expected constants connected to the existing checked actual distributions, arbitrary payload universes, and the duplicate-key limitation. |

Keep the existing `RandomQuickSort.lean` and its examples unchanged. The public
namespace remains `Resources.RandomQuickSort`; the example namespace is
`Examples.RandomQuickSortMean`. No new generic mean record, probability
carrier, execution framework, or independently recursive cost law is needed.
A new author base supplied by root would require a new exact identity before
use; do not silently follow the central development branch.

The production module directly reuses `Applications.Resources.RandomQuickSort`
and the pinned Mathlib PMF/integral APIs below. The example module may import
`Examples.RandomQuickSort` to use its public, already connected finite laws.
No production module imports `Examples`, and no client refers to the previous
module's private helpers. New shared probability drafts are not dependencies.

The proposed narrow Mathlib import set starts with
`Mathlib.Probability.ProbabilityMassFunction.Integrals`,
`Mathlib.MeasureTheory.Integral.Lebesgue.Countable`,
`Mathlib.MeasureTheory.Function.L1Space.Integrable`,
`Mathlib.MeasureTheory.Integral.Bochner.Basic`, and
`Mathlib.Basic.ENNReal.BigOperators`, as needed by the exact proof use sites.
Their inspected dependencies provide the ENNReal infinite-sum tools.
This is a source-inspected candidate import set, not a compiled minimal-import
certificate. Do not import root `Mathlib` or a different dependency version.

## 2. Exact distributions and public meaning

Let `n = xs.length`. In this document only, abbreviate the existing actual
laws by

```
P_T(lt,xs) = exerciseLaw lt xs
          = (run lt xs).map (fun result => result.2.1)
P_F(lt,xs) = literalLaw lt xs
          = (run lt xs).map (fun result => result.2.1 + result.2.2).
```

These are already `PMF Nat`, not invented substitutes for `run`. Use the
standard measurable structure on Nat and `PMF.toMeasure`. Introduce only the
two algorithm-specific real observation names, with these proposed shapes:

```lean
noncomputable def exerciseMean {α : Type u}
    (lt : α → α → Bool) (xs : List α) : ℝ :=
  ∫ k : Nat, (k : ℝ) ∂(exerciseLaw lt xs).toMeasure

noncomputable def literalMean {α : Type u}
    (lt : α → α → Bool) (xs : List α) : ℝ :=
  ∫ k : Nat, (k : ℝ) ∂(literalLaw lt xs).toMeasure
```

All finite-expectation and recursive-mean results below work for arbitrary
`α : Type u` and arbitrary Boolean comparator. They need no payload
`Inhabited`, `DecidableEq`, `Finite`, `Fintype`, `Countable`, `MeasurableSpace`,
or order instance. No sortedness or key-distinctness premise is needed for
this slice. Key assumptions enter later order/rank results or the specialization
of an already explicit all-false comparison hypothesis.

T is the Exercise 2.4 observation, including empty-call cost 1 and two actual
unit-predicate filters. F is T plus the actual right-associated append calls.
Both exclude pivot sampling implementation, index lookup/removal and random
bits. A PMF denotes probability; it is not itself a verified random-bit sampler.
The exact harmonic target belongs to T; an eventual F bound uses its separately
proved same-run comparison, not an asserted identical exact mean formula.

## 3. Existing interfaces reused and their limits

| Verified source interface | Actual use in this slice |
| --- | --- |
| `Resources.RandomQuickSort.exerciseLaw_cons` | Exact distribution recursion obtained by mapping the actual measured run. This is the only source recurrence used for the exercise mean. |
| `exerciseLaw_support`, `literalLaw_support` | Actual support lies below explicit natural cost bounds. These prove finite lower expectations before any real linearity is used. |
| `literalCost_comparison`, `jointCostLaw_of_all_false`, `jointCostLaw_of_constant_key` | Same-execution observations and duplicate joint laws; these preserve coupling when transporting costs. |
| `PMF.bind_apply`, `PMF.pure_apply`, `PMF.map`, `PMF.tsum_coe` | Nonnegative weighted bind/map identities and normalization, with arbitrary source/target universes. |
| `ENNReal.tsum_comm`, `tsum_mul_left`, `tsum_mul_right`, `tsum_add`, `tsum_le_tsum` | Rearrange or compare nonnegative sums without real summability or independence premises. |
| `lintegral_countable'`, `PMF.toMeasure_apply_singleton` | Identify an actual Nat-law lower integral with its PMF-weighted sum. |
| `measurable_of_countable`, `integrable_toReal_of_lintegral_ne_top` | Prove measurable Nat observations and genuine real integrability from the finite lower expectation. |
| `integral_toReal` | Identify each already justified real mean with the lower integral's `toReal`. This theorem alone is not an integrability certificate. |
| `ENNReal.toReal_add`, `toReal_sum`, `toReal_mul`, `toReal_inv`, `toReal_mono` | Transport the finite lower-mean identities and bounds to real arithmetic, supplying all required finiteness premises. |
| `PMF.integral_eq_tsum`, `PMF.integral_eq_sum` | Existing real expectation interfaces. The first requires explicit integrability; the second applies to finite pivot indices, not to Nat merely because a PMF has finite support. |

`PMF.toMeasure.isProbabilityMeasure` already proves total mass one. Mathlib's
`average_eq_integral` and `laverage_eq_lintegral` confirm that normalized
averages on these probability measures coincide with the chosen integrals;
no new generic expectation abstraction or `Average` import is required.

The existing `Applications.Probability.Table`/`lintegral_kernel` route uses
finite stochastic tables. Repackaging this already defined PMF as a table
would add a representation and correspondence obligation, with no benefit
for the present calculation. `ProbabilityProgress.Execution` and `Results`
model a fixed random environment, machine execution, and termination; they do
not supply this PMF's actual mean bridge. Replacing the current run by those
interfaces would require a separate execution correspondence and stronger
state/result infrastructure.

The XW01 `AccumulatedWork` draft assumes an integrated drift inequality for
supplied observations. XU04 `PermutationExpectation` proves means of fixed
subset statistics under a uniform global permutation, and explicitly uses
finite-sample integrability. Its `Integrable.of_finite` proof cannot simply
be copied onto the infinite Nat carrier. Neither draft supplies the direct
fresh-pivot mean. XU01–XU03 will matter for the separate uniform-input route
as recorded in the existing dependency handoff; none is imported here.
These are source/API assessments, not acceptance decisions for those drafts.

## 4. Finite lower expectations and genuine integrability

In this plan, B and U are just abbreviations for natural arithmetic:

```
B(n) = 2*n^2 + 2*n + 1
U(n) = (5*n^2 + 9*n + 2) / 2    -- natural floor division, before casting
```

Prove the two public algorithm-specific bounds:

```lean
(∫⁻ k : Nat, (k : ℝ≥0∞) ∂(exerciseLaw lt xs).toMeasure) ≤ (B n : ℝ≥0∞)
(∫⁻ k : Nat, (k : ℝ≥0∞) ∂(literalLaw lt xs).toMeasure) ≤ (U n : ℝ≥0∞)
```

A small private lemma for `p : PMF Nat` and `p.support ⊆ Set.Iic b` suffices.
Use `lintegral_countable'` and measurable singletons to obtain
`∑' k, p k * (k : ENNReal)`. For each k, if `p k = 0`, the summand is zero;
otherwise `PMF.mem_support_iff` and the support inclusion imply `k ≤ b`.
Compare termwise with `p k * (b : ENNReal)`, then use
`ENNReal.tsum_mul_right` and `PMF.tsum_coe` to get the finite bound b.
This also directly exhibits why the actual support bound matters. Merely
knowing each run terminates or each sampled cost is a natural is insufficient
to deduce a finite expectation.

Derive the explicit lower-integral `≠ ∞` facts from these bounds and
`ENNReal.natCast_ne_top`. Prove both public integrability contracts:

```lean
MeasureTheory.Integrable (fun k : Nat => (k : ℝ))
  (exerciseLaw lt xs).toMeasure
MeasureTheory.Integrable (fun k : Nat => (k : ℝ))
  (literalLaw lt xs).toMeasure
```

For each, `measurable_of_countable (fun k : Nat => (k : ENNReal))` supplies
measurability. Apply `integrable_toReal_of_lintegral_ne_top`, then rewrite
`ENNReal.toReal_natCast`. Only after these results are proved, use
`integral_toReal` and pointwise finiteness of Nat casts to expose

```
exerciseMean lt xs = (∫⁻ k, (k : ENNReal) ∂P_T.toMeasure).toReal
literalMean lt xs  = (∫⁻ k, (k : ENNReal) ∂P_F.toMeasure).toReal.
```

Retain real nonnegativity and the corresponding bounds `exerciseMean ≤ B n`
and `literalMean ≤ U n` for later clients. The cast of U must preserve its
natural division. These polynomial bounds prove integrability; they are not
the claimed distinct-key average `O(n log n)` theorem.

## 5. Private weighted bind/map bridge, with actual recursion

Keep the needed convenience lemmas private. For arbitrary types α and β,
`p : PMF α`, `f : α → PMF β`, and `g : β → ENNReal`, prove

```
∑' b, (p.bind f) b * g b = ∑' a, p a * (∑' b, f a b * g b).
```

Expand `PMF.bind_apply`; distribute the right factor through the inner sum;
commute the two ENNReal sums; reassociate products; factor out `p a`.
The exact pinned sum APIs above already justify these steps even for
nonfinite source types. Derive the pure and map specializations:

```
∑' b, (PMF.pure x) b * g b = g x
∑' b, (p.map h) b * g b = ∑' a, p a * g (h a).
```

The map identity requires no measurable structure on the source carrier.
Also use normalization to show the weighted mean of a constant is that
constant, and distribute sums of nonnegative observations. There is no new
public `Mean` carrier or independent cost recursion in this step.

For `xs = head :: tail`, put `m = tail.length` and, for each actual sampled
`i : Fin (m+1)`, define in the theorem's local expression:

```
pivot_i = xs[i.val] using i.isLt
rest_i  = xs.eraseIdx i.val
left_i  = rest_i.filter (fun x => lt x pivot_i)
right_i = rest_i.filter (fun x => !(lt x pivot_i)).
```

`exerciseLaw_cons` states exactly that the actual parent law binds
`uniformIndex m`, then `P_T(lt,left_i)`, then `P_T(lt,right_i)`, and returns
`leftCost + rightCost + 4*rest_i.length + 3`.
Apply the private weighted-bind lemma successively to these actual binds.
The weighted pure case exposes that returned sum; normalization of each
child PMF removes the unused other-child factor. This derives, first in
ENNReal, the finite occurrence average of
`lowerMean(left_i) + lowerMean(right_i) + 4*rest_i.length + 3`.
No external `IndepFun` hypothesis, assumed conditional distribution, global
priority coupling, or fresh resampling replacement is introduced.

Use `uniformIndex_apply` and `tsum_fintype` for the finite outer average.
`List.length_eraseIdx_add_one i.isLt` proves `rest_i.length = m`, so the
local toll can be placed outside the normalized finite sum. Each child lower
mean is finite by section 4, independently of the parent's mean recurrence.
Apply `ENNReal.toReal_sum`/`toReal_add` with those concrete finiteness facts,
then `toReal_mul`/`toReal_inv` and the real-mean transport above.

The main proposed public equation, `exerciseMean_cons`, is exactly:

```
exerciseMean lt (head :: tail) =
  (((m+1 : Nat) : Real)⁻¹) *
    ∑ i : Fin (m+1),
      (exerciseMean lt left_i + exerciseMean lt right_i)
  + ((4*m+3 : Nat) : Real).
```

The actual indexed remainder/filter expressions must occur on the right-hand
side (or unfold from transparent local lets), not unspecified lists of those
lengths. This theorem is valid with duplicates and for any Boolean comparator.
The denominator is positive because m+1 is the current nonempty length.
The empty law is handled separately; there is no uniform distribution on
`Fin 0` or division-by-zero argument.

Conditional on a root index, the child input lists here are the actual fixed
partitions of that remainder. Their subsequent pivots are freshly sampled by
`run`; their input orders are not being declared uniformly random. The later
length-only induction will use this exact equation and a proved rank bijection.

## 6. Preserve same-run coupling for the append-inclusive mean

Prove the public comparison, for every lt and xs:

```
exerciseMean lt xs ≤ literalMean lt xs ∧
  literalMean lt xs ≤ 2 * exerciseMean lt xs.
```

The two marginal laws use different measures, so an application of integral
monotonicity directly across those measures would be invalid. Instead apply
the private weighted-map identity twice. It expresses their lower means as
weighted observations over the same actual `run lt xs`:

```
Σ result, run lt xs result * (T(result) : ENNReal)
Σ result, run lt xs result * (T(result)+A(result) : ENNReal).
```

For a supported result, use the existing `literalCost_comparison`. For an
unsupported result the common weight is zero. ENNReal sum monotonicity and
constant-factor extraction give the two lower-mean inequalities. Both sides
are finite by section 4, so `toReal_mono` transfers them to the actual real
means. This needs neither a measurable payload universe nor a new joint-measure
adapter. The common run is an explicit, checked coupling; no independence or
coupling premise is supplied by the client.

For the duplicate family, map the existing actual joint cost law
`jointCostLaw_of_all_false` by the first projection and by `(t,a) ↦ t+a`.
The resulting pure Nat laws give

```
exerciseMean lt xs = (2*n^2+2*n+1 : Nat)
literalMean lt xs  = (2*n^2+5*n+1 : Nat)
```

with the explicit hypothesis `∀ a ∈ xs, ∀ b ∈ xs, lt a b = false`, and with
both right sides cast to Real. Key-constant and replicate clients specialize
that hypothesis or the already checked key-constant joint law. Different tags
with equal keys remain within the quadratic family; output order may vary.

## 7. Independent connected cases, fixed before implementation

The expected right-hand constants below were calculated from the source tariff
and initial checked finite laws, before authoring the new proofs. The identity
file records exact rational arithmetic. Each new example must assert the
actual `exerciseMean`/`literalMean` integral, not just prove these numbers
satisfy an unrelated recurrence.

| Input/case | Expected T mean | Expected F mean | Connection to actual execution |
| --- | ---: | ---: | --- |
| Empty input with payload `Empty` | 1 | 1 | Existing pure empty cost laws; no inhabited payload. |
| Singleton, arbitrary payload universe and comparator | 5 | 8 | Existing actual singleton observation (5,3). |
| `[0,1]`, ordinary strict Nat comparison | 13 | 39/2 | `two_key_exercise`; `two_key_execution` gives total costs 19 and 20, each with mass 1/2. |
| `[0,1,2]`, ordinary strict Nat comparison | 71/3 | No new exact F claim required here | `three_key_exercise_law`: the midpoint costs 21 with mass 1/3; two endpoints cost 25 with total mass 2/3. |
| Two distinct tags with equal key 7 | 13 | 19 | Existing actual constant-key joint cost is pure (13,6), despite the variable output order. |
| Three equal keys | 25 | 34 | Existing actual pure execution (25,9). |
| Arbitrary list of tags, all key 7, length n | `2*n^2+2*n+1` | `2*n^2+5*n+1` | General actual joint law; no tag equality, finiteness or measurable structure. |

For the two-key case, the independent tariff calculation is `1+5+7=13`.
The append counts are 6 or 7, so the literal mean is `(19+20)/2=39/2`.
For three distinct keys, the local toll is 11. A midpoint gives `5+5+11=21`;
an endpoint gives `1+13+11=25`; hence `(21+25+25)/3=71/3`.
These cases catch a missing empty call, a one-filter tariff, integer mean
truncation, or an unconnected comparison-count formula.

Add arbitrary-payload clients of the two real integrability theorems and the
same-run mean comparison. Use the existing repeated-occurrence event (2/3)
and instability witness as retained boundary evidence; no source changes are
needed to re-prove them. Exact size-four-and-larger means and a full three-key
joint distribution would enlarge this slice and are not required to establish
its universal finite-mean/actual-bind identities.

## 8. Mandatory later work: rank, recurrence, harmonic, both averages

This slice supplies the actual occurrence-average equation, not a length-only
average theorem. The next direct-random proof must still establish:

1. For `[LinearOrder κ]`, a fixed key map `key : α → κ`, and
   `(xs.map key).Nodup`, the selected occurrence's number of strictly smaller
   input keys defines a bijection of `Fin xs.length` with the rank indices.
   Child left length equals that rank; child right length equals
   `xs.length-1-rank`; both actual filtered lists inherit distinct keys.
   Distinct payload tags alone do not establish this hypothesis.
2. Reindex the actual finite mean sum through that proved bijection and use
   strong induction on the actual input length. This proves that the mean
   depends only on length within the distinct-key domain, with
   `A_0=1` and `A_n=(2/n)*Σ_{k<n} A_k + 4*n-1` for positive n.
   Do not introduce this equation as an assumption or replace the current
   PMF by an independently defined numerical cost law.
3. Prove the connected exact formula
   `A_n = 8*(n+1)*(harmonic n : Real) - 12*n + 1`.
   Reuse the pinned `harmonic` and its recurrence; n=0 and the first positive
   recurrence are explicit boundary cases. The target successor relation is
   `n*A_n=(n+1)*A_(n-1)+8*n-5` on the proved positive domain.
4. Reuse `harmonic_le_one_add_log` for a real logarithmic bound, then a
   genuine eventual `O(n log n)` result. The retained plan gives
   `A_n ≤ 16*n*(1+log n)` for n≥1 and, for n≥2, an n*log n constant
   `16*(1+1/log 2)`. Connect this to the actual random mean and then transfer
   the appropriate bound to F using section 6. Keep logarithm domain and
   change of base to the book's lg explicit.
5. Separately prove the deterministic first-pivot uniform-input mean. Its
   minimal source dependencies are the measured deterministic sorter and
   XU02/XU03 conditional marginal laws, with the existing historical acceptance
   prerequisites. Actual label/payload cost transport, conditional child-list
   identification, integrability and head-event normalization remain required.
   The random-pivot result does not establish this other experiment by itself.

The frozen average plan, probability dependency handoff and all **112 Chapter
2 obligations** retain their force. The exact-mean checks 1,5,13,71/3 agree with
that plan, but numerical agreement never supplies a missing execution proof.
Uniform pivot selection/removal overhead may preserve asymptotic order after
an explicitly measured comparison; its tariff and proof remain separate.
Physical runtime and random-bit complexity are not consequences of the current
probability denotation. No scope is closed by this preparation.

## 9. Implementation and validation boundary after release

Root reviews this complete plan first. On later source release, implement the
two files in the clean held author worktree, preserving exact pins, proof
restrictions and the current source. Commit a coherent bounded candidate,
record its complete diff and assumptions, and return it to root for the sole
central focused compiler. Do not build or share writable cache/output trees.
Compiler corrections must retain definitions, hypotheses, tariffs and cases.

The source and elaborated-type readback must explicitly check genuine
integrability, the exact occurrence/remainder/child terms, arbitrary payload
universes, and absence of a hidden rank/independence/mean-recurrence premise.
A focused pass is only the next diagnostic gate. Normal-versus-fresh rules,
full immutable-candidate checking and audit, both independent Standards and
Spec reviews, and immediate `./check.sh --verify-candidate HEAD` before local
acceptance remain mandatory. Preserve Chapter 1 at
`07e480f6ec9958d4975bb90151005b84f2907614`; this child has not accepted the
foundation candidate `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.

This preparation writes only this plan and its identity. It changes no Lean
source, ref, cache, ticket, coverage row or prior review evidence. After saving,
the author holds all writes pending root's review and explicit next release.
