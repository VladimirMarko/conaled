# Random-pivot execution: pinned PMF API preflight

## Status and bounded recommendation

This is read-only preparation for the retained Chapter 2 randomized assertion, not a frozen interface, implementation, validation result or chapter activation. No Lean source, Git state, dependency, cache, compiler, project hash helper or running gate was changed. The report path was absent before this write. Proposed names and statements below are proposals only.

The smallest sound route is an ordinary `PMF (Resources.Measured (List α) Nat)` whose recursive branches choose a valid occurrence index, erase exactly that occurrence, perform the source's two measured filters, and bind the two recursive executions. Project this actual result to `PMF Nat` before introducing a measure. That avoids payload equality, inhabitation, finite enumeration, order and measurability assumptions in the operation. Source order laws and distinct-key hypotheses belong to the correctness and average-cost theorems.

The inspected PMF modules already provide normalized finite construction, heterogeneous `bind`/`map`, support laws and conversion to probability measures. The small missing analytic convenience is a weighted ENNReal tsum identity for `bind`; it can initially be a private lemma derived from the existing tsum APIs. A new probability carrier, stochastic executor, expectation record, independence framework or cost-only recursive stand-in is unnecessary.

This report deliberately leaves the deterministic first-pivot algorithm averaged over a uniform input permutation, and its conditional-mean induction, to the separate root-owned plan. It does not claim equality between that experiment, a shared global ranking, and the fresh random-pivot execution described here.

## Evidence and source model

Primary inspected sources are local, pinned copies:

| Source | Identity and relevant location |
| --- | --- |
| FDSA, July 27, 2026 | PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; `book-source/chapter02.txt`, §2.3 printed p.16 and Exercise 2.4 printed pp.28–29. |
| Isabelle companion | `book-source/Sorting.thy`, lines 327–339, at Isabelle `f86f290225eebcc52c1ae7dba2e098f405f51c21`; file SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. |
| AFP comparison-count reference | `book-source/afp_quicksort_cost_2026_10_26/Randomised_Quick_Sort.thy`, definition/termination at lines 82–102 and `snd_rquicksort` at 200–202. Dated archive and file receipts are in `fdsa-control/provenance/afp-quicksort-cost-source.json`; archive SHA-256 `cda7ed0a00991dcf8a5adff2d9909d6e761b2d8fb9501425ed8b93dbf462f457`. |
| Mathlib | Pin `56a005855ea17e0b0958f73ec801ae140b0a1679`, inspected through `conaled-permutation-joint/.lake/packages/mathlib/Mathlib/`; source paths below are relative to `Mathlib/`. |
| Existing conaled operations | `conaled-permutation-joint/Applications/Resources/Measured.lean`, `CallCount.lean`, `Applications/Probability/FiniteKernel.lean` and `Applications/Selection/Rank.lean`. |
| Shared measured-list draft | `conaled-insertion-costs/Applications/Resources/ListCalls.lean`, originating in the saved shared list foundation chain; no acceptance is implied. Its eventual use is subject to the Chapter 1 repair and shared-integration prerequisites. |
| Prior mathematical scope | `fdsa-control/research/quicksort-average-proof-plan.md` and `probability-source-preflight.md`; their existing calculations and retained mathematical obligations are reused, not rerun. |

The book sends values strictly below the pivot left and values at least the pivot right. Its value expression contains two appends. Exercise 2.4 deliberately specifies a narrower observation: empty call cost 1, two recursive costs, two complete filter traversals with unit callback observation, and one current-call tick. It does not charge either append. For a nonempty input of length `m + 1`, the exact accounting is:

| Component | Exercise 2.4 observation |
| --- | ---: |
| Each measured filter on the erased list of length `m` | `2 * m + 1` |
| Two recursive calls | Their actual returned observations |
| Current quicksort entry | `1` |
| Abstract random choice, pivot lookup and occurrence deletion | `0` in this explicitly chosen source observation |
| Both output appends | `0` in Exercise 2.4 |

Thus the nonrecursive charge is `4 * m + 3`, equivalently `4 * n - 1` for positive total length `n`. The first form avoids truncated subtraction and is the preferable recursive equation. In particular the singleton cost is 5. Replacing the two filters by one partition traversal gives the same partition values but does not establish this source-cost correspondence.

AFP's actual randomized algorithm is useful evidence for occurrence sampling and strict length termination, but it counts comparisons, has empty observation 0, and partitions with membership in a supplied relation. Its later ordered specialization puts ties on the other side from the book. `snd_rquicksort` explicitly assumes `linorder_on A R`, membership of the input in `A`, and `distinct xs`. It is not an existing Lean theorem or an exact Exercise 2.4 cost implementation. On distinct keys, the strict/nonstrict difference disappears after removing the selected pivot; on duplicates it does not.

## 1. Positive finite occurrence choice

### Exact constructor and normalization

`Probability/ProbabilityMassFunction/Constructions.lean` supplies:

```lean
PMF.ofFintype [Fintype α] (f : α → ENNReal)
  (h : ∑ a, f a = 1) : PMF α

PMF.ofFintype_apply (h : ∑ a, f a = 1) (a : α) :
  PMF.ofFintype f h a = f a

PMF.mem_support_ofFintype_iff (h : ∑ a, f a = 1) (a : α) :
  a ∈ (PMF.ofFintype f h).support ↔ f a ≠ 0
```

Here `f` is implicit in the last two theorem signatures; the displayed `h, a` order is the source order. A proposed `uniformIndex (m : Nat) : PMF (Fin (m + 1))` uses the constant weight `(m + 1 : ENNReal)⁻¹`. The constructor needs an actual normalization proof, not an asserted finite-uniform instance. Reduce the finite sum to `(m + 1 : ENNReal) * (m + 1 : ENNReal)⁻¹`, then use:

```lean
ENNReal.mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1
ENNReal.natCast_ne_top (n : Nat) : (n : ENNReal) ≠ ∞
Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
```

The first two declarations are in `Basic/ENNReal/Inv.lean` and `Basic/ENNReal/Basic.lean`; `Fintype.card_fin` is in `Data/Fintype/Card.lean`. The nonzero premise follows from the successor cardinal. There is no request to choose an element of `Fin 0`; the empty sorting branch is `PMF.pure ([], 1)`. This also handles `List Empty` without inventing a default payload.

`PMF.ofFintype` and all PMF operations inspected are noncomputable probability denotations. A constructive valid index type does not turn the abstract distribution into a verified random-bit implementation. The similarly named finite-uniform measure API must not be mistaken for this PMF constructor.

### Reusable occurrence law

A minimal reusable statement is that an event on these indices has probability its finite event cardinality divided by `m + 1`. An event testing a Boolean predicate on the selected list entry therefore has probability the number of satisfying **occurrences** divided by list length. This can be stated on the existing `Fin` sample space, or on the PMF of the selected Boolean observation, so it needs no measurable structure or equality on `α`.

For a finite target, the exact existing pushforward theorem is:

```lean
PMF.map_ofFintype [Fintype α] [Fintype β]
  (f : α → ENNReal) (h : ∑ a, f a = 1) (g : α → β) :
  (PMF.ofFintype f h).map g =
    PMF.ofFintype (fun b ↦ ∑ a with g a = b, f a) ...
```

Use it for Boolean tests or a proved finite occurrence-to-rank bijection. Its **finite target** premise makes it unsuitable as a blanket theorem about arbitrary payload values or arbitrary list outputs. For the latter, ordinary `PMF.map_apply` remains available. If the input is `[a, a, b]` with `a ≠ b`, occurrence choice selects `a` with probability `2/3`, not `1/2`; a uniform draw from a deduplicated set is a different execution.

### Access and deletion without payload equality

For `xs = x :: tail` and `i : Fin (tail.length + 1)`, use the actual valid `xs[i.val]` (with the length proof) or `xs.get i` after the definitional length identification, and `xs.eraseIdx i.val`. The following inspected lemmas contain no payload equality or inhabitation assumption:

```lean
List.length_eraseIdx_add_one {l : List α} {i : Nat}
  (h : i < l.length) : (l.eraseIdx i).length + 1 = l.length

List.getElem_cons_eraseIdx_perm {n : Nat} (h : n < l.length) :
  l[n] :: l.eraseIdx n ~ l

List.length_filter_le (p : α → Bool) (l : List α) :
  (l.filter p).length ≤ l.length

List.length_eq_length_filter_add {l : List α} (p : α → Bool) :
  l.length = (l.filter p).length + (l.filter (!p ·)).length
```

The first and fourth are in `Data/List/Basic.lean`; the second is in `Data/List/Perm/Basic.lean`; the third is in the pinned Lean `Init.Data.List.Lemmas` source, saved as `book-source/LeanList-Lemmas.lean`. Together they give a strict bound for each child and the exact sum of child lengths. `List.erase`, which deletes by equality, is not needed. Nor is an arbitrary invalid-index extension: the `Fin` domain certifies the operation.

## 2. Actual measured recursive PMF

### Existing value and probability sequencing

`Resources.Measured α C` is the abbreviation `α × C`. Its `Resources.bind` allows the value types to lie in different universes and adds observations in execution order. `CallCount.tick` preserves the value and adds one to a Nat observation. These are the existing observation operations, not a request for a new probabilistic writer wrapper.

`Probability/ProbabilityMassFunction/Monad.lean` defines, with independent input/output types:

```lean
PMF.pure (a : α) : PMF α
PMF.bind (p : PMF α) (f : α → PMF β) : PMF β
PMF.bind_apply (p : PMF α) (f : α → PMF β) (b : β) :
  p.bind f b = ∑' a, p a * f a b

PMF.mem_support_bind_iff (p : PMF α) (f : α → PMF β) (b : β) :
  b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support
```

`pure_bind`, `bind_pure`, `bind_bind` and `bind_comm` are already available. In `Constructions.lean`, `PMF.map (f : α → β) (p : PMF α)` is literally `bind p (pure ∘ f)`; `map_bind`, `bind_map`, `map_comp` and `pure_map` provide ordinary transport laws. `PMF.mem_support_map_iff f p b` says exactly `∃ a ∈ p.support, f a = b`.

**Universe boundary:** write explicit `PMF.bind`/`PMF.map` at the transition from `PMF (Fin (m+1))` to `PMF (List α × Nat)`. The standard monadic notation fixes a universe and must not silently force `α : Type 0`. The pinned `Constructions.lean` documents `ULiftable.up` as the alternative when using `do` across universes, and defines `ULiftable PMF.{u} PMF.{v}` using ordinary maps. Explicit bind is the smaller proposal here; no public lift wrapper is needed.

### Proposed operation shape, not authored Lean

A proposed `randomQsort (before : α → α → Bool) (xs : List α)` returns `PMF (Resources.Measured (List α) Nat)`:

1. Empty input returns the actual pair `([], 1)` with `PMF.pure`.
2. On `x :: tail`, bind the positive `Fin (tail.length + 1)` distribution.
3. Read the chosen pivot and erase that precise index.
4. Form the left measured filter using callback `fun y => (before y pivot, 1)`; recurse on its actual value.
5. Form the right measured filter using callback `fun y => (!before y pivot, 1)`; recurse on its actual value.
6. Combine both actual recursive result values by the source append expression and combine their observations with the two filter observations and one `CallCount.tick`.

Keep both probability sequencing and measured sequencing explicit, with qualified names where `PMF.pure`/`Resources.pure` and the two binds could be confused. Merely naming the desired scalar recurrence beside an unrelated sort would not fulfill this execution obligation. Conversely, there is no source charge for invoking the semantic `PMF.bind` itself.

The exact measured-filter APIs already drafted are:

```lean
Resources.ListCalls.filterRun
  (p : α → Resources.Measured Bool Nat) (xs : List α) :
  Resources.Measured (List α) Nat

Resources.ListCalls.filterRun_value p xs :
  (filterRun p xs).1 = xs.filter (fun x => (p x).1)

Resources.ListCalls.filterRun_cost_of_constant p xs (c : Nat)
  (hc : ∀ x ∈ xs, (p x).2 = c) :
  (filterRun p xs).2 = (c + 1) * xs.length + 1
```

These are a genuine operation/value/cost connection. The constant callback hypothesis is local to reached occurrences. The proposed unit callbacks instantiate it at `c = 1` independently for each traversal.

### Termination and assumptions

Use well-founded recursion with `termination_by xs.length`. Each call is on a filtered erased list, so `filterRun_value`, `length_filter_le` and `length_eraseIdx_add_one` prove strict decrease. The relevant lengths are known before sampling any child result. No fuel, `partial`, `Inhabited α`, equality oracle, order instance or `bindOnSupport` is required to define the algorithm. A bounded elaboration risk remains: write the child-list lets and their length proofs so that the termination goals under the explicit bind lambdas expose exactly those lists. This is ordinary source proof work, not evidence that a compiler has accepted a proposed definition.

Use `before` and its complement in the operation so partition coverage is unconditional. The source specialization can take a key map `key : α → κ` and `before y p := decide (key y < key p)`; the law matching its complement to `key p ≤ key y` needs a total order on keys. No order on arbitrary payloads is necessary. A weaker on-input comparator compatibility contract is possible, but need not be invented for this preflight.

Sortedness and permutation are separate result-support laws. Randomly extracting an equal-key occurrence can move it before earlier equal-key occurrences, so stable-sort contracts cannot be imported without an appropriate qualification. For example, selecting the second of two distinct payloads with equal keys puts that selected payload first under the book's strict-left rule. This does not invalidate sortedness or permutation.

## 3. Support bounds and projection to an ordinary cost law

A proposed `costLaw before xs := PMF.map Prod.snd (randomQsort before xs)` is a `PMF Nat`. `PMF.map` itself has no measurable-space assumptions. Only this Nat result is converted to a measure; nothing requires a measurable space on `List α` or on `α`.

First prove the universal pathwise support statement, for `n = xs.length`:

```text
r ∈ (randomQsort before xs).support → r.2 ≤ B n,
where B n = 2*n*n + 2*n + 1.
```

This proposal holds for arbitrary Boolean `before`, including repeated keys, because the right predicate is its complement. Support induction uses `PMF.mem_support_bind_iff` and the singleton support of `PMF.pure`. For child lengths `a,b` with `a+b=m`, the induction step reduces to

```text
B a + B b + 4*m + 3 ≤ B (m+1),
```

whose gap is `4*a*b`. Thus no probabilistic averaging or order theorem is needed to establish finiteness of the eventual expectation. The cost-law support lies in the finite Nat interval from 0 through `B n`. A separate finite-support theorem for the whole payload-valued execution may be true, but is unnecessary for this mean proof and would enlarge the first unit.

The probability measure and its event/support connection are already supplied by `Probability/ProbabilityMassFunction/Basic.lean`:

```lean
PMF.toMeasure [MeasurableSpace α] (p : PMF α) : Measure α
PMF.toMeasure.isProbabilityMeasure (p : PMF α) :
  IsProbabilityMeasure p.toMeasure

PMF.toMeasure_apply_singleton p a (h : MeasurableSet {a}) :
  p.toMeasure {a} = p a

PMF.toMeasure_apply_eq_zero_iff p (hs : MeasurableSet s) :
  p.toMeasure s = 0 ↔ Disjoint p.support s

PMF.toMeasure_apply_eq_one_iff p (hs : MeasurableSet s) :
  p.toMeasure s = 1 ↔ p.support ⊆ s
```

All subsets of the standard countable discrete Nat space are measurable. The support bound therefore gives an almost-everywhere bound on the Nat observation and a lower-integral bound by the finite cast of `B n`. No finite-enumeration assumption on the payload universe is hidden in that argument.

## 4. Expectation identities already sufficient

### A small local bind identity

A bounded search of `Probability/ProbabilityMassFunction/` found the integral conversion theorems below, but no direct bind-expectation theorem. The following is a proposed private convenience lemma, not a new definition of expectation:

```lean
-- Proposed; arbitrary carriers and no measurable-space assumptions.
∑' b, (p.bind f) b * g b =
  ∑' a, p a * (∑' b, f a b * g b)
```

Here `p : PMF α`, `f : α → PMF β`, and `g : β → ENNReal`. Expand `PMF.bind_apply`, move the factor through the inner sum, commute the two sums, reassociate multiplication, and factor out `p a`. The exact pinned tools in `Topology/Algebra/InfiniteSum/ENNReal.lean` are:

```lean
ENNReal.tsum_comm :
  (∑' a, ∑' b, h a b) = ∑' b, ∑' a, h a b
ENNReal.tsum_mul_left : (∑' i, a * f i) = a * ∑' i, f i
ENNReal.tsum_mul_right : (∑' i, f i * a) = (∑' i, f i) * a
ENNReal.tsum_add : (∑' i, f i + g i) = (∑' i, f i) + ∑' i, g i
PMF.tsum_coe (p : PMF α) : (∑' a, p a) = 1
```

These nonnegative identities do not require a finite carrier, real summability or independence assumptions. The analogous map identity follows by taking `f a = PMF.pure (h a)`. In particular it connects the lower expectation of the actual cost projection to the weighted observation of the actual payload-valued execution.

For the recursive algorithm, apply the bind identity at the pivot and the two child draws. Additivity plus each PMF's normalization reduces the child terms to their respective means and the constant `4*m+3`. The chosen execution does specify fresh conditional draws by its bind structure; a separate theorem identifying a joint cost distribution or proving `IndepFun` is not needed merely to derive this mean equation. This does not excuse a conditional-law proof for a different history-dependent experiment.

### Existing lower-integral and real-integral transport

`MeasureTheory/Integral/Lebesgue/Countable.lean` supplies:

```lean
MeasureTheory.lintegral_countable'
  [Countable α] [MeasurableSingletonClass α] (f : α → ENNReal) :
  (∫⁻ a, f a ∂μ) = ∑' a, f a * μ {a}

MeasureTheory.lintegral_fintype
  [MeasurableSingletonClass α] [Fintype α] (f : α → ENNReal) :
  (∫⁻ a, f a ∂μ) = ∑ a, f a * μ {a}
```

With `p : PMF Nat`, the first theorem and `PMF.toMeasure_apply_singleton` identify `∫⁻ k, (k : ENNReal) ∂p.toMeasure` with the weighted tsum. Multiplication commutativity reconciles its displayed `f k * p k` orientation with the bind lemma's `p k * f k`. For the finite pivot sample the second theorem gives an ordinary finite average.

**Real expectation needs genuine integrability evidence.** The exact theorem in `MeasureTheory/Function/L1Space/Integrable.lean` is:

```lean
MeasureTheory.integrable_toReal_of_lintegral_ne_top
  {f : α → ENNReal} (hfm : AEMeasurable f μ)
  (hfi : (∫⁻ x, f x ∂μ) ≠ ∞) :
  Integrable (fun x ↦ (f x).toReal) μ
```

For `f k = (k : ENNReal)`, measurability follows from the existing `measurable_of_countable`, and the support bound proves `hfi`. Simplifying the Nat casts gives integrability of `fun k : Nat => (k : Real)`. Then `MeasureTheory/Integral/Bochner/Basic.lean` supplies:

```lean
MeasureTheory.integral_toReal {f : α → ENNReal}
  (hfm : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, f x < ∞) :
  (∫ x, (f x).toReal ∂μ) = (∫⁻ x, f x ∂μ).toReal
```

The pointwise Nat casts establish `hf`. This theorem by itself does not certify integrability: infinity and an undefined Bochner integral are totalized. The separate finite-mean/integrability proof is consequential and must remain part of the result.

`Probability/ProbabilityMassFunction/Integrals.lean` also gives, under measurable singleton and complete normed real-space assumptions:

```lean
PMF.integral_eq_tsum (p : PMF α) (f : α → E)
  (hf : Integrable f p.toMeasure) :
  (∫ a, f a ∂p.toMeasure) = ∑' a, (p a).toReal • f a

PMF.integral_eq_sum [Fintype α] (p : PMF α) (f : α → E) :
  (∫ a, f a ∂p.toMeasure) = ∑ a, (p a).toReal • f a
```

The finite version applies to the pivot index type, not directly to `PMF Nat`. The tsum theorem applies to the projected cost law after the integrability proof. Either real route is available; there is no need to repackage these as a general public expectation interface.

## 5. Remaining algorithmic bridges and connected cases

The direct distinct-key mean proof still needs an actual occurrence-to-rank bijection. For `n > 0`, assign each valid occurrence the number of input keys strictly below its key. Under `(xs.map key).Nodup`, this is a bijection of `Fin n`, the chosen left child has that rank as its length, and the complementary right child has length `n - 1 - rank`. Reindex the uniform finite sum through this proved bijection. Child lists inherit key distinctness, so strong induction applies to their actual means regardless of their input order.

Existing `Applications.Selection.RankedAt`, `pairwise_ranked`, `ordered_perm`, `ordered_pairwise` and `ranked_iff_index` connect zero-based ranks to sorted occurrence lists. They do not already state the needed strict-count occurrence bijection or a uniform-pivot theorem. Reuse their sorted/permutation contracts if useful, but do not rename them as a completed probabilistic bridge. No global `DecidableEq α` is needed; key order and the local distinctness premise suffice.

Once the actual finite mean is proved, its distinct-key recurrence is

```text
A 0 = 1
A n = (2/n) * sum (A k, k < n) + 4*n - 1,  n > 0.
```

The prior quicksort proof plan retains the proposed exact real solution `8*(n+1)*harmonic n - 12*n + 1` and logarithmic bound. Prove the ENNReal bind/additive equations first, then work in Real after justified transport for subtraction and the harmonic calculation. This report does not turn a scalar recurrence proof into a theorem about the algorithm without the cost/mean correspondence above.

The smallest meaningful eventual cases are:

| Case | Connected obligation |
| --- | --- |
| Empty list, including payload `Empty` | Actual execution is the pure measured pair `([],1)`; no invalid uniform index is constructed. |
| Singleton arbitrary payload | Actual returned list is that singleton; two empty filters and two empty recursive calls yield cost 5. No payload order or equality is needed for this case. |
| Three distinct ordered keys | Actual cost law has mass `1/3` at 21 and `2/3` at 25; real mean `71/3`. This uses the same selected pivot and recursive outcomes, not an unrelated scalar PMF. The values agree with the already saved calculation. |
| Repeated occurrence sampling | `[a,a,b]` chooses an `a` occurrence with total probability `2/3`; no deduplicated uniform sampler substitution. |
| All equal keys | Every selected pivot leaves one empty child and one child of size `n-1`; actual cost is deterministically `2*n*n+2*n+1`. This prevents claiming the two-way algorithm has an unqualified expected `O(n log n)` bound with duplicates. |
| Payload carrying additional data | Key order supplies sorting/rank hypotheses while no equality/measurability instance is imposed on the full payload; equal-key payload stability remains a separate property. |

The comparison-only observation `Q` can later be related on the **same execution** by `T = 4*Q + 4*n + 1`. The base and nonempty equations support this identity, but merely comparing two independently specified numerical distributions would be insufficient. A second instrumented observation is optional if the direct source mean proof is used; importing the entire AFP cost-distribution proof is not necessary.

Finally, charging pivot lookup, occurrence deletion, random-bit generation or append is a separately stated observation extension. Preserve both append occurrences and their association when making that extension. The exact harmonic formula above is for Exercise 2.4's stated tariff. Abstract PMF semantics and the support/mean proofs do not establish physical runtime, allocation or random-bit costs.

## Suggested placement and limits of this preflight

The source-specific random-pivot sorting operation and its measured contracts should remain an algorithm client of existing `Resources.Measured`, `CallCount` and `ListCalls`. A small ordinary positive-index sampler/event-count lemma may be shared under `Applications.Probability` when the selection client also needs it; it does not warrant a new carrier or executor. Initially keep the weighted-tsum bind convenience private unless two concrete clients need that exact missing statement. `Applications.Probability.Table` already gives finite rational tables and `lintegral_kernel`, but imposing a finite enumerable universe of all payload-valued recursive outputs merely to use it would be unnecessary here.

Candidate direct dependencies are `Mathlib.Probability.ProbabilityMassFunction.Constructions`, the inspected PMF/integral modules for analytic results, `Mathlib.Data.List.Perm.Basic`, and the existing measured-list modules. This is not a compiled minimal-import certificate. Prefer these concrete APIs over a root `Mathlib` import; source integration must respect the shared drafts' independent acceptance and the Chapter 1 prerequisite.

The concrete remaining proof risks are the termination goals beneath explicit bind lambdas, simplification of measured filter lets, local finite-sum normalization and universe elaboration, support induction, the strict-count rank bijection, and the actual mean correspondence. Each has a specific route above. No discovered mathematical obstruction requires changing the source tariff, assuming an inhabited payload, adding a probability framework, or weakening the retained randomized claim beyond its necessary distinct-key/domain qualifications. No compiler result or acceptance is claimed.
