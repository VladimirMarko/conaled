# Uniform-input first-pivot quicksort mean: bounded implementation plan

## Status and exact source boundary

Prepared 4 November 2026 under root's read-only preparation assignment. Only
this plan and `api-identities.json` are written. The natural-operations author
branch remains clean and held at `e1f3b5c43ba3b0f4aca5964f2b4568e06b47700c`.
Root has read that operational source and its complete author report with zero
source findings; its first compile is still pending. Actual operational
compiler diagnostics take priority over this preparation.

This plan supplies no implementation, compiled theorem, independent review,
new acceptance or permission to start another source slice. The accepted book
tip remains `07e480f6ec9958d4975bb90151005b84f2907614`; the exact first pending
foundation remains `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.

The complete preserved average proof plan, conditional-mean preflight,
probability dependency handoff and approved harmonic plan were read. The actual
321-line XU02 core, 485-line XU03 core, deterministic resource execution,
transport core/examples and relevant conditional boundary examples were read.
The selected exact sources are:

| Component | Exact source selection | Status used here |
| --- | --- | --- |
| XU02 whole-order law | `2695e20f76604cc85396fd8d8e82459b9067f551`, `PermutationOrder.lean` | Source inspected; this plan grants no acceptance. |
| XU03 conditional tail | `97ed9feee78f723cb6294aa5148da9ab5846db7a`, `PermutationTail.lean` | Root identifies this tail as uncompiled. |
| Actual deterministic cost | `0ec9954479b081664bd4504c90fb66fba5fd22c8`, `Applications/Resources/QuickSort.lean` | Existing actual execution and equations, not a new recurrence model. |
| Payload transport | `5a3af21cb4ff56896f1a7d249736c4804c229873`, both QuickSortTransport files | Uncompiled successor to `e71092c`; only explicit autoImplicit/warningAsError settings were added. |
| Harmonic algebra | Approved `provenance/chapter02-harmonic-preparation-20261104/plan.md` | Numerical implementation belongs to the quicksort owner; proposed names below do not claim new APIs exist. |

**Reconciliation detail:** the XU03 commit contains older Order bytes, not the
corrected XU02 selection. Its Order-to-2695e20 diff consists of the retained
notation, proof/API and local-instance corrections and omission of one unused
private equality instance. The inspected public mathematical contracts are
unchanged. A combined candidate must preserve the exact corrected Order source
and selected Tail source; checking out the entire historical Tail commit would
restore those old Order bytes. No such integration was performed here. The
transport successor's deterministic resource dependency matches 0ec exactly.

All source blobs, SHA-256 identities, the complete reconciliation diff, actual
pin identities and selected exact Mathlib API excerpts are recorded in
`api-identities.json`. Mathlib is pinned at
`56a005855ea17e0b0958f73ec801ae140b0a1679`; every recorded local Mathlib file was
compared byte-for-byte with that Git object. No compiler or cache was invoked.

## 1. Actual observation and minimal domains

Work first with labels `I : Type u`, an arbitrary Boolean comparator
`lt : I → I → Bool`, a complete nodup list `positions : List I`, and a fixed
`S : Finset I`. The existing `restrictedOrder positions S π` is denoted O_S(π).
The original measure is μ = `uniformOn Set.univ` on `Equiv.Perm I`.
Define only a source-specific mean of the existing cost:

```text
W_S(π) = (Resources.QuickSort.exerciseCost lt (O_S(π)) : Real)
M_lt(S) = integral W_S μ.
```

This is the first coordinate of the existing actual measured execution. It
counts the recursive entries and both full unit-predicate filter traversals;
its empty value is 1 and nonempty tail-length-m toll is 4*m+3. It is not the
classical one-comparison-per-tail statistic, append-inclusive cost, mapping
work, index-lookup work or physical runtime.

Use the existing `[DecidableEq I]` input needed by Finset/restrictedOrder, and
the sample-space measurable structure with measurable singletons. Completeness
supplies `Fintype.ofList positions hcomplete` locally in proofs. There is no
public label order, label default or nonempty-label requirement. The empty
label type still has its identity permutation and a nonempty sample space.
The list target measurable structure required for HasLaw can be chosen locally
as the discrete structure; it adds no payload measurable-space requirement.
Use ordinary proof-local `let` instances, not the rejected `letI` style.

Only the final rank/closed-form step needs ordered keys. There use a key map
`labelKey : I → κ`, where `κ : Type w` has `LinearOrder`, and the explicit
local hypothesis `Set.InjOn labelKey (S : Set I)`. Payloads later have a third
independent universe `α : Type v`. No `[DecidableEq α]`, payload order,
payload default or finiteness of all payloads is required. Key injectivity is
needed only on S, not on labels outside the selected problem.

## 2. Derive the actual conditional equation before rank assumptions

For fixed a∈S define the two fixed child subsets by Boolean outcomes:

```text
L_a = (S.erase a).filter (fun b => lt b a = true)
R_a = (S.erase a).filter (fun b => lt b a = false)
E_a = firstEvent (restrictedOrder positions S) a.
```

These definitions keep the strict/complement source split exact even before
an order law is imposed. Prove both children are subsets of `S.erase a`, their
disjoint union is `S.erase a`, and their cardinalities sum to S.card−1.
Consequently each is strictly smaller than S when a∈S. These facts do not
need distinct keys or any label order.

On E_a, `List.head?_eq_some_iff` exposes the actual equation O_S(π)=a::ys.
The tail is this same ys. Its members lie in `S.erase a` by
`tail_restrictedOrder_eq` and the existing membership theorem. Prove the two
pointwise Boolean predicate identities on those members, then use
`List.filter_congr` followed by `filter_tail_restrictedOrder_eq` to obtain:

```text
ys.filter (fun b => lt b a) = O_(L_a)(π)
ys.filter (fun b => !(lt b a)) = O_(R_a)(π).
```

These are on-event identities of the actual original sample. Do not replace
ys by an independently sampled order. Length comes from
`restrictedOrder_length` and the exposed cons equation, giving
`ys.length = S.card - 1`. Substitute into the existing proved
`exerciseCost_cons` to establish, on E_a:

```text
W_S(π) = W_(L_a)(π) + W_(R_a)(π) + (4*(S.card-1)+3 : Nat).
```

The final natural toll is cast to Real. This equation is derived from actual
source execution; it is not a hypothesis of the final mean theorem. In the
keyed specialization, the right predicate is key≥pivot. Distinctness after
erasing the pivot additionally makes it strict key>pivot; prove that fact only
when it is used, without changing the source complement filter.

## 3. Integrability and the same conditional child observations

With the local finite enumeration, `Equiv.Perm I` is finite. The pinned
`instIsProbabilityMeasure_uniformOn_univ` applies because that sample type is
nonempty. For every fixed child C and Boolean comparator, all actual real cost
observations on this sample space are integrable by
`MeasureTheory.Integrable.of_finite`. Its signature requires finite domain,
measurable singletons and a finite measure. It requires no finite list type.

For a∈S, XU03's public `uniformOn_firstEvent` gives
`μ E_a = (S.card : ENNReal)⁻¹`. Record positive cardinality and positive finite
event mass explicitly. Install `cond_isProbabilityMeasure` for μ[|E_a] before
using finite-measure integrability or integrating the constant toll. This
covers each actual child observation under the conditional measure as well.

For C⊆S.erase a, construct public `HasLaw` records for O_C using:

- `map_restrictedOrder_cond_first positions hnd hcomplete S a ha C hC`
  under μ[|E_a];
- `map_restrictedOrder_uniformOn positions hnd hcomplete C` under μ;
- `(measurable_of_finite _).aemeasurable` for the map field.

Do not refer to the private XU03 convenience constructor `restrictedOrder_hasLaw`.
The target real cost function on `List I` is AEStronglyMeasurable by the pinned
`AEStronglyMeasurable.of_discrete`: finite I makes `List I` countable, not finite.
`HasLaw.integral_comp` takes exactly this measurability hypothesis and equates
the composite integral with its common target-law integral. Apply it to both
records to derive the actual equality

```text
integral W_C (μ[|E_a]) = M_lt(C).
```

No independence of the two children is needed or asserted. The whole
conditional permutation environment does not regain the unconditional law.
The public `hasLaw_filter_tail_cond_first` is available if a proof retains the
actual filtered-tail functions directly; the mandatory subset premise is the
same. Use `ae_cond_of_forall_mem` to transport the on-event actual cost equation,
then `integral_congr_ae` and integral addition with the explicit integrability
proofs. The result is the actual conditional mean equation:

```text
integral W_S (μ[|E_a])
  = M_lt(L_a) + M_lt(R_a) + ((4*(S.card-1)+3 : Nat) : Real).
```

## 4. Recover the unconditional mean from the actual head partition

The empty subset is separate: O_∅ is pointwise [], hence M_lt(∅)=1 under μ.
Never condition on an empty head event to establish this base.

For n=S.card>0, prove the finite events E_a (a∈S) are measurable, pairwise
disjoint, and cover the entire permutation space. Measurability follows from
the finite sample domain. Coverage follows from the actual observed length n,
existence of a head without a default value, and membership of that head in S.
Disjointness follows from the two optional-head equalities.

The pinned `integral_biUnion_finset` takes measurable events, pairwise
disjointness and `IntegrableOn` proofs. Apply it to S and W_S, using restrictions
of the already proved finite-space integrability. It gives the sum of the
actual restricted integrals. For each event unfold the existing definition
`cond μ E_a = (μ E_a)⁻¹ • μ.restrict E_a` and use `integral_smul_measure`.
The known event mass makes the real scalar exactly n:

```text
integral W_S (μ[|E_a]) = (n : Real) * integral_(E_a) W_S μ.
```

Cancel only after proving `(n : Real) ≠ 0`. Equivalently the restricted
integral is `(1/n)` times the conditional integral. Thus prove, for every
Boolean comparator and nonempty S, the actual integral recurrence

```text
M_lt(S) = (1/(n : Real)) *
  sum (a in S) [M_lt(L_a) + M_lt(R_a) + ((4*(n-1)+3 : Nat) : Real)].
```

Finite-sum addition and cardinality simplify the repeated toll. The conversion
of that natural toll to `4*(n : Real)-1` uses n>0 and an explicit cast/subtraction
identity. No null-event cancellation, infinite normalization or averaging
equation at zero is introduced.

## 5. Rank the key image, retaining arbitrary labels

The older preflight applied `Finset.orderIsoOfFin` directly to S. That would
unnecessarily require a global order on I. Instead let K=`S.image labelKey`.
The explicit `InjOn` hypothesis gives K.card=S.card via the pinned
`Finset.card_image_of_injOn`.

The map from the membership subtype S to the membership subtype K is bijective:
injectivity is the supplied key distinctness; surjectivity is membership in the
image. Use `Equiv.ofBijective` to obtain e_key:S≃K. The existing
`K.orderIsoOfFin hcard` takes an arbitrary cardinality equality, so it already
has domain `Fin S.card`; no new cast/order framework is necessary. Compose its
underlying equivalence with e_key.symm to obtain

```text
e : Fin S.card ≃ S.
```

This is key-rank enumeration. It is independent of the order of `positions`,
which only enumerates the uniform sample's priority labels.

For pivot `a=(e k).val`, prove that `labelKey '' L_a` is the image of
`Finset.Iio k` under `K.orderEmbOfFin hcard`. Membership is proved in both
directions using the order isomorphism, its inverse and the erased-pivot
predicate. `Finset.card_map`, `Fin.card_Iio` and injectivity on the child give
`L_a.card=k.val`. The already proved complementary child-cardinality sum gives
`R_a.card=n-1-k.val`, including either empty child. This route needs only one
ordered-image equality; a second upper-interval construction is unnecessary.

Key distinctness is inherited by both children by restriction of the explicit
InjOn hypothesis along their subset inclusions into S. For actual observed
lists, combine `restrictedOrder_nodup`, exact support and that restricted
injectivity to obtain nodup mapped keys. Do not confuse distinct label values
or distinct payload records with distinct keys.

Reindex sums using the inspected generated `Finset.sum_coe_sort` and
`Fintype.sum_equiv`. Then use `Fin.sum_univ_eq_sum_range` and
`Finset.sum_range_reflect`; their additive names are generated by the exact
inspected product declarations at this pin. This gives two copies of the
same prefix sum after the child means have been identified.

## 6. Fixed-environment induction and numerical-owner interface

Let C(n) denote the numerical owner's real expression
`8*((n:Real)+1)*(harmonic n : Real)-12*(n:Real)+1`. The required imported
numerical facts are C(0)=1 and its **proved** positive-size recurrence

```text
C(n) = (2/(n:Real)) * sum (k in range n) C(k) + 4*(n:Real)-1,  n>0.
```

These are the exact agreed roles in the approved harmonic plan, not invented
already-compiled theorem names. The numerical owner also supplies nonnegativity,
explicit positive-size logarithmic bounds and ordinary Nat-indexed Big-O.

Strong-induct on S.card, retaining the same positions, label-key map and μ.
For each S, the statement quantifies the explicit key injectivity only on S.
Both child cards are strictly smaller, and their injectivity is inherited.
Substitute the induction hypotheses into the **proved actual** head-sum
equation, perform the rank reindexing above, and finish with C's recurrence.
The conclusion is the actual mean `M_lt(S)=C(S.card)` for the strict key
comparator. A fixed finite environment need not contain subsets of every
natural size. No actual global sequence A(n) is fabricated for unavailable
sizes, and the numerical recurrence is never assumed for M_lt.

The resulting scalar upper bound is `0≤M_lt(S)≤32*n*Real.logb 2 n` for n≥2.
Zero and singleton retain exact means 1 and 5; they cannot satisfy this scalar
n*log n bound. If the literal append-inclusive observation is exported, use
the same μ and its separately integrable actual literal cost, then integrate
the proved pointwise inequalities T≤literal≤2*T. This gives a bound with
constant 64, not an exact harmonic identity for the append-inclusive mean.

## 7. Arbitrary input payloads and a nonvacuous asymptotic family

For `xs : List α`, use occurrence labels `Fin xs.length`, lookup `i ↦ xs[i]`,
and the standard complete nodup occurrence enumeration. Each sampled input
is the actual restricted-order label list mapped through this lookup. Its
full occurrences form a permutation of xs, from the XU02 permutation theorem
and the existing enumeration/map identity. The distribution is precisely the
uniform ordering of occurrences; no probability structure on all payloads is
introduced.

The explicit input hypothesis is `(xs.map key).Nodup`. The inspected
`List.nodup_iff_injective_getElem` / `Nodup.injective_get` and `List.getElem_map`
turn it into injectivity of `i ↦ key xs[i]`. This requires no equality instance
on α. The occurrence-label, payload and key universe parameters remain
independent in the general transport interface.

Apply the exact `Resources.QuickSort.exerciseCost_map` from transport successor
5a3af21 pointwise, with the comparator pulled back along this same lookup.
Then integrate the equality to connect the actual mapped-payload execution to
the proved label mean. `run_map` preserves the full value and both cost
coordinates; the map need not be injective for that theorem. Lookup/map
evaluation is not charged by this observation. Distinct keys enter the
probabilistic rank theorem, not the transport theorem.

For the book's asymptotic statement, define the actual occurrence-based input
mean and consider any `family : Nat → List α` with length n and nodup mapped
keys at every n. The just-proved actual equality identifies its mean with C(n),
so the numerical Big-O yields

```text
IsBigO atTop (fun n : Nat => inputMean key (family n))
  (fun n : Nat => (n : Real) * Real.logb 2 n).
```

This changes the finite occurrence environment with each input length. An
eventual claim about subsets of one fixed finite I alone would not express
the intended unbounded-size sorting result. The canonical range family is a
connected specialization, not a substitute for arbitrary distinct-key inputs.

## 8. Consequential connected cases

| Case | Independently expected result and role |
| --- | --- |
| Empty selected subset; also I=Empty | Actual integral mean 1; no default pivot or positive-cardinality conditioning. |
| Singleton with arbitrary payload | Mean 5; two empty children and source toll 3. |
| Two distinct keys in either order | Actual cost 13, hence mean 13, with both zero-size child orientations covered. |
| Three distinct keys | Middle-rank first event has mass 1/3 and actual cost 21; extreme events have total mass 2/3 and cost 25; actual integral 71/3. |
| Labels with no order/default instance | A small named label type, arbitrary unsorted positions, keys such as 10,−5,7, and arbitrary payload components still give 71/3. |
| Key collision outside the selected subset | Selected three distinct keys retain 71/3; an outside label may share a selected key, detecting accidental global injectivity. |
| Empty left or right child | The conditional child order is [] and its actual mean 1, not 0. |
| Tagged equal-key input | Distinct payload records do not satisfy distinct keys. The source's all-right chain has mean 2*n²+2*n+1; size 3 gives 25, not 71/3. |
| Existing conditional boundary | Retain `environment_changed` and `PermutationTailBoundary.outside_order_12_mass`, `outside_order_21_mass`, `outside_order_not_uniform`: excluding the exposed key alone does not imply containment in the selected remainder. |
| Payload transport boundary | Retain arbitrary occurrence lookup, duplicate map and comparator-sensitive append-cost examples from 5a3af21; costs are transported only for the pulled-back comparator. |
| Scalar versus eventual logarithmic bound | Exact means cover n=0/1; scalar n*log₂n bound starts at 2; exported Big-O has explicit Nat indexing and actual means. |

The size-three mean should have both connections: the actual head-conditioned
calculation and the universal closed-form specialization. Do not prove it only
by reducing C(3). The saved factorial calculations need not be rerun; they are
independent development evidence, not a proof of the actual integral.

## 9. Minimal next source slice and gates

Subject to a future explicit implementation release, a source-specific resource
module and companion example module can contain, in this order:

1. Actual restricted-order cost mean, child subsets, support/cardinality facts,
   finite integrability and the empty-mean law.
2. On-event source filter/recurrence identification, public conditional HasLaw
   transport and conditional child integral equality.
3. Measurable head partition and the unconditional actual integral recurrence,
   still valid for arbitrary Boolean comparators.
4. Key-image rank equivalence, inherited distinctness, rank child-cardinality
   laws and finite-subset closed-mean induction using the numerical dependency.
5. Actual occurrence lookup mean, arbitrary-payload theorem, explicit logarithmic
   and genuine family Big-O corollaries, with the connected cases above.

The core mathematical imports needed are XU02/XU03, actual deterministic
QuickSort, the explicit transport successor and the numerical owner's mean
module. XU01 remains part of the recorded historical acceptance chain even
though XU02 does not import it. No XU04–06, joint law, branch independence,
new probability backend or random-pivot distribution identity is needed.
The separate randomized-pivot execution remains a separate source obligation.

Before any future implementation, root must align exact source dependencies
and release that slice; this plan authorizes neither edits nor builds. Then
preserve immutable candidates and every actual terminal log, inspect complete
elaborated universes/domains and connected statements, continue both independent
review axes, and satisfy all applicable complete candidate/audit/immediate
verification gates. Source inspection does not establish any of these results.

**Hold:** the operational source and all Git refs remain unchanged. Only the
two specifically authorized preparation files were written; all further writes
are held pending root's diagnostics or an explicit continuation.
