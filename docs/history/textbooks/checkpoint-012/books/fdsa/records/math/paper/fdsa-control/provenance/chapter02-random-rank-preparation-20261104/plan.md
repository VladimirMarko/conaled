# Actual random-pivot ranks, child sizes, and size-only means

## 1. Scope, current evidence, and release boundary

This is a bounded source/API preparation plan. It writes no Lean source,
changes no Git reference, starts no build and writes no dependency or project
cache. Proposed names and proof arrangements remain subject to root's source
release and the normal candidate/review gates.

The checked initial recursive PMF and examples are the unchanged pair at
author `bb4fb243bb7b16ae8bef921fec479a86f2b01c90`, checked in central
`dfaf68114d1dda4e15628c94c3d988c3f5457c49`. The full focused attempt4 and the
62-name author source/elaborated-type readback are already preserved. These
are focused results, not a complete foundation or Chapter 2 acceptance.

The mean dependency was first submitted at
`7b1851cee7fe580a4fe235740b0c07e4ddd8fc58`. Its first central focused compile
at `fff993ec1d041c0a86e7e79a94d13f5be6b92a94` closed exit 1, with five owned
proof elaboration diagnostics. Those findings took priority over this plan.
The proof-only successor is now
**`19879f244a81b03b7ccaabbcf53fc0b355e9985b`**, clean and uncompiled by this
author. The closed failed result and exact repair are preserved under
`../chapter02-random-expectation-proof-repair-20261104/`. None of this plan
assumes that the mean dependency has passed its pending central check.

The next bounded implementation should add only:

1. `Applications/Resources/RandomQuickSortRank.lean`.
2. `Examples/RandomQuickSortRank.lean`.

The production dependency is the actual `RandomQuickSortMean` source, hence
the actual run, measured-list and deterministic-resource dependencies already
recorded there. It does not require XW01 or XU01–XU06. The historical shared
foundation dependency is still subject to root's acceptance gates; this
preparation supplies no acceptance evidence for it.

This slice proves the actual occurrence-to-rank and child-size correspondence,
then the actual mean's invariance under input order and distinct key values,
and finally its size-only recurrence. Harmonic algebra and Big-O are a
separate owned continuation. Uniform-input deterministic quicksort remains a
separate C02-024 obligation with its own probability correspondence.

## 2. Preserve the execution and the generality

For `xs : List α`, key function `key : α → κ`, and `[LinearOrder κ]`, write
`lt a b := decide (key a < key b)`. Payload and key universes remain
independent: `α : Type u`, `κ : Type v`. No finite, countable, measurable,
inhabited or decidable-equality assumption is added to `α`.

For the actual valid occurrence `i : Fin xs.length`, the exact child lists are

```lean
pivot := xs[i.val]'i.isLt
rest  := xs.eraseIdx i.val
left  := rest.filter (fun x => decide (key x < key pivot))
right := rest.filter (fun x => !(decide (key x < key pivot)))
```

The primary statements retain this Boolean complement on the right, matching
`exerciseMean_cons` exactly. A key-order presentation using
`decide (key pivot ≤ key x)` may be a proved corollary; it is not a different
partition. The input hypothesis is **`(xs.map key).Nodup`**. Payload `Nodup`
alone is insufficient because different payloads may carry equal keys.

The recursive PMF continues to sample a fresh uniform valid occurrence at
every nonempty recursive call. This plan never changes that PMF. The only
sorting permutation introduced below is a finite mathematical reindexing of
the actual current occurrences; it is not a pivot sampler, a shuffled input,
or a shared random priority assignment. Conditioned on a root occurrence,
the child inputs are the displayed fixed lists. They are not resampled
uniform input orders. Their later randomness is their own actual recursive
PMF already present in `run`.

## 3. A concrete occurrence-to-rank bijection

The preferred finite rank object uses the pinned tuple-sort API:

```lean
def occurrenceRank [LinearOrder κ] (key : α → κ) (xs : List α) :
    Equiv.Perm (Fin xs.length) :=
  (Tuple.sort (fun i : Fin xs.length => key xs[i.val]'i.isLt)).symm
```

`Tuple.sort f` is an actual permutation of `Fin n`; it sorts the graph
`(f i, i)` in lexicographic order. Thus its inverse maps an original
occurrence index to its sorted position. This definition exists at length
zero without selecting an element of `Fin 0`. If keys repeat, the graph's
index tie breaking still gives a permutation, but its positions do not equal
strict key counts. The correspondence theorem therefore needs mapped-key
distinctness explicitly.

Proposed primary order contract:

```lean
theorem occurrenceRank_lt_iff [LinearOrder κ] (key : α → κ)
    (xs : List α) (hd : (xs.map key).Nodup)
    (i j : Fin xs.length) :
    occurrenceRank key xs i < occurrenceRank key xs j ↔
      key xs[i.val]'i.isLt < key xs[j.val]'j.isLt
```

The exact proof route is finite and source-connected:

1. Let `f i := key xs[i.val]`. `List.ofFn_getElem_eq_map` identifies
   `List.ofFn f` with `xs.map key`. `List.nodup_ofFn` therefore gives
   `Function.Injective f` from the stated hypothesis, without a global
   injectivity requirement on `key`.
2. `Tuple.monotone_sort f` gives monotonicity of `f ∘ Tuple.sort f`.
   Compose the injectivity of `f` with the permutation's injectivity and use
   `Monotone.strictMono_of_injective`.
3. Apply `StrictMono.lt_iff_lt` to the inverse images of `i` and `j`.
   The two inverse laws give exactly the displayed comparison.

No axiom asserts a rank distribution or an order isomorphism. The finite
permutation comes from the inspected tuple graph construction, and its key
interpretation is proved from the real input's distinct keys.

## 4. Exact sizes and inherited distinctness of the executed children

Proposed contracts, with the above `pivot`, `rest`, `left` and `right`
expanded as `let` expressions in final Lean statements, are:

```lean
left.length = (occurrenceRank key xs i).val
right.length = xs.length - 1 - (occurrenceRank key xs i).val
(left.map key).Nodup ∧ (right.map key).Nodup
left.length < xs.length ∧ right.length < xs.length
```

The first two and the Nodup conjunction require `hd`; strict decrease itself
needs only a valid index and the actual length bounds. Empty input supplies
no index, so none of these statements fabricates an empty pivot.

### Count the actual left child

A small private helper can prove, for every Boolean predicate and arbitrary
payload list,

```lean
(xs.filter p).length =
  (Finset.univ.filter (fun i : Fin xs.length => p xs[i.val]'i.isLt)).card
```

Use `List.ofFn_get`/`List.ofFn_getElem`, `List.ofFn_eq_map`, and
`List.filter_map` to write the list as the map of all actual occurrence
indices. Length ignores the map. The filtered `List.finRange` has Nodup;
`List.toFinset_card_of_nodup`, `List.toFinset_filter` and
`List.toFinset_finRange` identify its length with the finite cardinality.
All finite equality requirements concern `Fin xs.length`, never payloads.

For the strict-below-pivot predicate, the rank permutation maps that finite
index filter bijectively onto `Finset.Iio (occurrenceRank key xs i)`, by the
proved order contract. Prove the image equality, use
`Finset.card_image_of_injective`, then `Fin.card_Iio`. The result is the
strict-filter length in the original input.

Now apply the existing
`List.getElem_cons_eraseIdx_perm i.isLt : pivot :: rest ~ xs` to that same
filter. The selected pivot fails its strict self-comparison. `List.Perm.filter`
and permutation length equality therefore identify the actual erased-list
left-child length with the original strict-filter length. This is sufficient
for the size claim and avoids assuming payload equality or substituting a
set deletion for the actual occurrence deletion.

### Derive the actual right size

`List.length_eraseIdx_add_one i.isLt` proves `rest.length + 1 = xs.length`.
The existing `Resources.QuickSort.partition_lengths` proves
`left.length + right.length = rest.length` for these complementary filters.
Together with the left-rank equality, natural arithmetic yields the right
size, including rank zero and the largest rank. A proof never replaces
natural subtraction by real subtraction before the relevant bounds hold.

### Preserve distinct keys in both actual children

Each filter is a sublist of `rest`, and `List.eraseIdx_sublist` makes `rest`
a sublist of `xs`. Map these sublist relations with `key` using
`List.Sublist.map`, then use `List.Nodup.sublist` on `hd`. This proves the
exact recursive mapped-key hypotheses without obtaining or assuming a
decidable-equality instance on payloads and without requiring the key
function to be globally injective.

`List.length_filter_le` and the erased-list length equation give both strict
recursive size bounds. The existing random core's analogous helper is
private, so a client must use these public list lemmas instead of referring
to that private name.

## 5. Actual uniform occurrence-to-rank transport

First prove a private finite-permutation law for the existing constructor:

```lean
(uniformIndex m).map σ = uniformIndex m
```

where `σ : Equiv.Perm (Fin (m + 1))`. The inspected `PMF.map_ofFintype`
expresses each output mass as the sum over its actual preimage. Every rank
has exactly one preimage, `σ.symm r`, so the sum is the same constant
`((m + 1 : Nat) : ENNReal)⁻¹`. Alternatively, `PMF.map_apply` with the same
unique preimage proves it directly. This proof requires no order or Nodup
hypothesis because it is just permutation invariance of the actual finite
uniform distribution.

Apply this to `occurrenceRank key (head :: tail)` and combine it with the
proved child-size law. A useful public consequence, with `hd`, is:

```lean
(uniformIndex tail.length).map (fun i => (actualLeft key (head :: tail) i).length)
  = (uniformIndex tail.length).map Fin.val
```

Here `actualLeft` is notation in this plan for the explicit erased/filter
expression, not a requested replacement execution. `PMF.map_comp` transports
the finite rank law to Nat. The finite-target premise of `map_ofFintype` is
used only for `Fin`, not incorrectly applied to the final Nat target or
arbitrary payload values. This law exhibits the uniform rank of the actual
chosen occurrence. It does not assert any uniform child-input order law.

## 6. Prove equal-length actual means before defining the size sequence

The recommended bridge is stronger than an input permutation lemma and
avoids introducing an unconnected recursive numerical sequence:

```lean
theorem exerciseMean_eq_of_length_eq
    {α : Type u₁} {κ : Type v₁} {β : Type u₂} {λ : Type v₂}
    [LinearOrder κ] [LinearOrder λ]
    (key₁ : α → κ) (key₂ : β → λ) (xs : List α) (ys : List β)
    (hx : (xs.map key₁).Nodup) (hy : (ys.map key₂).Nodup)
    (hlen : xs.length = ys.length) :
    exerciseMean (fun a b => decide (key₁ a < key₁ b)) xs =
      exerciseMean (fun a b => decide (key₂ a < key₂ b)) ys
```

The theorem keeps four independent universes. Strong induction on the common
length quantifies over both actual input lists. The zero case forces both
lists empty and uses the proved actual empty mean. In the successor case,
open `exerciseMean_cons` for both nonempty lists. The exact index bijection is

```lean
(occurrenceRank key₁ xs).trans (finCongr hlen)
  |>.trans (occurrenceRank key₂ ys).symm
```

with its fully parenthesized expression in source. This matches an actual
left input occurrence to the actual right input occurrence of the same rank.
`finCongr_apply_coe` preserves the rank value across the length equality.
The actual left children have equal lengths by Section 4; so do the actual
right children. Both pairs have inherited mapped-key Nodup and strictly
smaller lengths. The induction hypothesis therefore identifies their actual
recursive means. `Fintype.sum_equiv` reindexes the two actual root averages,
and the common length makes the denominator and source toll equal.

This is a proof about the two actual PMF means. It does not assume that they
already depend only on length. It uses neither the target recurrence nor a
closed harmonic formula as an induction hypothesis. It also makes no stronger
claim that the output values or full joint run distributions are identical
across different payload types.

## 7. Define and derive the genuine size-only recurrence

Use a canonical input only after the preceding actual-mean comparison:

```lean
def sizeMean (n : Nat) : ℝ :=
  exerciseMean (fun a b : Nat => decide (a < b)) (List.range n)

theorem exerciseMean_eq_sizeMean [LinearOrder κ] (key : α → κ)
    (xs : List α) (hd : (xs.map key).Nodup) :
    exerciseMean (fun a b => decide (key a < key b)) xs = sizeMean xs.length
```

The proof applies the two-input theorem to the canonical Nat list, using its
actual `List.nodup_range` and length. Thus `sizeMean` is definitionally an
actual execution mean. No finite/permutation average or cost-only recursion
is substituted for it.

For the exact recurrence, first rewrite both actual child means in
`exerciseMean_cons` using this theorem and inherited child distinctness.
The child-size identities then give

```text
n⁻¹ * Σ i : Fin n, (sizeMean (rank i).val
                     + sizeMean (n - 1 - (rank i).val)) + 4*m + 3
```

for `n = m + 1`, with all displayed arithmetic in its declared Nat/real type.
Reindex by `occurrenceRank` using `Equiv.sum_comp`. `Fin.revPerm` then shows
the second rank sum equals the first, because its Nat value is `n - 1 - k`.
The finite-sum body must be explicitly parenthesized; the first mean compile
showed that leaving an additive summand unparenthesized can lose binder scope
with the current notation. Real ring arithmetic gives the factor `2/n`.

The primary successor contract is:

```lean
sizeMean 0 = 1

sizeMean (m + 1) =
  (2 / ((m + 1 : Nat) : ℝ)) *
    (∑ r : Fin (m + 1), sizeMean r.val) + ((4 * m + 3 : Nat) : ℝ)
```

Prove this first for any actual distinct-key input of length `m + 1`, then
instantiate `List.range (m + 1)`. Decomposing the canonical nonempty list is
just list case analysis plus its length; the proof need not force its
append-shaped `range_succ` equation into a head recursion.

The agreed harmonic-owner interface is the positive-size range-sum wrapper:

```lean
theorem sizeMean_recurrence (n : Nat) (hn : 0 < n) :
    sizeMean n = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, sizeMean k)
      + 4 * (n : ℝ) - 1
```

Use the pinned `Fin.sum_univ_eq_sum_range`, express positive `n` as a
successor, and justify casts/toll arithmetic explicitly. The empty equation
stays separate, so no division-by-zero identity is used to certify the base.

## 8. Agreement with the harmonic owner

Root and the quicksort author were sent this actual `sizeMean` proposal. The
quicksort author confirmed that the successor recurrence and the above
range-sum wrapper match its planned numerical interface.

The separate tentative module `Applications/Resources/QuickSortMean.lean`,
namespace `Resources.QuickSortMean`, is probability independent. Its generic
solver may take a real sequence with proved base and recurrence and derive
the harmonic identity and logarithmic/Big-O estimates. The current rank slice
does not depend on that solver to prove the actual mean recurrence. A later
final actual-mean theorem may import both, or extend the rank module after
the numerical module passes; either arrangement avoids a cycle.

The agreed eventual target is
`sizeMean n = 8 * ((n : ℝ) + 1) * (harmonic n : ℝ) - 12 * (n : ℝ) + 1`.
The harmonic author also plans a genuine Big-O result with an explicit
large-size bound. These remain that author's work and are not proved by this
plan. The already implemented same-run literal-mean comparison may later
transport an actual exercise-mean bound to the append-inclusive observation,
after its own dependency has passed validation.

## 9. Independently checked consequential cases

These are expected contracts/calculations for the next example file, not
compiled examples or a substitute for the general proof.

| Case | Actual occurrence/rank and child facts | Mean consequence |
| --- | --- | --- |
| Empty input, including `List Empty` | No actual pivot and no `Fin 0` sample; the rank permutation is the empty permutation. | Actual mean 1; the recurrence uses a separate zero case. |
| Singleton | The one occurrence has rank 0; both actual children are empty; local toll 3. | `1 + 1 + 3 = 5`. |
| Two distinct keys in either order | The actual occurrence ranks are a permutation of 0 and 1; child sizes are `(0,1)` or `(1,0)`; local toll 7. | Both branches have `1 + 5 + 7 = 13`. |
| Keys `[2,0,1]` | Original-index ranks are `[2,0,1]`; actual left/right sizes are `(2,0)`, `(0,2)`, `(1,1)`. Each index has mass `1/3`. | Branch exercise costs are 25, 25 and 21, so the mean is `71/3`, matching the existing three-key law and mean contract. |
| Keys `[3,1,0,2]` | Actual child lengths by original index are `(3,0)`, `(1,2)`, `(0,3)`, `(2,1)`. The filtered children retain their actual order, e.g. pivot 2 leaves left `[1,0]` and right `[3]`. | The local toll is 15. Extreme-rank conditional means are `119/3`; internal-rank means are 33. Their uniform average is `109/3`. |
| Distinct payload tags with keys `[1,1,2]` | Payload Nodup can hold while mapped-key Nodup fails. The second equal-key occurrence has sorted tie position 1 but actual strict-left size 0. | The rank-size theorem's hypothesis is necessary; the existing actual sampler still gives the repeated key mass `2/3`. |
| All equal keys, length 3 | Every actual left child is empty regardless of sampled occurrence. | Existing actual means stay exercise 25 and literal 34; no distinct-key harmonic claim applies. |
| Generic payload/key universes | State clients with only the key's `LinearOrder` and mapped-key Nodup; include comparison to canonical Nat input via the four-universe theorem. | No hidden finite/measurable/equality/inhabited payload premise may enter the elaborated declarations. |

The two- and three-key means are already preserved actual laws/mean contracts;
the new cases exercise rank transport and actual child ordering. Numerics are
checked independently by the displayed branch arithmetic and do not become
premises of a general theorem. Source tests must include the duplicate-key
boundary even if the pure tuple permutation exists for those inputs.

## 10. Inspected APIs and minimum implementation discipline

The adjacent identity record fixes the Mathlib pin, exact source files, and
current project/source hashes. The relevant inspected APIs are:

| API source | Specific API used in the plan |
| --- | --- |
| `Data/Fin/Tuple/Sort.lean` | `Tuple.sort`, `Tuple.monotone_sort`, graph permutation construction. |
| `Data/List/OfFn.lean`, `Data/List/FinRange.lean` | `ofFn_get`, `ofFn_getElem_eq_map`, `ofFn_eq_map`, `nodup_ofFn`. |
| Lean `Init/Data/List/OfFn.lean`, `Lemmas.lean`, `Sublist.lean`, `Pairwise.lean`, `Erase.lean`, `Perm.lean` | `ofFn_getElem`, `filter_map`, `filter_sublist`, `Sublist.map`, `Nodup.sublist`, `eraseIdx_sublist`, `Perm.filter`. |
| `Data/List/Perm/Basic.lean` | `getElem_cons_eraseIdx_perm`. |
| `Data/Finset/Basic.lean`, `Data/Finset/Card.lean`, `Data/Fintype/Basic.lean` | `List.toFinset_filter`, `List.toFinset_card_of_nodup`, `Finset.card_image_of_injective`, `List.toFinset_finRange`. |
| `Order/Monotone/Defs.lean`, `Order/Monotone/Basic.lean` | `Monotone.strictMono_of_injective`, `StrictMono.lt_iff_lt`. |
| `Order/Interval/Finset/Fin.lean` | `Fin.card_Iio`. |
| `Data/Fin/SuccPred.lean`, `Data/Fin/Rev.lean` | `finCongr`, value-preserving cast laws, `Fin.revPerm`. |
| `Algebra/BigOperators/Group/Finset/Defs.lean`, `Data/Fintype/BigOperators.lean` | `Fintype.sum_equiv`, `Equiv.sum_comp`, `Fin.sum_univ_eq_sum_range`. |
| `Probability/ProbabilityMassFunction/Constructions.lean` | `map_ofFintype`, `map_apply`, `map_comp` for the actual constructor's rank pushforward. |
| Actual project `QuickSort.lean`, `RandomQuickSort.lean`, `RandomQuickSortMean.lean` | `partition_lengths`, `uniformIndex` and its exact mass, actual bind-mean equation and genuine integrability boundary. |

Inspect final imports for public availability and keep them limited to APIs
actually used. Do not import a private project proof name. Continue to use
ordinary `let` for proof-local instances if needed; the pinned
`linter.style.haveILetI` is enabled. Do not suppress a linter to accommodate
the notation or cast issues observed in the preceding compile.

Before any source acceptance, root must secure the focused terminal result,
complete explicit type inspection including universes and all hypotheses,
author source/type readback, and the applicable full immutable-candidate
check/audit, independent Standards/Spec reviews and immediate verification.
No dependency or mathematical gate is waived by this plan. The chosen metrics
still exclude pivot sampling, index lookup/removal and random-bit work.

This bounded plan is now ready for root's assessment. Implementation remains
unreleased. All source/ref/control writes are held after the two preparation
artifacts and the authorized proof-repair handoff are closed.
