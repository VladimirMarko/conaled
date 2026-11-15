# Literal floor-left mergesort: value, stability and termination readiness

Prepared 2026-11-02. **Read-only preparation, not implementation, chapter activation, a compiler result or either final review.** Chapter 1 remains unaccepted and gate 80227 is unchanged. All shared drafts remain subject to their own acceptance and the recorded integration prerequisite.

This report supplements, and does not edit or supersede, the fully read `mergesort-proof-plan.md`, `chapter02-reuse-plan.md` and `../reviews/chapter02-requirements.md`. The frozen requirements intentionally retain their original **107-row snapshot**. The current reconciled Chapter 2 inventory contains **112 obligations**, including C02-108–112; `scope-reconciliation.md` records the clarification without changing the source comparison metric. The relevant focus here is C02-025–032, C02-035–036, the ordinary/keyed interfaces in C02-089–092, and the selected stable-sort realization for C02-107. The separately assigned `mergesort-cost-readiness.md` owns comparison-count readiness.

## 1. Recommendation

The existing plan is implementable with a small genuine algorithm addition and extensive exact reuse. Keep one ordinary floor-left recurrence over `List.merge`; prove its own decreasing lengths, permutation, keyed sortedness and filtered stability. Reuse the existing `KeySorted`, `Stable` and `StableSort` contracts, then obtain agreement with the library sorter from the existing uniqueness theorem. Do not create a second merge, list-prefix abstraction, sorting specification or resource framework.

The missing converse merge observation is also small: each input is a sublist of `List.merge` for **every** Boolean comparator, so arbitrary pairwise order of the output restricts to each input. The inspected pinned sorting files contain membership and permutation lemmas, but no matching exported each-input-sublist lemma. The old C02-031 gap therefore remains real; it does not require another sorting proof.

Two assumption refinements should guide implementation:

- Input-local comparator compatibility suffices for **sortedness**, but not equal-key **stability**. The actual key comparator and its left-tie branch must remain visible in the stability proof.
- `DecidableEq` on keys is needed to state the existing executable filter-based `Stable` contract. A plain output-equality theorem can introduce that instance locally in its proof; it need not add a public equality-decision assumption when neither algorithm uses it. No result here needs equality, order or an inhabitant on the payload type.

## 2. Evidence and exact source identity

The following local primary sources were inspected. No dependency or source was fetched or changed.

| Evidence | Exact relevant content |
| --- | --- |
| `book-source/Sorting.thy`, Isabelle mirror `f86f290225eebcc52c1ae7dba2e098f405f51c21` | `merge`, `msort`, `mset_merge`, `mset_msort`, `set_merge`, `sorted_merge`, `sorted_msort`; source guard and floor-left split at lines 79–89, value proofs at 94–143. The following comparison functions were read only to keep the value boundary correct. |
| `book-source/LeanListSort-Basic.lean`, pinned Lean `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | Entire file: `List.merge`, `MergeSort.Internal.splitInTwo`, `List.mergeSort`. The actual standard split has left size `(n+1)/2`. |
| `book-source/LeanListSort-Lemmas.lean`, same Lean pin | Entire file: merge equations, `pairwise_merge`, `merge_perm_append`, `merge_of_le`, `mergeSort_append`, permutation/sortedness/stability proofs, `map_merge`, `map_mergeSort`. |
| `book-source/LeanList-{Basic,Lemmas,TakeDrop,Pairwise}.lean`, same recorded Lean pin | Relevant ordinary list constructors, `Sublist.cons`/`cons_cons`, reconstruction, pairwise restriction and map laws. |
| `conaled-insertion-costs/Applications/Sorting/{Stable,Merge,SourceMerge,Sort}.lean` | Entire four modules. These are the existing reusable value contracts, not new acceptance evidence. |
| `conaled-insertion-costs/Applications/Resources/ListCalls.lean` and `Examples/ListLibrary.lean` | Entire files, including exact `takeRun`/`dropRun` and `split_reassembles`. Relevant `Resources/SymmetricCosts.lean` length/split definitions and proofs were also read. |
| `conaled-insertion-costs/.lake/packages/mathlib/Mathlib/Data/List/Sort.lean`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` | Exact relation-class wrappers `List.Perm.eq_of_pairwise'`, `List.Pairwise.merge`, `pairwise_mergeSort'`, and their assumptions. |
| Mathlib `Data/Multiset/{Defs,AddSub}.lean` at the same pin | `Multiset.coe_eq_coe` and `Multiset.coe_add`; no decidable payload equality is needed for these bridges. |
| Existing `Examples/StableSorting.lean`, `Examples/InsertionCosts.lean`, `Applications/Selection/Rank.lean` | Actual stable payload examples, generic payload contract and `pairwise_ranked` client shape. |

The previous reuse plan preserves SHA-256 provenance for the Lean reading copies and the pinned book/source theory. This report did not run a hash helper or inspect/change Git. Exact current candidate identities and eventual validation belong to the coordinator's immutable records.

## 3. Why the library recurrence is not the source recurrence

The source computes `n := xs.length`, returns `xs` when `n ≤ 1`, and otherwise merges recursive results on `xs.take (n/2)` and `xs.drop (n/2)`. The comparison selects the left head on a tie.

The pinned standard declarations instead say:

```lean
List.MergeSort.Internal.splitInTwo
  (l : {l : List α // l.length = n}) :
  {l : List α // l.length = (n+1)/2} ×
  {l : List α // l.length = n/2}

List.mergeSort_append (l₁ l₂ : List α)
  (h₁ : l₂.length ≤ l₁.length)
  (h₂ : l₁.length ≤ l₂.length + 1) :
  (l₁ ++ l₂).mergeSort cmp =
    List.merge (l₁.mergeSort cmp) (l₂.mergeSort cmp) cmp
```

The latter is a value identity for the standard orientation. At odd length at least three, the source's left block is smaller, so `h₁` is false. Swapping the blocks is not a repair: it changes the original contiguous order and can change the order of tied records. No theorem about identical final sorted values changes the split actually executed.

The retained length-three witnesses remain consequential: ordinary natural-order input `[0,1,2]` gives source/library comparison counts 2/3, while `[2,1,0]` gives 3/2. Both value outputs agree. The cost-side report handles their eventual measured proof. Likewise the standard runtime replacements in `Sort/Impl.lean` are value replacements, not evidence of the source's external comparison count.

For a completely arbitrary comparator, do not assert even unconditional output equality of different merge-sort trees. A reflexive cyclic comparator with `0 ≼ 1`, `1 ≼ 2`, `2 ≼ 0`, but not `0 ≼ 2`, gives source floor-left output `[0,1,2]` and ceil-left output `[2,0,1]` on `[0,1,2]`: the floor tree first merges 1 with 2, while the ceil tree first merges 0 with 1. This is a hand-derived boundary target, not a newly checked Lean example. The lawful key-order hypotheses in the proposed equality theorem are substantive.

## 4. Exact reusable API surface

All project names in this table are in `Applications.Sorting` unless qualified otherwise. These are existing declarations; proposed source-sort names in later sections are only design placeholders.

| Declaration and argument order | What it supplies |
| --- | --- |
| `List.nil_merge ys`, `List.merge_right xs` | Exact empty-side equations. The pinned right-empty theorem is named `merge_right`. |
| `List.cons_merge_cons cmp x y xs ys` | `merge (x::xs) (y::ys) cmp = if cmp x y then x::merge xs (y::ys) cmp else y::merge (x::xs) ys cmp`. |
| `List.merge_perm_append cmp` | `(List.merge xs ys cmp).Perm (xs ++ ys)`, no comparator laws. |
| `List.length_merge cmp xs ys` | Exact sum of input lengths, no comparator laws. |
| `List.mem_merge` | Membership iff membership in either input; preserves the distinction between set support and occurrence multiplicity. |
| `sourceMerge_eq_merge xs ys` | Existing literal source merge equals standard merge under `[LE α] [DecidableLE α]`. |
| `mergeBy_source key xs ys` | The existing source adapter under the locally pulled-back key order. Payloads acquire no public order instance. |
| `merge_sorted_compatible_on key cmp xs ys hc hx hy` | Sorted output under a key preorder and compatibility only on actual left/right input members. |
| `mergeBy_sorted key xs ys hx hy` | Sorted keyed merge under `[LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]`. |
| `mergeBy_filter key xs ys hx hy k` | Exact equal-key filter of the merge equals concatenation of the two input filters; needs a key preorder, key equality decision, and sorted blocks, but not antisymmetry or totality. |
| `mergeBy_spec key xs ys hx hy` | Existing stable-sort contract for concatenated sorted blocks, under key linear preorder and equality decision. |
| `StableSort.unique hy hz` | Equality of two outputs satisfying the same stable-sort contract; needs only key partial order and key equality decision once those contracts are supplied. |
| `sortOn_spec key xs` | Stable specification of the standard sorter; the final equality target, not proof that a different recursion was executed. |
| `StableSort.map h f hf` | Transports a contract through a key-preserving payload map, with no injectivity or equality decision on payloads. |
| `List.Pairwise.sublist hs h`, equivalently the usual `h.sublist hs` use | Any relation on a list restricts to a sublist; neither transitivity nor an order instance is needed. |
| `List.Pairwise.take h`, `List.Pairwise.drop h` | Pairwise order inherited by contiguous pieces. |
| `List.Pairwise.rel_of_mem_take_of_mem_drop h hx hy` | An ordered original list orders every member of its taken prefix before every member of its dropped suffix. |
| `List.merge_of_le hcross` | Merge equals concatenation when every cross comparison is true; no global comparator laws. |
| `List.pairwise_map` | `(xs.map key).Pairwise R ↔ xs.Pairwise (fun a b => R (key a) (key b))`. This is the exact mapped-key versus pulled-back-key bridge. |
| `Multiset.coe_eq_coe` | `(xs : Multiset α) = ys ↔ xs.Perm ys`. |
| `Multiset.coe_add xs ys` | `((xs : Multiset α) + ys) = ((xs ++ ys : List α) : Multiset α)`. |

The pinned standard generic sortedness alternative is also available:

```lean
List.pairwise_merge
  (trans : ∀ a b c, cmp a b → cmp b c → cmp a c)
  (total : ∀ a b, cmp a b || cmp b a)
  xs ys hx hy
```

Mathlib's `List.Pairwise.merge` packages the same idea using a decidable relation, `[Std.Total r]` and `[IsTrans α r]`. These facts can support an ordinary relation-level statement. For the existing conaled keyed/domain-local contract, `merge_sorted_compatible_on` is already the precise interface; adding a new relation/typeclass layer would not improve this source realization.

## 5. Concrete proof construction

### 5.1 The missing merge converse

Prove, by the actual merge branches, the two ordinary sublist observations:

```text
xs <+ List.merge xs ys cmp
ys <+ List.merge xs ys cmp
```

The branch taking a left head uses `List.Sublist.cons_cons` for the left observation and `List.Sublist.cons` for the right; the branch taking a right head reverses those roles. Base cases use reflexivity and the empty sublist. A sum-of-length recursion or nested structural induction follows the existing merge proofs. No comparator law, order relation, payload equality decision or inhabitant occurs in either statement.

Then `Pairwise R (merge xs ys cmp)` implies `Pairwise R xs ∧ Pairwise R ys` by `Pairwise.sublist`. Combine that generic implication with `mergeBy_sorted` for the source's keyed sortedness iff, and specialize to the identity key for C02-031. The implication from sorted output to sorted inputs is stronger in domain than its linear-order source specialization; there is no reason to impose linearity on that direction.

Place the observation in the existing `Sorting/Merge.lean` rather than a new merge carrier/module. Whether both sublist facts are public or proof helpers should depend on actual consumers; the semantic missing iff must be available. The pinned searches found `mem_merge`, `merge_perm_append`, `sublist_mergeSort` and `pair_sublist_mergeSort`, but the last two concern **sorting**, not either input of one merge. They do not fill this gap.

### 5.2 One actual floor-left value operation

The old proposed location `Applications/Sorting/TopDown.lean` remains sensible. A raw proposed operation `sortFloorBy (cmp : α → α → Bool) : List α → List α` may use explicit empty/singleton/two-or-more equations and `List.merge` in the recursive case. This is equivalent to the source's `length ≤ 1` guard, and the public source equation should make the equivalence explicit.

For `n ≥ 2`, define only locally `a := n/2` and `q := n-a`. Termination needs:

```text
(take a xs).length = a < n
(drop a xs).length = q < n
```

`List.length_take` gives `min a n`, `List.length_drop` gives `n-a`, and `Nat.div_le_self n 2` or constant-divisor arithmetic removes the minimum. The needed positivity and strictness are `1 ≤ a`, `a < n`, `1 ≤ q`, `q < n`. The stronger balanced relations `a ≤ q ≤ a+1` and `q=(n+1)/2` can be retained where the measured proof consumes them; do not build a new split API merely to rename these arithmetic facts.

The exact existing `sortBy_sorted_compatible_on` proof already demonstrates the local proof pattern:

```text
termination_by xs.length
simp only [List.length_take, List.length_drop, List.length_cons]
omega
```

For the proposed floor split, the nontrivial case has `xs = x::y::tail`, so the lower bound two is explicit. If the definition instead follows the literal `if n≤1` syntax, keep the negative guard hypothesis in the termination context. No returned-output length is used to justify recursive input termination, so there is no circularity.

Prefer safe base equations and a targeted non-base/source equation over globally simplifying an unrestricted recursive theorem. The pinned Isabelle itself removes `msort.simps` from its global simplifier. The normal well-founded definition and its equation theorem are sufficient; there is no need for a custom recursion/eliminator framework.

### 5.3 Permutation, support and length

Prove the raw comparator-polymorphic permutation by the same length recursion:

```text
merge(sorted take, sorted drop)
  ~ sorted take ++ sorted drop
  ~ take ++ drop
  = xs.
```

The steps are exactly `List.merge_perm_append cmp`, `List.Perm.append` on the two induction hypotheses, and `List.take_append_drop a xs` through `List.Perm.of_eq`. No order law is needed.

Derive the source multiset, membership and length statements from this one result using `Multiset.coe_eq_coe`, `Perm.mem_iff` and `Perm.length_eq`. For merge's multiset sum use `Multiset.coe_add`; for its set union use extensional membership plus `List.mem_merge`. Do not switch to `Finset` and accidentally demand decidable payload equality, and do not mistake set preservation for the required occurrence permutation.

### 5.4 Sortedness with the existing local compatibility contract

For raw `cmp`, the most immediately reusable keyed statement has the same premises as `sortBy_sorted_compatible_on`:

```text
[LE κ] [Std.IsPreorder κ]
∀ a∈xs, ∀ b∈xs,
  (cmp a b=true → key a≤key b) ∧
  (cmp a b=false → key b≤key a).
```

Restrict the premise to each child using `List.mem_of_mem_take` and `List.mem_of_mem_drop`. Apply `merge_sorted_compatible_on` to the actual recursively sorted children. To discharge its cross-member premise, first use each child's proved permutation to recover membership in the unsorted child, then the ordinary take/drop membership implication. This is precisely the already inspected standard-sort proof with its split replaced; the merge correctness proof itself is reused unchanged.

For the actual source/keyed comparator `decide (key a ≤ key b)`, a linear preorder supplies the compatibility law: the true branch is sound by `of_decide_eq_true`, and totality turns a false forward comparison into the reverse weak inequality. Antisymmetry is not used for this sortedness proof. Mapped-key sortedness from C02-092 is then just `List.pairwise_map`, not a new definition.

### 5.5 Stable ties and agreement with existing sorters

Use the source comparator, not arbitrary `cmp`, for the existing key-filter stability contract. On the nontrivial case, both recursive outputs are key-sorted. Apply:

```text
mergeBy_filter key (sourceSort take) (sourceSort drop)
  childSortedLeft childSortedRight k.
```

Rewrite each child filter with its stability induction hypothesis. The resulting concatenation of the input filters equals the filter of `take ++ drop` by `List.filter_append`, and reconstruction gives the original input filter. This retains original records and their order; it does not just compare key multisets. The contiguity of the split and the left-tie merge are the exact structural reasons the proof works.

Combine this result, permutation and sortedness into the **existing** `StableSort key xs (sourceSort xs)`. This supplies the concrete non-insertion selection for C02-107 without promising stability for every exercise variant. Then use:

```text
sourceSpec.unique (sortOn_spec key xs)
```

under key partial order in addition to the already established source/library specifications. The standard easy specialization is key `Std.IsLinearOrder`. `StableSort.unique` needs a key equality decision because its specification uses filters. In a theorem whose conclusion is only `sourceSort xs = sortOn key xs`, `classical` may install this equality decision locally, since neither value operation uses it. For a theorem that exposes `Stable`/`StableSort` itself, keep the required key equality instance explicit. There is no payload equality premise in either route.

Once the source contract exists, reuse `StableSort.map` for key-preserving payload transformations and `StableSort.unique` against the existing insertion specification when that comparison is wanted. Do not copy the standard `sublist_mergeSort`, `mergeSort_zipIdx` or stable uniqueness proofs. They concern a different implementation or are already the library theorem being consumed.

For ordinary element-order output uniqueness, C02-089 already has `List.Perm.eq_of_pairwise'`: given the two pairwise premises and their permutation, it needs only antisymmetry of the relation, not a new global totality or equality-decision assumption. The key-record case is different: equality of keys does not identify records, so its stable observation remains essential.

## 6. Hypothesis boundaries worth preserving

| Claim | Sufficient hypotheses at the existing interfaces | What must not be inferred |
| --- | --- | --- |
| Raw operation, termination, permutation, length, support | Arbitrary `cmp : α → α → Bool`; `α : Type u` | No sorting/stability claim follows merely from execution. |
| Source/keyed operation | `[LE κ] [DecidableLE κ]`, `key : α → κ` with independent universes | No global order or equality decision on records. |
| Keyed sortedness with arbitrary comparator | Key preorder plus input-local compatibility | Compatibility does not enforce left ties. |
| Filter stability of one keyed merge | Key preorder, key equality decision, both blocks sorted, exact key comparator | No totality or antisymmetry is needed for that helper; sortedness premises are real. |
| Source keyed stable-sort contract | Key linear preorder and key equality decision | Antisymmetry can wait until a uniqueness/equality theorem. |
| Equality of already specified stable outputs | Key partial order and key equality decision within the proof | This is the minimum of the reused uniqueness interface, not a claim that no alternative equivalence-class stability proof could weaken it. |
| Ordinary sorted-permutation uniqueness | Antisymmetry, plus the actual pairwise and permutation premises | Totality is not the same property as antisymmetry. |

A concrete failure of conflating the first two semantic laws: let every record's key be zero and let `cmp` always return false. The existing local sortedness compatibility premise holds, since both key inequalities are true. Sorting two distinct records reverses them, so their equal-key filter is not stable. The retained `Examples.StableSorting.sorted_permutation_not_stable` already demonstrates the broader sortedness/permutation-versus-stability distinction. No stronger comparator assumption should be silently introduced into the raw permutation theorem to avoid stating this boundary.

The helper `mergeBy_filter` also must not be applied to arbitrary unsorted blocks. For example, merging key list `[2,1]` with a right record of key 1 can output that right key-1 record before the later left key-1 record. The existing theorem's sorted-left premise rules out precisely this obstruction.

## 7. Shared list-prefix work: reuse without a dependency reversal

The saved shared work provides ordinary `List.take`/`drop` observations, not a separate list-prefix carrier. Relevant exact declarations are:

```lean
Resources.SymmetricCosts.splitRun_value (k : Nat) (xs : List α) :
  (splitRun k xs).1 = (xs.take k, xs.drop k)

Resources.SymmetricCosts.splitRun_work (k : Nat) (xs : List α) :
  (splitRun k xs).2 = min k xs.length + 1

Resources.ListCalls.takeRun_exact k xs :
  takeRun k xs = (xs.take k, min k xs.length + 1)

Resources.ListCalls.dropRun_exact k xs :
  dropRun k xs = (xs.drop k, min k xs.length + 1)
```

`ListCalls.take_drop_separate` actually calls both operations on the **original** `xs`; its result equals the fused split's pair and its declared count is twice the fused split count. This is a useful exact boundary if a later full traversal-count client is separately required. It does not identify one shared traversal with two traversals.

The pure floor-left sorter needs only ordinary `List.take`, `List.drop`, their lengths and `List.take_append_drop`. It should not import `Resources.ListCalls`, `Potential` or `SymmetricCosts` just to obtain those standard equations. `Examples.ListLibrary.split_reassembles n xs` is already a checked-client source use of `List.take_append_drop`, not a new abstraction to wrap again.

The source comparison-only execution must likewise not bind these positive-count list operations into its comparison observation: doing so would change C02-033/034. Their erased values may justify separately modelled execution correspondence, but the theorem is not a machine-runtime theorem. C02-108–112 retain their separately named natural-run operational obligations; they do not alter this top-down comparison tariff.

## 8. Remaining implementation work and connected clients

The smallest justified sequence, after the recorded acceptance prerequisite, is:

1. Add the genuinely missing merge sublist/converse observation in the existing merge domain, preserving its comparator-polymorphic direction.
2. Add the ordinary floor-left value recurrence with explicit source equation and length termination. Retain arbitrary payload universe and no extra payload assumptions.
3. Prove raw permutation once and derive source multiset/set/length observations. Establish key-sortedness by the existing local merge law.
4. Prove exact key-filter stability with `mergeBy_filter`; package the existing stable contract and derive the standard-sort value equality. Use `pairwise_map` for the source's mapped-key wording.
5. Compose the resulting contract with existing clients; do not introduce a second stable-sort or rank specification.
6. Let the separate measured companion prove erasure to this exact value recurrence and its own actual comparisons. Its termination can reuse the same input-size facts; output length follows from the already independent value permutation.

Consequential value/client cases already required or naturally sharing those proofs are:

- Empty and singleton inputs, including an `Empty` payload type for the empty case; no fabricated default element.
- The existing signed-key record fixture with equal keys crossing the **source** split, whose full-record expected list and filters are independently specified in `Examples.StableSorting`.
- A generic contract for `List (Nat × payload)` with no assumptions on `payload`, mirroring the existing insertion client; it exercises actual universe and capability boundaries rather than one ordered record instance.
- Source output agreement with `sortOn`, while the separately measured odd-size examples retain unequal counts.
- An occurrence-rank consumer: `Applications.Selection.pairwise_ranked hs.sorted hs.perm hindex` consumes any sorted/permutation result, including repeated values. Keep this composition in Examples so Sorting does not depend on Selection, and make no claim about indexing cost.

If a real consumer later needs a source sorted-input fixed point, the direct proof can use `Pairwise.take`, `Pairwise.drop`, `Pairwise.rel_of_mem_take_of_mem_drop` and `List.merge_of_le`; it need not strengthen to a total/antisymmetric order merely to use standard uniqueness. This is an available proof route, not an additional frozen deliverable.

Bottom-up and natural algorithms may consume the same merge observations. The alternating splitter and reversed accumulator pass remain distinct recurrences; this note does not replace their termination, multiplicity or stability obligations with the top-down theorem.

## 9. Corrections and limits relative to the old plan

No old requirement or report was modified. The main floor-left route and source/library split warning remain correct. This readiness note records the following precise clarifications:

- The reuse-plan opening's 107 count is historical; current scope is 112, with the unchanged frozen snapshot plus explicit reconciliation.
- The original C02-031 search gap is confirmed in the inspected pinned sort/list files. `sublist_mergeSort` is not an input-sublist lemma for `merge`.
- The key equality-decision assumption can remain local in a plain value-equality proof; it must remain explicit wherever the existing filter-based contract appears in the statement.
- The generic local comparator theorem is a sortedness contract, not a stability contract. Preserve the actual source key comparator in the latter proof.
- A direct source stable contract remains necessary before invoking existing standard-sort uniqueness for tagged records. Proving only key-sortedness and permutation cannot justify full-record equality.
- No new public arithmetic/list-prefix wrapper is justified solely by the proof plan. The standard take/drop equations already exist, and the saved measured prefix operations belong to their own observation domain.

This is a source-level feasibility assessment. No new Lean declaration was elaborated, no constructor/recursive equation script was compiled, no test or project check was run, no hash helper or Git command was used, and no gate state changed. Remaining elaboration risks are ordinary and concrete: keeping the length guard available to the well-founded recursion, orienting the `Perm.of_eq`/`Multiset.coe_add` rewrites correctly, normalizing Boolean equality versus proposition coercions in compatibility proofs, and using the actual recursive equation rather than attempting to unfold well-founded recursion by unrestricted simplification. Existing pinned proof bodies show the intended APIs and tactics, but only later validation of the matching immutable candidate can settle those risks.
