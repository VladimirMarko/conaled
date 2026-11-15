# Chapter 2 Exercise 2.3: three-way quicksort API readiness

Prepared 2026-11-03 for **C02-102**, within the existing book workflow.
This is bounded source/API preparation, unexecuted and uncompiled. It does
not activate Chapter 2, select an implementation candidate, create a shared
unit, change requirements, or confer acceptance. Chapter 1's existing full
gate remains the sole validator; its processes and active outputs were not
inspected or operated on by this task.

## 1. Finding and smallest remaining work

The needed independent partition boundary already exists as the saved,
unaccepted **XQ01** draft. The older Chapter 2 reuse plan's suggested extraction
must therefore be read against that later evidence: do not extract it again,
copy its laws into a new framework, or import the whole selector merely to
obtain its partition facts. The remaining exercise work is an actual
Chapter 2-local three-way sorter, its length termination, its prescribed
cons equation, and its ordinary sorting/content proof and connected cases.

No mathematical or source-interface obstruction was found. In particular,
termination does **not** require the pivot to belong to its tail. The existing
membership-premised strict-size theorem was written for selection and is not
the appropriate general argument for this exercise. Each recursive bucket is
at most as long as the tail, which is shorter than the complete cons input.

A sensible future placement remains the existing plan's proposed
`Applications/Sorting/Quick.lean`, alongside the ordinary quicksort work.
This is a placement proposal, not a newly existing module or frozen name.
The small XQ01 `Applications/Sequences/Partition.lean` is the useful value
prerequisite after its own integration and acceptance. Neither Selection's
recursive rank algorithm nor the measured partition executor is a necessary
import for the pure correctness proof.

The initial Chapter 2 prefix remains exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`. XQ01 is a distinct later candidate,
not part of that prefix and not an accepted dependency. The current inventory
has **112** rows; the preserved freeze used the historical **107**-row
snapshot. Both retain the same C02-102 exercise. All other source obligations,
including ordinary quicksort, the accumulator exercise and the separate
Exercise 2.4 tariff, remain unchanged.

## 2. Inputs, inspection boundaries and provenance

The complete current and preserved Chapter 2 inventories, frozen requirements,
complete reuse plan, full 435-line `Sorting.thy`, full current
`Selection/ThreeWay.lean`, `Selection/Rank.lean`, `Sorting/Sort.lean` and
`Sorting/Stable.lean` were read. The relevant retained Lean list sources and
pinned Mathlib declarations below were read directly. The final 324-line
source readiness report was read in full after its author stopped.

Applicable guidance was read from `conaled/AGENTS.md`,
`docs/agents/domain.md`, `docs/agents/architectural-quality.md`, `GLOSSARY.md`,
the ADR index and ADR 0001, and the relevant README development guidance.
The resulting design follows the existing carrier and ordinary observations,
keeps operations separate from correctness and cost, and preserves existing
public interfaces. This report does not start a new implementation or final
review loop.

The manuscript's Exercise 2.3 is printed p.28 / PDF p.34, retained in
`book-source/chapter02.txt` at 513–525. Its order convention is printed p.13.
The separately pinned Isabelle `Sorting.thy` contains ordinary quicksort at
327–339, but no `quicksort3` or `partition3` implementation or exercise proof.
Thus the three-way recurrence is printed source, while the proof below is a
proposed Lean reconstruction. The exact primary URLs, manuscript attribution,
source distinction, and full applicable 1,673-byte Isabelle notice are retained
in `research/quicksort-three-way-source-readiness.md`, sections 2 and 9, and
`book-source/ISABELLE-COPYRIGHT`. No implementation was translated by this task.

Project Git reads used only the pinned Nix launcher and read-only `git show`
and `git ls-tree`, with optional locks disabled. No checkout, merge, index or
ref operation occurred. Pinned library source was read from
`conaled/.lake/packages/`; retained Lean primary copies were used rather than
assuming an installed `src/lean` tree exists. No network retrieval was needed.

| Primary input | Exact identity |
| --- | --- |
| Book PDF, July 27, 2026 edition | SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; official source <https://fdsa-book.net/functional_data_structures_algorithms.pdf>. |
| `book-source/chapter02.txt` | 28,337 bytes / 562 lines; SHA-256 `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1`. |
| `book-source/Sorting.thy` | 14,846 bytes / 435 lines; SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`; Isabelle revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, `src/HOL/Data_Structures/Sorting.thy`. |
| Lean primary list sources | Lean v4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; exact retained file identities are in section 9. |
| Mathlib / Batteries | `56a005855ea17e0b0958f73ec801ae140b0a1679` / `66e469188fe07963e5cf666c7d4433f45b8131c5`. |
| Final parallel source report | `research/quicksort-three-way-source-readiness.md`, 21,439 bytes / 324 lines; SHA-256 `d555fa3519e4f2eed6870f674f50a8bd205e00076291159bc186df1c4ce90946`. |

## 3. Actual existing implementations and immutable comparison

Four immutable revisions were compared:

| Role | Revision |
| --- | --- |
| Original common source | `1aabd512284fe86254278ac631eda061d311050b` |
| Corrected Chapter 1 candidate | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Unchanged initial Chapter 2 prefix | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Saved independent partition draft XQ01 | `de5410286bbefd841dff50bef55c2e52d2ebbd2a` |

At the first three revisions, `Applications/Selection/ThreeWay.lean` is
byte-identical: 10,489 bytes / 226 lines, SHA-256
`bd72ca5f11d028cde9420ae42f9a9f1f84d6cfc00bf02bd528a61fd00f586d52`.
Its only import is `Applications.Selection.Rank`. In namespace
`Applications.Selection`, with `{α : Type u} [LinearOrder α]`, it defines
`partition3 p xs` by one `List.partition` on `x < p`, then another on the
upper remainder using `x = p`. The triple is the first lower list and the
second partition's equal and greater lists.

The full public source was inspected, not just this prefix. After the eight
partition declarations, it provides `sorted_partition`, `dispatch` and
`dispatch_value`; `PivotValid`; fuel-based `runWith` and `runWith_value`;
`selectWith` and its value/ranked/failure/success/policy facts; head and last
pivot validity; and `sortSelect` with the final equivalence facts. None is an
ordinary three-way quicksort implementation. The selector chooses a pivot
from its complete current input, which explains its strict-size premise.

`Selection.Rank` imports `Sorting.Sort`. Its `ordered` abbreviation is
`Sorting.sortOn id`; `ordered_perm` and `ordered_pairwise` are existing
reference-value facts. `Sorting.Sort` implements `sortBy` through
`List.mergeSort`, and `sortOn` through a key comparator. Its ordinary
`sortOn_correct` separates `KeySorted` and permutation. The further
`StableSort` contract is stronger than this exercise requires. These are
available specifications, not evidence that source quicksort already exists.

At XQ01, the shared file is **3,840 bytes / 87 lines**, SHA-256
`c83144cda94133662be7537fa9c2e8e7870f4959c55c78526d1a62e11fe1f56b`.
It imports only `Mathlib.Data.List.Perm.Basic` and
`Mathlib.Order.Defs.LinearOrder`, and uses namespace **`Sequences.Partition`**.
Its eight-declaration operation/law fragment is exactly the original fragment:
2,350 bytes, SHA-256
`b9b77db666fee99c520e2bebdddb8d4d9d2420800147ca54fc84bfd99344b287`.
This equality was independently compared from the Git objects.

XQ01's `Selection/ThreeWay.lean` adds the shared import and preserves all old
public partition names through same-signature definition/theorem adapters.
It is 9,718 bytes / 211 lines, SHA-256
`ba20014bce5fa78df547dbb04283511274883988d037233a9af8ac4ecc7e85fa`.
The entire suffix beginning at `theorem sorted_partition` is byte-identical
to the original: 7,882 bytes, SHA-256
`d81e7a883d8f974d7903090689cf292a1b4871fe65b0644258608fd03de227d3`.
`Selection/Rank.lean`, `Sorting/Sort.lean`, `Sorting/SourceMerge.lean` and
`Examples/RankSelection.lean` were also compared unchanged at all four inputs.
The retained XQ01 compatibility record independently records the same
fragment/suffix identities and the unchanged Selection consumer source.

The complete XQ01 pure module, Selection adapters/suffix, 60-line resource
module and 172-line examples were read directly from the candidate. Its
`Resources.Partition.partitionRun` is a separate actual single-tail recursive
execution, with `partitionRun_value` and `partitionRun_cost p xs` giving
`xs.length + 1` invocation work. It is not the pure two-partition definition
and not the book's three filters. This executor is unnecessary for C02-102's
pure proof, and its cost must not be transported by value equality.

No `Applications/Sorting/Quick.lean` was present in the inspected relevant
source trees. XQ01 remains a committed, uncompiled, unaccepted draft. The
candidate record and integration addendum do not authorize its premature
integration or convert source equality into validation.

## 4. Exact small partition API and source recurrence bridge

All declarations in this table are **existing at XQ01**, under
`{α : Type u} [LinearOrder α]`. Explicit argument order is shown. Write
`T := Sequences.Partition.partition3 p xs`, `L := T.1`, `E := T.2.1`,
and `G := T.2.2`; the nested product shape is ordinary Lean tuple notation.

| Existing declaration | Statement and use |
| --- | --- |
| `partition3 p xs` | `List α × List α × List α`, using the two stable `List.partition` operations described above. |
| `partition3_eq_filters p xs` | `T = (xs.filter (fun x => decide (x < p)), xs.filter (fun x => decide (x = p)), xs.filter (fun x => decide (p < x)))`. No pivot-membership premise. |
| `partition3_perm p xs` | `(L ++ E ++ G).Perm xs`. Exact occurrence content, not just set union. |
| `partition_left_mem p xs x` | `x ∈ L ↔ x ∈ xs ∧ x < p`. |
| `partition_equal_mem p xs x` | `x ∈ E ↔ x ∈ xs ∧ x = p`. |
| `partition_right_mem p xs x` | `x ∈ G ↔ x ∈ xs ∧ p < x`. |
| `partition_lengths p xs` | `L.length + E.length + G.length = xs.length`. |
| `partition_strict_sizes p xs hp` | Given `hp : p ∈ xs`, `L.length < xs.length ∧ G.length < xs.length`. Membership is sufficient; it is not claimed necessary. |
| `partition3_nil p` | The triple for `[]` is `([], [], [])`. |
| `partition3_cons p y ys` | With `t := partition3 p ys`, return `(y :: t.1, t.2.1, t.2.2)` if `y < p`, otherwise `(t.1, y :: t.2.1, t.2.2)` if `p = y`, otherwise `(t.1, t.2.1, y :: t.2.2)`. This is a value equation, not a one-pass cost claim for the underlying pure operation. |

A future exercise implementation must expose the actual nil/cons recurrence.
For mathematical discussion only, call it `Q`. With the buckets of the
**tail** `xs`, an explicit value grouping is:

```text
Q [] = []
Q (p :: xs) = Q L ++ (p :: (E ++ Q G))
```

This preserves the printed value `Q L ++ ((p :: E) ++ Q G)`. Existing
`List.cons_append` and `List.append_assoc` justify the ordinary grouping;
no append-cost equality is asserted. The pivot occurs once, in front of
all equal-tail occurrences. Only `L` and `G` are recursive inputs.

If the pure definition calls the saved shared partition, rewriting its
actual cons equation with `partition3_eq_filters p xs` gives the printed
three-filter equation exactly. This is the economical value-level route
using the existing fragment. The executable partition body in that choice
is still two `List.partition` calls. If a later task requires literal
three-filter execution or a source-specific tariff, it must retain that
actual realization and prove its own cost correspondence; it cannot infer
that correspondence from the equation just described. Defining the pure
exercise directly with the three filters and using the shared equation in
proofs is also possible, but no new independent partition theory is needed.

There is no reason to define a second recursive reference sorter solely for
this value bridge. Defining `Q` as `sortOn id` would not implement the printed
source recursion, even if output equations could be proved; it supplies no
source-cost correspondence. Exact public names, equation-compiler names and
implementation syntax remain future Chapter 2 choices.

## 5. Termination on the held pivot's tail

The primary retained Lean declaration is:

```lean
theorem List.length_filter_le (p : α → Bool) (l : List α) :
  (l.filter p).length ≤ l.length
```

Both arguments are explicit. It is at `LeanList-Lemmas.lean:1272` within the
read 1259–1283 block. After `partition3_eq_filters`, apply it separately to
`fun y => decide (y < p)` and `fun y => decide (p < y)`, on the tail `xs`.
The resulting arithmetic is:

```text
L.length ≤ xs.length < xs.length + 1 = (p :: xs).length
G.length ≤ xs.length < xs.length + 1 = (p :: xs).length.
```

This gives a well-founded definition using the input list’s length. The equal
bucket does not need a decreasing proof because it is not recursively sorted.
The existing `partition_lengths p xs` also implies both non-strict bucket
bounds by natural-number arithmetic; either route is short. The filter route
states directly why it is valid for every pivot and tail. No new public
strict-size wrapper is necessary just to express the successor step.

`partition_strict_sizes p xs hp` must not introduce `hp : p ∈ xs` as a new
sorter assumption. For the actual parent `[0,2,1]`, the tail `[2,1]` has
`G = [2,1]`; the purported strict tail bound `2 < 2` is false, while the
required parent bound `2 < 3` holds. The existing theorem can still be used
where its premise really holds, as in selection. Its absence for this tail
is an application mismatch, not a theorem defect.

A proof could instead partition the full `p :: xs`, use its membership,
and relate those buckets back to the tail. That adds an unnecessary value
bridge for termination. It must never silently change the executable body
to full-input buckets followed by a second explicit pivot.

No fuel, partial definition, default element, `Inhabited α`, distinctness,
finite-carrier instance or valid pivot-policy record is required. Let-bound
product projections and decreasing goals will need ordinary explicit rewrites
when the future definition is elaborated. This preparation does not claim
that any exact termination script or generated equation has been compiled.

## 6. Sorting and occurrence proof using existing observations

Prove the occurrence result first, or prove it together with pairwise order
in the same induction on input length. The two induction hypotheses belong
to the actual `L` and `G`, with the decreases from section 5. Do not assume
sortedness of the original input or of the suffix of an unrelated algorithm.

### 6.1 Exact occurrences, including the held pivot

The standard observation can be `List.Perm`; the book's multiset equality
is equivalent. The relevant directly read APIs are:

```lean
Multiset.coe_eq_coe {l₁ l₂ : List α} :
  (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂

Multiset.coe_add (s t : List α) :
  (s + t : Multiset α) = (s ++ t : List α)

Multiset.cons_coe (a : α) (l : List α) :
  (a ::ₘ l : Multiset α) = (a :: l : List α)

Multiset.add_cons (a : α) (s t : Multiset α) :
  s + a ::ₘ t = a ::ₘ (s + t)
```

The locations are `Mathlib/Data/Multiset/Defs.lean:100`,
`AddSub.lean:58,109`, and `ZeroCons.lean:101`. These statements have no
`DecidableEq α` or payload-order premise. Protected `Multiset.add_assoc`
at `AddSub.lean:77` handles grouping. This supplies a concrete occurrence
proof without inventing a permutation helper or depending on uninspected
argument conventions of a pivot-reordering lemma.

Let `M` denote ordinary list-to-multiset coercion, not a new declaration.
Convert the two recursive permutation hypotheses and `partition3_perm` by
`Multiset.coe_eq_coe`. The cons case is precisely:

```text
M (Q L ++ (p :: (E ++ Q G)))
 = M (Q L) + (p ::ₘ (M E + M (Q G)))
 = M L + (p ::ₘ (M E + M G))
 = p ::ₘ (M L + (M E + M G))
 = p ::ₘ M (L ++ E ++ G)
 = p ::ₘ M xs
 = M (p :: xs).
```

The one pivot-moving step is `Multiset.add_cons`; no element is discarded
or duplicated. Convert back to `List.Perm` if that is the public form.
The existing `List.Perm` append/cons/transitivity calculus is an equally
ordinary route; it is not necessary to implement any new occurrence carrier.
Permutation then yields exact membership and length consequences as needed.
Set equality alone is insufficient for the equal block.

### 6.2 Pairwise nondecreasing order

Two primary list interfaces are enough for the final assembly:

```lean
List.pairwise_cons :
  Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l

List.pairwise_append {l₁ l₂ : List α} :
  (l₁ ++ l₂).Pairwise R ↔
    l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b
```

They are at `LeanList-Basic.lean:1378` and
`LeanList-Pairwise.lean:170–172`. The latter file's
`pairwise_of_forall_mem_list` at 269–270 takes
`h : ∀ a ∈ l, ∀ b ∈ l, r a b` and returns `l.Pairwise r`.
Use it for the equal bucket: both members equal `p`, so reflexivity applies.

The recursive content laws transfer every output membership to its input
bucket. The three existing membership iff theorems then provide:

- every member of `Q L` is strictly below `p`;
- every member of `E` equals `p`;
- every member of `Q G` is strictly above `p`.

The induction hypotheses sort `Q L` and `Q G`. The cons and append criteria
sort the middle `p :: E` and connect both sides: strict inequalities imply
weak inequalities, and transitivity handles a left member versus a right
member. The result is `List.Pairwise (fun a b => a ≤ b)`, not strict ordering
and not a duplicate-free list. Multiplicity and sortedness are distinct
observations and both are required by C02-102.

`Selection.sorted_partition` already illustrates these order and content
connections for its `ordered` reference value. Its surrounding selector
import is unnecessary for this proof. Moving another theorem or copying a
large selector-dependent fragment is not justified merely to shorten this
exercise. Equality to an existing correct canonical sorter can be a later
corollary of ordinary sortedness/permutation uniqueness; it is not needed
to prove this prescribed recurrence or its two required observations.

### 6.3 Assumptions and prospective imports

The saved public partition API and the source both use an arbitrary
`α : Type u` with `[LinearOrder α]`. This supplies the comparisons, equality
decisions and exhaustive lawful classification needed by the three filters.
The filter-length fact itself is order-free; multiset coercion and its
addition/cons algebra are also order-free. The pairwise assembly uses the
usual reflexivity/transitivity and bucket bounds. This does not justify a
new arbitrary-comparator partition theorem: incomparable elements could be
absent from all three literal filters without totality.

Do not add a separate payload equality assumption, global inhabitance,
nonempty list premise, `Nodup`, finite universe, or externally selected pivot.
An empty element type has only the nil input and needs no manufactured pivot.
A keyed variant with independent payload/key universes would be a separate
extension with explicit source and stability obligations; it is not required
by this ordinary-element exercise.

After the saved XQ01 dependency is properly integrated, the concrete pure
import route is `Applications.Sequences.Partition`, ordinary pairwise/list
lemmas, and, if using the displayed occurrence calculation,
`Mathlib.Data.Multiset.AddSub`. Exact sufficient import closure remains for
normal future elaboration; no claim of a compiler-verified minimal import
list is made. Do not import `Applications.Selection.ThreeWay` or
`Applications.Resources.Partition` merely for these pure facts, and do not
add a new sorting correctness record.

## 7. Connected independent cases and excluded substitutions

The case author's independently derived compact expectations exercise the
actual source body, rather than only a generic sorted-output oracle:

| Input / observation | Expected value or boundary |
| --- | --- |
| `[]`, `[2]` | `[]`, `[2]`; singleton has two empty strict children and one held pivot. |
| `[2,2,2]` | Tail buckets `([], [2,2], [])`; full result `[2,2,2]`. The equal block is retained directly. |
| `[2,3,1,2,0,3,2,1]` | Tail buckets `[1,0,1]`, `[2,2]`, `[3,3]`; child results `[0,1,1]` and `[3,3]`; final `[0,1,1,2,2,2,3,3]`. |
| `[0,2,1]` | Pivot absent from its tail; greater bucket `[2,1]` equals the whole tail in length, but is shorter than the parent. |
| Omit pivot or replace `E` by one representative | Can still yield a sorted list with the same underlying set, while losing required multiplicities. |
| Partition the full input, then add pivot | Adds an extra pivot occurrence. The source filters the tail. |
| Recursively sort `E` | May preserve ordinary values but changes the required recursive calls. |
| Recursively sort `p :: E` | Fails the length decrease on all-equal input. |

The existing XQ01 examples remain useful partition clients: replicate input,
old/shared equality, mixed buckets, an outside pivot and an absent interior
pivot. Its outside-pivot example shows why a strict bound for arbitrary
partition input is false; its interior example shows pivot membership is
not necessary for strict shrinkage in every individual case. Preserve these
old cases and Selection's public connections rather than replacing them
with the new sorter examples.

No complexity, comparison count, stability of distinct keyed payloads,
expected running time or probability consequence follows from these values.
Three filters, two stable partition calls and the measured one-pass worker
have different actual executions. C02-103's supplied two-way tariff remains
separate; it is not an implicit tariff for `Q`. The accumulator exercise's
universal suffix and cons-only requirements are also a different C02 row.

## 8. Remaining implementation steps and actual limits

Within future Chapter 2 work, after its accepted prerequisites:

1. Reuse the existing accepted partition boundary, preserving XQ01's original
   candidate/history and the old Selection adapters and suffix. Follow the
   already retained integration addendum; do not alter the initial prefix.
2. Author the actual ordinary three-way recursion with only strict-tail
   recursive calls. Establish the length decreases directly from filter
   bounds and expose its source cons equation with the complete equal block.
3. Prove permutation/multiset preservation and pairwise order using the actual
   two recursive hypotheses and the existing bucket laws. Keep raw content
   and order claims separate from any later measured executor.
4. Connect the compact expected-value/domain cases to those actual public
   theorems, alongside existing partition/Selection cases. Preserve every
   other Chapter 2 obligation and use its existing validation/review sequence.

No exact future names, generated recursion equations, chosen tactic script,
new scope or candidate are frozen here. There is no unresolved mathematical
obstruction in the bounded route. Remaining uncertainty is ordinary uncompiled
implementation work: let/projection rewriting in termination goals, coercion
and append grouping, import closure, and actual theorem application during
elaboration. The saved XQ01 draft itself still requires its matching gates.
These are not grounds to weaken the exercise, invent a framework or claim
validation from source inspection.

## 9. Exact retained identities and final disposition

Paths in this first table are relative to `fdsa-control/`. The complete
planning documents and XQ01 records listed here were read; no existing record
was rewritten. The final source report's identity is in section 2.

| Control input | SHA-256 |
| --- | --- |
| `research/chapter02-obligations.md` | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `reviews/source-inventories-before-scope-repair/chapter02-obligations.md` | `edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d` |
| `reviews/chapter02-requirements.md` | `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36` |
| `research/chapter02-reuse-plan.md` | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| `reviews/three-way-partition-candidate.md` | `96264044d5adef8a13f771d84a2153ae753c0b0e855d9306ed0f9e3409460d7c` |
| `reviews/partition-shared-integration-addendum.md` | `99a64a6db17c7114e98cca6087e440af4b4e9872962c6df6885ba0b8e1e4f3e2` |
| `reviews/three-way-partition-source-identities.json` | `c65556b40f31c48cc3df3321e02256a007cd8c1b3dea571b7b3ec7e1ac1dc1c3` |
| `reviews/three-way-partition-compatibility-reading.json` | `e5ba9687cc5215090d252d09cb1a7ed113381a7d05b0c6dd39303c0cd8a0faea` |

The relevant primary library ranges were read, not entire unrelated library
modules. Ordinary file hashes identify the retained sources; they do not
claim successful elaboration or authenticate compilation.

| Pinned source | SHA-256 / inspected declarations |
| --- | --- |
| `book-source/LeanList-Basic.lean` | `566e74dd5c3e72b2111af000b8bd1552f1aaffe29be317ba01bc91c9e5b55293`; append/cons/associativity, `pairwise_cons`, ordinary `Perm` constructors. |
| `book-source/LeanList-Lemmas.lean` | `9365fb1c6da0313a4c73e8cf096377e69c28ece28d38290a0423e5f8cc1fdfdb`; filter/length/sublist and `partition_eq_filter_filter` at 3127–3130. |
| `book-source/LeanList-Pairwise.lean` | `fcc984c70a81216c178d42a858dea5e3640201023a9a4d2837e76f138fd9b0f4`; `pairwise_append`, pairwise membership criterion. |
| `book-source/LeanListSort-Lemmas.lean` | `e04f8070b20080cdbcdd31a6d240e267363e308a5804fdaf6749c92a885547c0`; existing permutation assembly/reference uniqueness uses, not a source quicksort. |
| Mathlib `Data/Multiset/Defs.lean` | `09b5004aedbde97d9fc6f3ad40510eb2d120c7485088c30cf2e2f72e81d72334`; ordinary quotient/coercion and `coe_eq_coe`. |
| Mathlib `Data/Multiset/ZeroCons.lean` | `c027e054f500a81906405fb496e55bcc9adee1d2d684c4074bcec923e87dbf17`; ordinary empty/cons and `cons_coe`. |
| Mathlib `Data/Multiset/AddSub.lean` | `1fd0c73c2dc4c3a2ff08e32939490e1b710e283c83cbaf73166eddc07a0f9f1e`; order-free addition/coercion/cons/associativity laws before its later erasure section. |
| Mathlib `Data/List/Perm/Basic.lean` | `73cb327fd595ffec05bc06dc317f339b05824096cb2d68873d4f39d49e96ef71`; actual shared-module import and permutation interface. |
| Mathlib `Data/List/Pairwise.lean` | `41965f675c118d7828714a6de4d924871f4f942c8546a93b3675d39baf02aa5a`; existing ordinary pairwise import boundary. |

For the immutable comparison, the unchanged relevant source identities are:
`Selection/Rank.lean` — `4a82df75593d909e2968bf1e27cbfea52c9795abfe81250bb2385e7dfc16f965`;
`Sorting/Sort.lean` — `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218`;
`Sorting/SourceMerge.lean` — `bebd8eb2f06d92cc10e6f319c96b7965cdee36ff14c4a8b0b19e1351e8ebeaf2`;
`Examples/RankSelection.lean` — `641a752cdee9b2ab30e66bb2f7feda2548cffebfe6733460b52ff5f7e119520e`.
XQ01's directly read resource/example files are respectively
`3317bd84f5b8eacb0ede5d9fcde4adc98361fb2afadf7e41afff1d4a5e14e6d2`
and `7bae757d70436cca816888147938cfa38053abe8affebc367d74e0e67498d526`.

Only this assigned Markdown report was authored. No Lean source, other report,
requirement, inventory, ticket, worktree, ref, index, cache, active output,
compiler/checker/project hash helper or remote item was changed or operated
on beyond the permitted static source/control reads. The report was fully
read back before its stopped handoff. All source and validation status,
Chapter 1's acceptance prerequisite, and the original Chapter 2 scope and
initial prefix remain intact.
