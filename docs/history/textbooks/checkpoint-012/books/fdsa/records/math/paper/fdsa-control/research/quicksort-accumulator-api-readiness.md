# C02-101: accumulator quicksort API and termination readiness

Prepared 2026-11-03. **Report-only source/API preparation. No Lean implementation,
new shared unit, scope freeze, chapter activation, compiler result or acceptance
is supplied.** The only authored path is this report. The complete original
Chapter 2 obligations remain queued under the existing workflow.

## 1. Conclusion and preserved scope

The proposed nested worker is a feasible small implementation of Exercise 2.2:
both recursive calls decrease the length of their **first** list argument, and
one induction generalized over **every suffix** proves its value equality with
the actual ordinary quicksort followed by that suffix. Existing pinned list
operations and lemmas suffice. No new carrier, executor, comparison-law record,
difference-list representation or probability dependency is needed.

This is a remaining Chapter 2 algorithm client, not a newly justified shared
unit. The ordinary first-pivot definition and termination in C02-017 provide the
definition to which the worker is related. C02-018–023 remain separate content
and order obligations; their correctness results supply later sorting
corollaries but are not logical premises of the suffix simulation itself.
There is no identified ordinary quicksort implementation in the inspected
conaled sorting modules that can simply be called or renamed.

The unchanged freeze refers to the original 107-row inventory. The recorded
C02-088 reconciliation appended C02-108–112, so the current inventory has
**112 obligations**. C02-101 remains exactly the append-free implementation and
universal-suffix requirement in both records. The initial Chapter 2 foundation
prefix is still `c80eec92f5458eccfd1c34c8314d666c2a1e3847`; this report neither
changes that prefix nor includes the later `c28ba718...` potential addition.
Chapter 1 acceptance, later implementation and all existing validation/review
requirements remain prerequisites. No implementation base is selected here.

## 2. Source statement and actual local reuse

The retained book reading copy, `book-source/chapter02.txt:508–512`, locates
Exercise 2.2 on printed p.28 / PDF p.34. It asks for accumulation by cons without
append and equality for both arbitrary list arguments. It supplies no worker
recurrence, numeric cost formula or full tail-recursion requirement. The
completed source readiness report separately checked the PDF passage.

The ordinary source is `book-source/Sorting.thy:327–339`, at Isabelle commit
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. It chooses the first occurrence,
filters only the tail using `y < pivot` and `pivot ≤ y`, and appends the left
result, singleton pivot and right result. Equal keys go right. Its explicit
element class is `linorder`. The accompanying permutation/multiset, set and
sortedness results concern this ordinary recursion. No `quicksort2` or generated
quicksort timing implementation was recovered from that theory.

The complete Sort/SourceMerge modules and the indicated Stable interface were read:

| Existing source | Actual API and consequence |
| --- | --- |
| `conaled/Applications/Sorting/Sort.lean`, 128 lines | `sortBy` is `List.mergeSort`; `sortOn` pulls back key order; `insertionOn` is `List.insertionSort`. Their existing value/stability theorems do not supply a first-pivot quicksort recurrence. The proof of `sortBy_sorted_compatible_on` illustrates a theorem recursive on input length, with explicit decreasing obligations. |
| `conaled/Applications/Sorting/SourceMerge.lean`, 37 lines | `sourceMerge` is the literal merge adapter and terminates by the sum of its two input lengths; `sourceMerge_eq_merge` proves its actual value bridge. This is an existing example of source correspondence and well-founded definition style, not the quicksort operation or the correct measure for the proposed accumulator. |
| `Applications/Sorting/Stable.lean:13–24` | `KeySorted` is ordinary `List.Pairwise` on the key relation; `Stable` and `StableSort` impose additional equal-key observations. These contracts remain separate from the unconditional suffix equation. |

A bounded search for quicksort names in `Applications/Sorting`,
`Applications/Selection` and `Examples/StableSorting.lean` returned no matches.
The inspected pinned `Mathlib/Data/List/Sort.lean` describes insertion sorting
and list order predicates, not a ready source quicksort. These are scoped
observations, not a claim of absence from every archived project or dependency.
No unrelated shared draft was opened to manufacture a dependency.

## 3. Proposed mathematical recurrence, with no promised public names

Use `Q` for the **future actual ordinary source definition** and `A` for a
possible accumulator implementation. These are mathematical notation in this
report, not existing Lean declarations, agreed future names or generated
recursor/equation names. For a pivot `x` and tail `xs`, abbreviate:

```text
L = xs.filter (fun y => decide (y < x))
R = xs.filter (fun y => decide (x ≤ y))

Q [] = []
Q (x :: xs) = Q L ++ [x] ++ Q R

A [] suffix = suffix
A (x :: xs) suffix = A L (x :: A R suffix)
```

The worker body must perform those actual two worker calls. The result of the
right call becomes part of the suffix supplied to the left call. Neither
`Q xs ++ suffix`, another library sort, a separately sorted suffix nor a
reversed accumulator is a faithful replacement for that executable restriction.

The occurrence of append above belongs to the ordinary specification and the
proof. The worker's proposed recursive result assembly uses only cons. Standard
`List.filter` itself is the inspected order-preserving cons recurrence.
The source's append association may be normalized for this value proof by
associativity. That normalization is not a cost-preserving execution claim.

## 4. Termination: the suffix is not part of the decreasing measure

Fix the comparison operations throughout the recursion. For each nonempty
input `x :: xs`, the existing filter bound gives:

```text
L.length ≤ xs.length < (x :: xs).length
R.length ≤ xs.length < (x :: xs).length.
```

This proves decrease for both actual recursive calls:

| Call | First argument measured | Second argument |
| --- | --- | --- |
| Inner right call | `R` | The original arbitrary suffix |
| Outer left call | `L` | `x :: A R suffix`, using the actual inner result |

There is no comparison between the two child lengths. Either child can have
the entire tail length. The child is still strictly smaller than the original
cons input. No sortedness, distinctness, complementarity, permutation or output
length theorem is needed to prove this decrease.

The intended well-founded measure is first-input length, equivalently the
inverse image of the usual natural-number order under
`(input, suffix) ↦ input.length`. In eventual source this can be expressed by a
`termination_by` clause selecting the first input's length. Its exact binder
spelling depends on the eventual definition; this note does not promise the
equation compiler's generated parameter names, case names or recursor arity.

The pinned source supports a short explicit child proof. For any Boolean
predicate `p`, the term

```lean
Nat.lt_succ_iff.mpr (List.length_filter_le p xs)
```

has the needed strict successor bound; simplification with
`List.length_cons` identifies the parent length. This exact natural-number
lemma use already occurs at `LeanList-Lemmas.lean:1307`. The same retained
file's proof of `List.eraseDups_append` at 3720–3730 uses a filtered first-input
length bound and `termination_by as.length` while its other list argument
changes. That is useful proof-construction evidence only: no erase operation,
equality instance or duplicate-removal lemma is a dependency of this exercise.

In the future decreasing goals, expose the actual filter lets and supply the
two local bounds. Do not require a theorem about the length of the recursively
produced suffix or use the desired suffix theorem to justify termination.
There is no need for fuel, a partial definition, a default payload, or a
lexicographic phase machine.

The sum of the two argument lengths is not a reliable substitute. The
independent cases author identified the ordinary-order input
`[2,1,2,3,0]` with suffix `[4,0,2]`: the root has total argument length
`5 + 3 = 8`, while its outer left call has first input `[1,0]` and actual
suffix `[2,2,3,4,0,2]`, totaling `2 + 6 = 8`. First-input length decreases
from 5 to 2. This is a mathematical check of the proposed recurrence, not an
executed Lean case or a new required test campaign.

## 5. The all-suffix induction and actual nested-call substitution

The induction property must be

```text
P(input) := ∀ suffix, A input suffix = Q input ++ suffix.
```

A strong induction on first-input length gives the usable hypothesis

```text
∀ child, child.length < input.length →
  ∀ suffix, A child suffix = Q child ++ suffix.
```

Equivalently, a recursive proof theorem can keep the suffix generalized and
use the same decreasing measure as the definition. An actual generated
functional induction principle may also be usable once the definition exists,
but its exact type must be inspected then. Ordinary structural list induction
with an IH only for the unfiltered tail does not directly provide these child
claims. An IH fixed at the original suffix or only at `[]` is also too weak.

The empty case reduces to `suffix = [] ++ suffix`. In the nonempty case,
instantiate the smaller-child IH **first at the suffix actually passed**:

```text
A (x :: xs) suffix
  = A L (x :: A R suffix)                     -- actual worker equation
  = Q L ++ (x :: A R suffix)                  -- left IH, that actual suffix
  = Q L ++ (x :: (Q R ++ suffix))             -- right IH, original suffix
  = (Q L ++ [x] ++ Q R) ++ suffix             -- ordinary list algebra
  = Q (x :: xs) ++ suffix.                    -- actual ordinary equation
```

The left IH is used at `x :: A R suffix`, not at an independent list with a
similar length. The right IH then rewrites its real occurrence inside that
suffix. One can reverse the order of these proof rewrites, but the implemented
data dependency must remain the same.

After substituting both IHs and exposing the actual ordinary equation,
normalizing with `List.append_assoc`, `List.cons_append` and
`List.nil_append` closes the value algebra. For example, the right side
`((P ++ [x]) ++ T) ++ suffix` normalizes to
`P ++ (x :: (T ++ suffix))`. If the ordinary equation is right-associated,
the same normal form results. No cost equality is inferred from that rewrite.

The empty-suffix corollary follows using `List.append_nil`. It is a useful
client of the universal theorem, not a substitute for it.

## 6. Exact pinned list interfaces

These declarations were read in the retained Lean 4.35.0 sources at commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The installed toolchain source path
was not assumed or probed. The source files are the exact retained copies
already pinned by the Appendix A inventory.

| Declaration and inspected position | Exact useful shape / assumption |
| --- | --- |
| `List.filter`, `LeanList-Basic.lean:483–487` | `(p : α → Bool) → List α → List α`; nil returns nil; a true head is consed and a false head is skipped. No payload structure. |
| `List.filter_nil`, Basic:489 | `filter p [] = []`, with `p` implicit. |
| `List.length_cons`, Basic:89–90 | `(List.cons a as).length = as.length + 1`; head and tail implicit. |
| `List.length_filter_le`, `LeanList-Lemmas.lean:1272–1281` | `(p : α → Bool) (l : List α) : (l.filter p).length ≤ l.length`. Both arguments are explicit, in predicate/list order. |
| `List.filter_sublist`, Lemmas:1423–1425 | `{p : α → Bool} : ∀ {l : List α}, filter p l <+ l`. Available for inherited observations, but unnecessary when the direct length bound suffices. |
| `List.nil_append`, Basic:609 | `(as : List α) : [] ++ as = as`. |
| `List.cons_append`, Basic:610 | `{a : α} {as bs : List α} : (a :: as) ++ bs = a :: (as ++ bs)`. |
| `List.append_nil`, Basic:612 | `(as : List α) : as ++ [] = as`. |
| `List.append_assoc`, Basic:627 | `(as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs)`. |
| `List.append_cons`, Basic:641 | `(as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs`. A convenient existing alternative bridge; no renamed wrapper is needed. |
| `List.pairwise_append`, `LeanList-Pairwise.lean:170–172` | `(l₁ ++ l₂).Pairwise R ↔ l₁.Pairwise R ∧ l₂.Pairwise R ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, R a b`. Arbitrary relation; used only when discussing sortedness of the final concatenation. |

The core source declares independent universes for list element types.
Everything in the length/append part is polymorphic in `α : Type u`.
No `DecidableEq α`, `BEq α`, `Inhabited α`, `Finite α` or numeric
payload assumption is introduced by those lemmas.

For future imports, the actual ordinary-sort module and the existing Lean list
lemmas are sufficient for the simulation. `Init.Data.List.Lemmas` is the
retained module containing the filter-length facts; ordinary list append facts
are in `Init.Data.List.Basic`. The surrounding project sorting modules already
use the standard list infrastructure through `Mathlib.Data.List.Sort`.
This is a source-level import recommendation, not a compiled minimal-import
certificate. No new source file or import is created by this report.

## 7. Minimal hypotheses and semantic boundaries

| Layer | Necessary content |
| --- | --- |
| Raw filter recursion and termination | Finite lists and the chosen Boolean comparisons. For literal proposition-valued `<` and `≤` filters, their operations and decision procedures supply the corresponding Boolean predicates. |
| Universal suffix simulation | The actual two matching recurrences and child length decrease. It uses no comparison laws, complementary-partition proof, sortedness or correctness theorem for `Q`. |
| Ordinary source specialization | Preserve the book's lawful linear order and exact strict-left/nonstrict-right filters. If a previously selected generic ordinary sorter uses one Boolean predicate and its negation, its correspondence with the literal second filter needs the lawful-order complement identity. This task does not choose a new generic operation interface. |
| Payload/key formulation, if the ordinary sorter exposes one | A key map `α → κ` may have independent universes. Comparison operations/laws belong to keys; full payload equality and inhabitation are unnecessary. The suffix still has the same payload type as the output. |
| Sorting result at empty suffix | The universal equation plus the ordinary sorter's separately established permutation/sortedness. Existing generic sorting contracts remain available without redefining them. |
| Sorting result at arbitrary suffix | The suffix must itself be sorted and every prefix element must precede every suffix element. The exact `pairwise_append` theorem exposes this boundary. No such premises are allowed to narrow the exercise's value equality. |

The weak proof premise description is not a promise to remove assumptions from
the type of an ordinary sorter that has not yet been implemented. Reuse the
actual selected comparison parameters and inherited source assumptions; do not
build public wrappers merely to restate each layer of this table.

Duplicate-bearing lists, suffixes overlapping the input, unsorted suffixes and
suffix elements below the prefix are all allowed by the value law.
`A [2] [1] = [2,1]` is the simplest boundary: even a sorted suffix does not
make the concatenation sorted without the cross-order premise. Empty input
returns the entire suffix unchanged. With an empty payload type, the nil
branches suffice; no default pivot is needed.

The nested right call is not in tail position. Cons accumulation therefore
does not by itself establish complete tail recursion, constant stack use,
constant allocation or a compiler optimization claim. Exercise 2.2 asks for
append-free accumulation; the explicit tail-recursion wording elsewhere in
Chapter 2 belongs to a different exercise.

## 8. Minimal implementation handoff and actual remaining uncertainty

After Chapter 2 is authorized under its existing prerequisites:

1. Implement and retain the actual ordinary first-pivot source definition and
   its length termination, as already required by C02-017.
2. Add the actual cons-only nested worker using the same tail filters and
   first-input-length termination. Inspect the body for the exercise's
   no-append restriction; output equality alone does not establish it.
3. Prove the universal-suffix equation with the generalized property above.
   Keep child bounds local unless another genuine client needs a public fact.
4. Connect the empty-suffix result to ordinary quicksort correctness and the
   already-required nonempty-suffix cases. Reuse the independent cases report
   for discriminating expectations; do not add another acceptance gate.
5. Leave C02-024, C02-102/103, the literal append-inclusive execution and all
   other original obligations with their existing scopes.

No mathematical obstruction was found. The concrete remaining formal work is
definition elaboration, exposing both filtered-tail termination goals and
using the eventual public equations in the proof. A strong length induction
avoids guessing generated recursor signatures. Reduction of local filter lets
and ordinary definitions may require explicit unfolding. None of these has
been tested by a compiler in this pass, and none warrants new premises,
unchecked recursion or weakening the arbitrary-suffix statement.

The prior average/conditional/random-pivot reports were read for scope
consistency. They retain actual execution/distribution links and the distinct
resource models. In particular Exercise 2.4 excludes append traversal, while
the separately required literal append-inclusive execution accounts for it.
A value simulation gives neither those numerical identities nor a new
`Tquicksort2` theorem. This report adds no metric, expected-work, primitive-test,
runtime or potential obligation.

## 9. Exact read identities and limits

All identities below are ordinary SHA-256 readings of the named source/control
files. No project hash helper or active output was read. Complete freeze,
current inventory, reuse plan, scope reconciliation, three quicksort plans,
conditional-plan source assessment and the stopped accumulator source report
were read. List/library inspection was limited to the declarations and nearby
proof patterns identified above.

| Input | SHA-256 |
| --- | --- |
| `book-source/chapter02.txt` | `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1` |
| `book-source/Sorting.thy` | `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca` |
| `book-source/LeanList-Basic.lean` | `566e74dd5c3e72b2111af000b8bd1552f1aaffe29be317ba01bc91c9e5b55293` |
| `book-source/LeanList-Lemmas.lean` | `9365fb1c6da0313a4c73e8cf096377e69c28ece28d38290a0423e5f8cc1fdfdb` |
| `book-source/LeanList-Pairwise.lean` | `fcc984c70a81216c178d42a858dea5e3640201023a9a4d2837e76f138fd9b0f4` |
| `conaled/Applications/Sorting/Sort.lean` | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| `conaled/Applications/Sorting/SourceMerge.lean` | `bebd8eb2f06d92cc10e6f319c96b7965cdee36ff14c4a8b0b19e1351e8ebeaf2` |
| `conaled/Applications/Sorting/Stable.lean` | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/List/Sort.lean` | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |
| `fdsa-control/reviews/chapter02-requirements.md` | `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36` |
| `fdsa-control/research/chapter02-obligations.md` | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `fdsa-control/research/chapter02-reuse-plan.md` | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| `fdsa-control/research/scope-reconciliation.md` | `21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87` |
| `fdsa-control/research/quicksort-average-proof-plan.md` | `ca2090accf91ac662f2738486f7590e8b29968be524794e9356257d5f918dc46` |
| `fdsa-control/research/quicksort-conditional-mean-preflight.md` | `464af5974d485823b7ecb76b7546ad793ed860fbf947afdb03ef11d91b25b66c` |
| `fdsa-control/reviews/quicksort-conditional-mean-source-preflight.md` | `a268d4a74db81230a4fdb8b0350f7aaaebc379eb38a2439a18d86c0e0c868b55` |
| `fdsa-control/research/random-pivot-api-preflight.md` | `91d34b4c86d315935f0df98023cf382fe3d141e8ab7d748baf9fdc64738a0ed0` |
| `fdsa-control/research/quicksort-accumulator-source-readiness.md` | `ce8c019bfe437bbdb71e5863119469a67c0f0d1a7961a3c0f879566731025eba` |

The retained Lean source pin is recorded in
`fdsa-control/research/appendix-a-obligations.md:17–32`; its current file identity
is `91233486d25272ef0e6be256f40de1ed35bee61bb6b8d8dfb9845d36cc869002`.
The Mathlib pin remains `56a005855ea17e0b0958f73ec801ae140b0a1679`.
This pass did not query or mutate Git refs. The source note preserves the exact
book/Isabelle provenance and complete applicable Isabelle notice; the retained
Lean library files carry their Apache-2.0 attribution. Reading source is not an
Isabelle rebuild or evidence of Lean elaboration.

No original plan, requirement, inventory or source file was edited. No
compiler/checker, project command, project hash helper, active artifact, cache,
ref/index/worktree or remote operation occurred. C1's sole validation ownership
remains with root, and this report makes no fresh liveness or terminal-status
claim. All implementation, connected checking, warnings, proof audit and
independent final review remain pending within the existing chapter workflow.
