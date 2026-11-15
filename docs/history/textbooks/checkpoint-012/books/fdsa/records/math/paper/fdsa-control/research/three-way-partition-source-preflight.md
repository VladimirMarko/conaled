# Shared three-way partition: source and cost preflight

Prepared 2026-11-02. **Read-only preparation, not implementation, validation,
chapter activation or either final review axis.** The governing whole-book
request and original chapter order remain unchanged. Root retains the sole
Chapter 1 compiler/checker run at candidate
`07e480f6ec9958d4975bb90151005b84f2907614`; no second compiler, Lake/checker,
project hash helper, ref/worktree/cache or remote mutation was performed.
Only this report was written.

## Conclusion and bounded scope

There is a concrete shared boundary for Chapter 2's three-way quicksort and
Chapter 3's selection: reuse the existing stable three-way partition values
and their independent filter/permutation/membership/length laws, and add an
actual single-pass measured realization of the companion source equation.
Preserve all existing Selection public names and consumers. A new sorting,
selection, comparison, probability or resource framework is unnecessary.

The one-pass source count is exactly `xs.length + 1`, including empty input.
It belongs to an execution that recursively partitions the tail once and then
conses the current head onto its selected bucket. The existing conaled
`Applications.Selection.partition3` uses two `List.partition` operations.
Its exact output equality is reusable semantic evidence, but supplies no
one-pass execution or source-cost theorem for that old implementation.

This supports all of C03-031 and B-018/019 after validation, and preserves the
shared semantics behind C03-011/013. It supplies only the partition component
of C02-102. Complete quicksort3, its recursive correctness, selection dispatch,
median-of-medians, randomized execution and their cost proofs remain later
chapter obligations. This shared preparation must not delay or widen the
existing initial Chapter 2 foundation prefix.

## Sources and exact identities

The following retained primary files were read directly. Ordinary byte hashes
were independently recomputed; these are provenance identities, not project
integrity-helper or compiler results.

| Primary source | Identity and inspected support |
| --- | --- |
| [FDSA official PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf), July 27, 2026 version | 1,742,029 bytes; SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. Exercise 2.3 and 2.4 on p.28; selection recurrence on pp.34–35; selector time composition on pp.40–41; Appendix B.1–B.2 on pp.347–348. |
| [Selection.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Selection.thy) | 47,922 bytes / 1,074 lines; SHA-256 `c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8`. `partition3` and `partition3_code` at lines301–309; length law at311–315; arbitrary-pivot recurrence at334–380; selected timing equation and exact count at638–641. |
| [Sorting.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorting.thy) | 14,846 bytes / 435 lines; SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. The two-filter quicksort equations and correctness are at327–339. This inspected file does not define quicksort3 or its source time. |
| [Time_Functions.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Library/Time_Functions.thy) | 3,432 bytes / 147 lines; SHA-256 `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`. Product projections have zero time; `T_filter_simps`/`T_filter` at81–87 expose callback time separately from traversal entries. |
| [Isabelle COPYRIGHT](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/COPYRIGHT) | 1,673 bytes; SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`; BSD-3-Clause. `Selection.thy` names Manuel Eberl, TU München. Preserve applicable notices when translating source. |

The companion revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
It is recorded separately from the manuscript version and is not claimed to
have generated that PDF. The PDF URL is mutable; the version and byte identity
pin the inspected manuscript. Retained research copies and extracted text are
not part of the source deliverable; keep these original summaries and recovery
URLs/identities instead of copying the manuscript into checkpoints.

An important provenance distinction is that the book prints the **three-filter
specification** in Exercise 2.3 and the **time recurrence** in Appendix B.2.
The exact single-tail-recursion implementation is explicitly supplied by
the companion's `partition3_code [code]`; it is not a separately displayed
Chapter 3 code block in the inspected manuscript text.

## Exact value and source execution correspondence

For pivot `p` and input `xs`, write `(ls, es, gs)` for the output. The semantic
specification is exactly:

```text
ls = xs.filter (fun y => y < p)
es = xs.filter (fun y => y = p)
gs = xs.filter (fun y => p < y).
```

These are ordered occurrence lists. Every bucket retains its input order and
multiplicity, including every pivot-equal occurrence. Concatenating the buckets
is a permutation of `xs`; it need not equal the original list. No set-only
observation can replace this contract.

The companion code equation has empty result `([], [], [])`. For `y :: ys`,
it recursively obtains the actual tail triple, then chooses:

| Selected branch | Returned triple |
| --- | --- |
| `y < p` | `(y :: ls, es, gs)` |
| Not less, and `p = y` | `(ls, y :: es, gs)` |
| Neither preceding condition | `(ls, es, y :: gs)` |

The second test in the companion is `p = y`; the existing Lean stable
partition predicate is `y = p`. Equality symmetry reconciles those tests;
this does not change the declared zero-comparison tariff. In a linear order,
the final branch is equivalent to `p < y`.

The recurrence traverses one tail and rebuilds one selected bucket at each
step. It is structural recursion with work after the recursive call, so a
single traversal is not a claim of tail recursion, constant stack use or a
particular compiled representation.

The proposed measured definition should consume the actual recursive result
through existing sequencing, for example this mathematical program shape:

```text
run p [] = tick (pure ([], [], []))
run p (y :: ys) =
  tick (bind (run p ys) (fun (ls, es, gs) =>
    pure (if y < p then (y :: ls, es, gs)
          else if p = y then (ls, y :: es, gs)
          else (ls, es, y :: gs))))
```

This is an uncompiled design equation, not a new implementation. It uses one
recursive call and its actual returned buckets. Defining the desired pair as
`(partition3 p xs, xs.length + 1)` would instead attach a proposed formula to
the old value function and omit the required source-execution argument.

Prove two independent contracts of the actual program:

```text
(run p xs).1 = sharedPartition3 p xs
(run p xs).2 = xs.length + 1.
```

The first can proceed by structural induction, using the existing exact
three-filter correspondence and the cons branch laws. A pure cons equation
for the extracted existing operation is useful without adding a second pure
partition implementation. The second follows from the actual empty/cons
cost recurrence. Semantic theorems then compose through the first projection;
their proofs do not establish the second projection.

## Domain, quantifier and termination boundaries

The source operation and the current conaled operation use a linear order on
payloads. Keeping this existing interface is coherent for the identified
clients; the minimal scope does not require a new generalized classifier.
The branch operation itself could be expressed using decidable less-than and
equality tests, but identifying the remaining branch with strict greater-than
needs appropriate order laws. Do not add a generalized contract merely to
avoid reusing the current concrete shared interface.

The value/filter/permutation/length correspondence and exact one-pass count
cover every finite list and every supplied pivot, including repeated values,
empty input and pivots outside the input. They require neither `Nodup` nor
pivot membership. No `Inhabited` payload instance, default pivot, finite
payload universe or payload measurability is needed. An actual pivot argument
is supplied; an uninhabited type does not authorize manufacturing one.

Pivot membership is a separate sufficient condition for both strict output
lengths to be smaller than the **full input** length. A supplied pivot in `xs`
makes the equal bucket nonempty. For an arbitrary outside-range pivot, one
strict bucket can be all of `xs`, so unconditional strict decrease is false.
Quicksort3 partitions the **tail** after removing its head pivot; its recursive
strict buckets are bounded by the tail length even when the tail has no equal
occurrence. Its termination argument therefore does not need to assert that
the pivot belongs to that tail.

The selection recurrence on pp.34–35 permits an arbitrary pivot for valid
rank `k < xs.length`. It is a semantic equation, distinct from termination.
The source returns the pivot directly in the middle branch, while conaled's
existing dispatch indexes the equal bucket. The middle branch ensures the
required equal occurrence exists; its bridge remains a Selection theorem.
Do not strengthen that semantic result with pivot membership or assert
`set es = {p}` for an arbitrary pivot when `es` can be empty.

Existing monotone selected-value transport does not imply that these three
buckets commute with every monotone label map. A noninjective monotone map can
turn `y < p` into equality, moving an occurrence from the lower bucket to the
equal bucket. For example, mapping both natural values zero and one to zero
changes their partition relation. No such bucket-map law belongs to this
minimal scope; stronger embedding assumptions would need a concrete client.

## Exact tariff and distinctions from quicksort

Appendix B.2 explicitly gives the base count one and a cons count equal to the
tail count plus one. The companion selects `partition3_code` in its `time_fun`
command before proving `T_partition3 x xs = length xs + 1`. Consequently:

- Every invocation, including the empty base, contributes one unit.
- Primitive comparisons, equality, tuple selection and cons constructors add
  no extra time under this declared source tariff.
- There is one traversed tail, not three independently executed filters or
  the current Lean operation's two stable partitions.
- Selecting the returned bucket does not add another recursive call or outer
  wrapper tick. A separate client may have its own entry charge.
- The result is a mathematical function-call observation. It does not count
  machine comparisons, equality implementation complexity, allocation, garbage
  collection, stack use or physical runtime.

The proposed use of `Resources.CallCount.tick` counts the actual recursive
entries, and ordinary `bind` preserves execution of the actual returned
buckets. There is no need for a time-function translator, syntax representation
or new observation framework.

The source metrics for the relevant algorithms remain distinct:

| Program/model | Required interpretation |
| --- | --- |
| Three-way value specification in Exercise 2.3 | Three ordered filters specify the result. That equation alone does not fix an implementation's traversal cost. |
| Existing Lean `Selection.partition3` | Two `List.partition` operations; exact value/filter laws exist. No measured execution count was found in this operation. |
| New source-faithful one-pass realization | One recursive pass; exact call count `n+1`. Its value theorem connects to the shared operation. |
| Two-way quicksort, Exercise 2.4 | Two full filters on a tail of length `m`, each with unit callback charge and traversal count `2*m+1`, plus the current-call charge and the two recursive costs. |

For the last row, the nonrecursive contribution is `4*m+3`; its empty
quicksort call costs one, and a singleton therefore costs five in the supplied
metric. The recurrence deliberately omits append traversal. The exact sorted
input/global-upper target remains `2*n^2+2*n+1`. Replacing those two filters by
the new one-pass partition would change the execution and its tariff even if
the resulting selected sublists were equivalent in an appropriate domain.
This shared unit supplies no replacement proof of C02-103 or C02-024.

## Existing local interfaces read

The existing Selection partition fragment was read directly, together with
the actual resource definitions in the Chapter 1 repair worktree. Ordinary
identities of those local files are:

| File | SHA-256 |
| --- | --- |
| `Applications/Selection/ThreeWay.lean` | `bd72ca5f11d028cde9420ae42f9a9f1f84d6cfc00bf02bd528a61fd00f586d52` |
| `Applications/Resources/Measured.lean` | `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| `Applications/Resources/CallCount.lean` | `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |

The independent fragment contains `partition3`, `partition3_eq_filters`,
`partition3_perm`, the three membership iff lemmas, `partition_lengths` and
`partition_strict_sizes`. Their output product association is
`List α × (List α × List α)`, observed through `.1`, `.2.1`, `.2.2`.
Preserve that shape and the existing Selection-facing names. The architecture
preflight owns the precise new namespace/path and adapter decision.

`sorted_partition`, `dispatch`, `dispatch_value`, pivot policies and selector
correctness use Selection's ordered/rank interface. They should consume the
shared partition facts instead of making the shared value module import the
whole selector. Pure shared operations must not import resource or Examples
modules. Extracting the stable value fragment should retain its actual two-pass
definition; the new single-pass execution has its own explicit measured name.

`Resources.Measured` is an ordinary value/cost pair with independent universes;
`pure` contributes zero and `bind` consumes the actual value before adding the
next observation. `CallCount.tick` adds one to natural cost. These interfaces
already express the proposed realization and its source count exactly.

## Coverage and retained obligations

| Original obligation | Contribution of the proposed shared unit |
| --- | --- |
| C02-102 | Shared exact partition values and occurrence/order facts only; complete quicksort3 recursion, termination, sortedness and multiset preservation remain Chapter 2. |
| C03-011 | Preserve/expose existing three-filter, permutation, total-length and membership laws as shared facts. |
| C03-013 | Preserve the existing pivot-membership-qualified strict-size theorem; do not infer termination for arbitrary outside pivots. |
| C03-031 | Actual one-pass source realization, its value bridge, defining count recurrence and exact `n+1` result. |
| B-018/019 | The same actual recurrence and exact count, with Appendix B's zero-primitive/one-entry convention explicit. |
| C03-012 and later selection algorithms | Useful dependencies only. Rank/equal-block dispatch bridges, actual selector recursion and all further bounds remain separate. |

The source/implementation distinction is already retained in the original
chapter inventories, `chapter02-reuse-plan.md`, `selection-proof-plan.md`,
`random-pivot-api-preflight.md` and `appendix-b-obligations.md`. This report
confirms and sharpens the exact provenance; it does not replace those records,
change any frozen requirements or add a mandatory extra theory/algorithm.

Remaining implementation risks are ordinary proof work: transporting exact
tuple components through the recursive value bridge; simplifying equality
orientation and the final strict-order branch; preserving old public names,
imports and clients during extraction; and checking that examples exercise
general laws with duplicates, absent pivots and empty boundaries. All future
compiler/audit and independent review gates remain unchanged. No source
preflight or saved draft can close a chapter or shared unit.
