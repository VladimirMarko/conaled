# Alternating splitter and merge sorter: Exercise 2.5

Author handoff within the existing active FDSA-002 loop, 4 November 2026.
**Uncompiled source draft; no checked coverage or acceptance is claimed.**
The coordinator has not released a build in this worktree. This bounded task
is C02-104; all 112 Chapter 2 obligations and the unchanged frozen requirements
plus explicit scope reconciliation remain in force.

## Source identity, base and ownership

The actual Exercise 2.5 was read from the pinned July 27, 2026 book, printed
p.29 / PDF p.35. The PDF SHA-256 was independently verified as
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The exercise requests one traversal accumulating alternate elements onto two
piles, gives `halve [2,3,4] ([0],[1]) = ([4,2,0],[3,1])`, and specifies the
empty/singleton/recursive merge-sort equations. It asks for multiset preservation
and sortedness. It does not prescribe a numerical time formula or assert
stability of this alternating variant.

The relevant mergesort proof plan, value/API readiness, independent case
readiness and cost/source readiness were read, together with the requirements,
current C02-104 inventory row, reuse mapping and accepted sorting interfaces.
Their historical pending-Chapter-1 statements do not override the current
accepted state or active Chapter 2 authorization.

Worktree: `conaled-ch02-insertion`, repurposed onto
`work/fdsa-ch02-alternating`. The accepted chapter/full-spec review base remains
`07e480f6ec9958d4975bb90151005b84f2907614`. Before authoring, the coordinator
reconciled two reappearing insertion files against their preserved exact
development prefix and retained that prefix on this branch:
`95cfce304b9b63057286acc7d5b20b53d95d8eaa`. See
`provenance/chapter02-alternating-retained-prefix-20261104/reconciliation.json`.
Those unchanged files are not an additional accepted dependency of this sorter.

Only `Applications/Sorting/Alternating.lean` and
`Examples/AlternatingSorting.lean` are authored in the repository. The known
unrelated pinned-asset residual is preserved for coordinator reconciliation /
identity-checked checkpoint exclusion. No existing source, public root, tracker,
coverage, dependency, compiler or tooling file is edited. The separate quicksort
worktree is stopped and untouched.

## Actual execution and public observations

`halve xs (left,right)` is an ordinary structural list recursion:

```text
halve [] (left,right) = (left,right)
halve [x] (left,right) = (x::left,right)
halve (x::y::rest) (left,right) = halve rest (x::left,y::right)
```

The pair-consuming recursive call is in tail position. It traverses each input
element once and assembles the piles by cons, without calling `length`, `take`,
`drop`, append, reverse or a different splitter in its body. This is a concrete
exercise solution, not a claim that the book printed this exact worker code.

`halve_perm` states combined occurrence permutation against
`xs ++ left ++ right` for every accumulator pair and payload type. It composes
the actual recursive result with canonical `List.perm_middle`, append and cons
permutations; no element equality or order is assumed. `mem_halve` derives the
ordinary support observation from that occurrence statement.

`halve_lengths` states the exact two lengths:

```text
leftResult.length  = left.length  + (xs.length+1)/2
rightResult.length = right.length + xs.length/2.
```

`halve_balance` compares the increments above the original accumulator lengths.
Those increments differ by at most one, with the left increment at least the
right. It does not falsely claim that arbitrary unequal starting piles become
balanced. `halve_empty_balance` specializes the law to empty piles;
`halve_strict` proves both actual output lengths smaller than `xs.length` when
`2 ≤ xs.length`. The bases cannot be omitted: splitting a singleton leaves a
length-one child.

`sortAlternatingBy` has explicit empty and singleton bases. Its recursive body
binds the actual empty-accumulator `halve` result once, recursively sorts the
two returned fields, and calls canonical `List.merge` on those returned values.
The measure is input length, justified by `halve_strict`, not by sorting
correctness or a theorem about the returned sorted lengths. Public one-step
and two-element equations expose this execution.

Raw sorter permutation composes `List.merge_perm_append`, both recursive
permutations and `halve_perm`. Length and membership follow from permutation.
Key-sortedness reuses the accepted `merge_sorted_compatible_on` interface with
its key preorder and comparisons justified only on original input members.
Child permutations and the split occurrence invariant recover that membership.
The thin keyed operation requires only `LE` and `DecidableLE`; correctness adds
`Std.IsLinearPreorder`, without antisymmetry or any payload typeclass. A source
`LinearOrder` is therefore a supported specialization. No new comparison,
sorting, list or resource carrier is introduced.

## Independent expectations and connected cases

Before these additions, the accepted sorting APIs had no actual alternating
accumulator splitter or sorter to connect to Exercise 2.5. This is the exposed
implementation/theorem gap, not a claimed compiler failure. The following
expectations were fixed from the source equations and elementary list arithmetic
before their proof scripts were written:

- The printed nonempty-accumulator example returns `([4,2,0],[3,1])`. The
  source step equations prove the proposed value case, while the general
  length theorem gives lengths three and two.
- Empty-start input `[0,1,2,3]` returns `([2,0],[3,1])`, with lengths two and
  two. This checks alternating order on an even input rather than a contiguous
  split that merely has equal lengths.
- An arbitrary-accumulator multiset client consumes `halve_perm` through the
  standard quotient bridge. Empty and singleton cases retain arbitrary piles;
  the empty payload type is supported without choosing a default element.
- Initial piles `[3,2,1]` and `[]` with no remaining input retain lengths three
  and zero, exposing the distinction between balanced increments and balanced
  final piles. A universal client combines empty-start balance and strict
  decrease at the actual recursion threshold.
- The three-element sorter equation exposes the actual children `[c,a]` and
  `[b]` for input `[a,b,c]`. It would distinguish an order-preserving or
  contiguous split from this operation.
- Input `[2,1,2,3,0]` has independently expected sorted permutation
  `[0,1,2,2,3]`. Its proposed proof consumes both public correctness fields
  through ordinary sorted-permutation uniqueness. A generic multiset client
  and generic occurrence/length client retain arbitrary Boolean comparators.
- The existing accepted nonnegative-domain comparator witness supplies a
  concrete use of input-local sortedness without asserting global compatibility.
- For arbitrary first/middle/last payloads with keys `[1,0,1]`, the actual
  reversed piles give expected output middle/last/first. This case uses public
  step/base equations and the canonical merge equations; ordinary correctness
  alone would not establish this full-record value. The concrete tagged
  specialization proves failure of the existing `Stable` filter observation,
  rather than accidentally transporting another sorter's stability theorem.

## Statement review and current validation boundary

Source-level statement review checked arbitrary accumulators, occurrence rather
than set preservation, floor/ceiling orientation, increment versus final-size
balance, the `n ≥ 2` termination threshold, actual recursive child values,
comparator-law scope and arbitrary payload universes. No circular premise,
inhabitance assumption, payload order/equality decision or false stability
transfer is introduced. The length calculation is a value invariant, not an
execution-cost observation.

The two files have been read back. Their elaboration, connected proofs and
inferred public types still require the coordinator-released exact compiler.
There is no focused module result, full candidate check, exhaustive axiom audit,
independent Standards/Spec pass or immediate candidate verification for this
draft. All applicable integration gates remain mandatory, and the rest of
Chapter 2, including its cost/probability obligations, remains outstanding.

## Closed focused compiler continuation, 4 November 2026

The original 43242f43 draft is preserved. Root incorporated it without source
changes into the cumulative Chapter 2 development candidate, preserving all
original branches and the accepted chapter review base 07e480f. The bottom-up
compiler loop also checked the two alternating targets beginning with attempt2.
Two association corrections (9fe8660 and 0b76f0e) repaired the middle-permutation
steps and membership disjunction normalization. The example correction fdf6515
uses the public length theorem directly and removes a redundant simp argument.
Definitions, statement types, assumptions and independent expected values
remain unchanged. All failed attempts and exact proof patches are preserved.

Exact clean cumulative candidate 98696d86162bd93c1cba46719eeb65bf6cabe65a passed
all four bottom-up/alternating targets in attempt5, exit 0 in 17.481 seconds.
The public statement inspection passed, exit 0 in 38.091 seconds, checking 126
declarations, including all 39 alternating library/example declarations. Root
read those elaborated types against the complete source: arbitrary-accumulator
occurrence/length laws, strict child decrease, raw comparator generality,
input-local/key ordering premises, printed source/even/empty cases and the
explicit equal-key instability witness retain their intended contracts.

See provenance/chapter02-bottom-up-alternating-focused-summary.json and the
full attempt/type/native logs. Source/dependency/profile restrictions and one
Lean thread remain unchanged. This is focused implementation confirmation,
not an independent final review, full candidate audit or chapter acceptance.
