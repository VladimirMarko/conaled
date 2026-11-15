# Shared binary-tree shape bounds

Historical checkpoint and local-ticket references in this account resolve through
the [preserved FDSA records](../history/textbooks/checkpoint-012/books/fdsa/README.md).
Current coverage and follow-up belong to [#558](https://github.com/VladimirMarko/conaled/issues/558);
old process and tracking instructions describe the producing session.

## Receiving continuation — 5 November 2026

This unit is received against accepted Chapters 1–3 and XT01 at
`90469ce4ba3fc49397d369a5db7d58aec7014f58`, durable in checkpoint0138.
The original unit base remains `64c6b777d828ecfe83234fc2aed94600a1f24297`
and original donor remains `974a97321a8ec174b56104c7e6efaaca881b6639`.
The three formal modules are initially copied byte-for-byte from that donor.
The accepted public root and reconstruction map are preserved, with only this
unit's new import and source section added. The original XT02-SP01 wording
correction and all five requirement groups remain in the same full review loop.

The source assessment below describes the original drafting stage. Current
focused/type/full/audit/review/immediate-verification results are recorded
separately in `fdsa-control`; reception alone grants no validation or chapter
acceptance. Every later algorithm, representation and runtime obligation remains.

## Status and source boundary

This is the implementation-side source and statement assessment of the
FDSA-XT02 draft. The natural and real theorem families and their connected
uses have been written. **No compiler, complete candidate gate, exhaustive
audit or independent final review has run for this unit.** Accepted repaired
Chapter 1 and the preceding shared tree-cache unit remain prerequisites to
integration and acceptance. These files close no chapter or appendix ticket.

The source is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, July 27, 2026, especially Chapter 4, pp. 47–48 and 51–53. Later
consumers include Braun height bounds in Chapter 11, pp. 128–130, and the
minimum-height bound used by leftist heaps in Chapter 15, pp. 183–186.
The [official manuscript](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`;
it is a research input and is not redistributed here.

Supporting Isabelle theories `src/HOL/Library/Tree.thy` and `Tree_Real.thy`
were inspected at `f86f290225eebcc52c1ae7dba2e098f405f51c21`. They identify
Tobias Nipkow as author; the pinned source inventory retains their exact
hashes and BSD-3-Clause provenance. That revision postdates the manuscript
and is not claimed to be its build revision. The Lean proofs below use the
existing Mathlib carrier and arithmetic interfaces at
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The fixed initial base for this bounded unit is the saved, unvalidated XT01
draft `64c6b777d828ecfe83234fc2aed94600a1f24297`. Exact frozen requirements,
candidate history and independent review/validation records are retained in
the local checkpoint's `fdsa-control` directory. The initial requirements
SHA-256 is `50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91`.

## Ordinary observations and conventions

`Applications.Trees.Shape` reuses `BinaryTree`, its existing `numNodes`,
`numLeaves` and `height`, and XT01's ordinary fold. The only new numeric
observation is `Trees.minHeight`: fold zero at nil and `min left right + 1`
at a node. Its meaning is distance to the nearest external empty leaf.
The empty tree therefore has zero nodes, one leaf and both heights zero;
a singleton has both heights one. The general leaf identity remains the
existing `numLeaves = numNodes + 1`.

`Complete` is an independent recursive predicate: nil is complete, and a node
is complete exactly when both children are complete and have equal maximum
heights. This is the perfect-tree convention. The theorem
`complete_iff_minHeight_eq_height` connects that recursion to the equal-depth
interpretation. Completeness has not been defined by the numerical answer of
one of the later leaf-count theorems.

`AlmostComplete t` means `t.height <= minHeight t + 1`, with an explicit
equivalence to the source's natural-subtraction expression. It permits one or
two adjacent external-leaf levels. It imposes no left-to-right filling rule.
Completeness implies almost completeness, and the latter passes to each
immediate child. The arbitrary-subtree relation and executable source checker
are still separate Chapter 4 work.

Payload types are arbitrary. Map preservation works across independent
universes and needs no injectivity, order, equality decision or default label.
Neither a tree nor its payload type is assumed nonempty. The existing
`BinaryTree Empty` case is retained through the public nil laws.

## Sharp power bounds and logarithms

Writing `m`, `h` and `L` for minimum height, maximum height and external-leaf
count, structural induction supplies

\[
2^m\le L\le2^h.
\]

At a node, both child counts are bounded using the smaller child minimum
height or the larger child maximum height, respectively. Existing natural
power monotonicity justifies that step, and the successor power is twice the
preceding power. There is no enumeration premise or new arithmetic framework.

The complete case attains both bounds. For the strict upper induction, unequal
child maximum heights make one summand strict; equal heights force an
incomplete child. The strict lower induction splits minimum child heights.
In its equal-height case, two complete children would also have equal maximum
heights, contradicting parent incompleteness. Both equality converses then
follow from the strict bounds:

\[
\operatorname{Complete}(t)
\iff L=2^h
\iff L=2^m.
\]

The natural logarithms are the existing `Nat.log` and `Nat.clog`. Their power
adjunctions give the universal inequalities `m <= log 2 L` and
`clog 2 L <= h`. On an almost-complete tree these become equalities. If the
tree is complete, use the logarithm of a power. Otherwise almost completeness
forces `h=m+1`, and both strict capacity bounds determine the two rounded
logarithms. This route includes `L=1`; it does not use a predecessor inequality
that would fail at height zero.

`height_optimal` compares `s : BinaryTree alpha` and `t : BinaryTree beta`
with independent payload universes. Its premises are almost completeness of
`s` and `s.numNodes <= t.numNodes`; its conclusion is `s.height <= t.height`.
The second tree has no shape invariant. The proof converts the count comparison
to leaves, applies the second tree's capacity bound, and uses the ceiling-log
formula for `s`. It neither constructs trees of arbitrary size nor claims a
converse or strict height comparison.

`Applications.Trees.ShapeLog` keeps real analysis separate. It lifts the four
discrete inequalities through the corresponding `Real.logb`/real-power
equivalences, using the actual positive leaf count and base two greater than
one. The complete real equality follows from the resulting sandwich and
minimum/maximum-height equality. The almost-complete natural floor and ceiling
corollaries consume `Real.natFloor_logb_natCast` and
`Real.natCeil_logb_natCast`. These are actual real statements, including the
empty tree, without a floating-point approximation or a replacement logarithm.

## Source correspondence

| Common source obligations | Draft connection |
| --- | --- |
| C04-009, C04-011 | `minHeight`, its constructor equations and `minHeight_le_height`; the existing `height_le_numNodes` already covers C04-010. |
| C04-012–013 | `pow_minHeight_le_numLeaves`, `numLeaves_le_pow_height`. |
| Recursive mathematical part of C04-031, C04-032 | `Complete`, `complete_node`, `complete_iff_minHeight_eq_height`; the executable checker remains open. |
| C04-033–036 | Complete equalities, both strict incomplete bounds, and both equality characterizations. |
| C04-037 and the supporting real strict/sandwich results | `height_eq_logb_numLeaves`, `minHeight_le_logb_numLeaves`, `logb_numLeaves_le_height` and strict variants. |
| C04-042–045 | `AlmostComplete`, `almostComplete_iff_sub`, `height_optimal`, exact natural log/clog and real floor/ceiling formulas. |
| Immediate-child portion of C04-046 | `complete_almostComplete`, `almostComplete_children`; the general subtree result remains open. |
| Common mathematics later used by C11-014–018 | Almost-complete shape/logarithm/optimum results. The constructor arithmetic, Braun/weight-balance invariant bridges and array operations remain separate. |
| Common shape bound used by C15-006 | Universal minimum-height power/log bounds. Existing leftist `rank_paths`, `rank_size` and `rank_log` remain intact; cache/representation and actual merge-cost bridges remain separate. |

This table describes intended source connections in an uncompiled shared
draft. It does not mark any inventory row accepted or replace a whole chapter's
coverage review.

## Connected uses and independent expectations

The cases in `Examples.TreeShape` were selected before source edits from
hand calculations. Existing definitions could already compute some numbers;
the missing connections were the shared structural and logarithm results.
No compiler failure was manufactured or reported during this drafting stage.

| Case | Intended connection and independently expected result |
| --- | --- |
| Empty payload type and singleton | Existing `empty_tree`, new nil laws and completeness/height equivalence. Empty gives leaves one and heights/logs zero; singleton gives heights one. |
| Complete three-node tree | The upper equality converse establishes completeness; the minimum equality and real height identity then follow through public results. Leaves four, both heights two. |
| Two-node right chain | Public strict capacities and real strict bounds hold, yet both rounded bounds are equalities. Leaves three, minimum one, height two. Child closure and subtraction equivalence are also used. |
| Saved XT01 asymmetric sample | The actual four-node tree has leaves five, minimum two and height three. Its almost completeness gives natural and real rounded logarithms. A separate proposition rejects replacing `numNodes + 1` with `numNodes`. |
| Label maps and actual pair annotation | Arbitrary map laws preserve minimum height and completeness predicates. The saved pair-summary sample uses its actual erasure theorem, without requiring cache validity for shape. |
| Saved corrupt size annotations | Their erasure still gives the same almost-complete shape with minimum two, while the existing all-node size validity predicate fails. Shape preservation is independent of stored-value correctness. |
| Actual minimum-height cache | `min_reader` specializes `Cached.read_eq_fold` and map preservation. `minSample` is produced by the existing `annotate`; its validity and erasure establish that the actual root reader returns two. |
| Three-node chain | Four leaves form a power of two, but the minimum-bound completeness characterization rejects completeness. The arbitrary exponent alone is insufficient. |
| Boolean-labelled optimum counterexample | A root with nil left child and a complete three-node right child has four nodes, five leaves, minimum one and height three. The public optimum compares it with the natural-labelled sample and proves it optimal against every competitor with at least four nodes, although it is not almost complete. |
| Recursive local-height-balance counterexample | A private example predicate holds at every node of the independent seven-node fixture. Leaves eight, minimum two, height four; almost completeness fails. This is not an AVL implementation or invariant bridge. |
| Arbitrary saved left chains | The general natural rounded inequalities apply without an almost-complete premise. They do not become equalities on every skew tree. |

## Statement assessment and remaining gates

The implementation-side reading checked the recursive source meanings,
independent universes, quantifier order, leaf-versus-node count, empty boundary,
both directions of each equality characterization, strict-versus-rounded
claims, and actual use of public results in the compositions. The optimality
witness uses two different inhabited label types; no vacuous positive-size
existence assertion over `Empty` is substituted for that use.

Bounded independent source/API readings found no concrete issue in the stable
natural core or real bridge. The independent client reading caught one
docstring that incorrectly described recursive cache validity as necessary
for root correctness. The theorem already states sufficiency; the wording is
corrected and the finding retained. An invalid descendant can coexist with an
accidentally correct root observation. Additional source/client assessments and
exact file identities are retained with the immutable candidate handoff. These are
source readings only. Elaboration, simplifier behavior, matching candidate
build/guards, exhaustive audit, both independent final review axes and immediate
candidate verification remain required. No informal note is a proof dependency.

The public root imports `Examples.TreeShape`, which imports both new domain
modules. The core adds no resource executor, generic tree class or alternate
carrier. It claims no lookup/merge runtime, physical sharing or storage bound.
Boolean checking, arbitrary subtrees, complete/almost-complete constructor
exercises, weight balance, Braun operations and leftist representation/cost
bridges remain mandatory later book obligations.
