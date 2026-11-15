# Shared BinaryTree observations: independent client expectations

Recorded 2026-11-02. Contributor: `/root/tail_examples_preflight`; transcribed
by root from its completed read-only response. This is preparation for an
architecture decision, not a frozen implementation scope, checked Lean
examples, a final review or acceptance of Chapter 4 or any later chapter.

Use the existing Mathlib `BinaryTree` carrier. No new carrier, label order,
label equality, finiteness or inhabited-label premise is required by these
expectations. The mathematical fold below uses the argument order
`combine leftSummary label rightSummary`; it does not choose a final Lean API.

## Shared asymmetric fixture and ordinary folds

Let

```text
t = node 1 (node 0 nil nil) (node 3 (node 2 nil nil) nil).
```

There are four labelled nodes and the height is three. A fold with base 0
and combine `left + right + 1` must agree with the existing `numNodes`.
A fold with base 0 and combine `max left right + 1` must agree with the
existing `height`. A paired size/height fold can exercise the projection
fusion laws rather than computing both observations through separate APIs.

For arbitrary annotations, erasure is `BinaryTree.map Prod.fst`. Folding the
erased tree must equal folding the annotated tree while ignoring each
annotation in the combine callback. This unconditional identity includes
malformed annotations and does not imply cache validity.

If a bottom-up annotation construction is included in a later scope, its
distinct intended obligations are erasure back to the input, validity at
every node, and root-summary agreement with the original fold (using the
supplied base at `nil`). The presence of this possible client does not add
that construction to a frozen unit by itself.

## Ordering and empty labels

With base `[]` and combine `left ++ [label] ++ right`, the fixture gives
`[0,1,2,3]`. Preorder would give `[1,0,3,2]`. The asymmetric fixture detects
both confusing traversal orders and swapping child arguments. This is a
semantic sequencing check, not a claim that list concatenation costs a
constant amount under the source model.

Every `BinaryTree Empty` equals `nil`: the node case would supply an element
of `Empty`. Its size and height are zero, its inorder is empty, and a generic
fold returns the explicitly supplied base. Annotation/erasure therefore
need no invented label or inhabited-label premise.

## A malformed cache that passes two root-only checks

Use size summaries on the same fixture, with these annotations:

| Label | Stored size | Actual subtree size |
| --- | ---: | ---: |
| 1, root | 4 | 4 |
| 0 | 2 | 1 |
| 3 | 1 | 2 |
| 2 | 1 | 1 |

The root observation is correct and its local equation is also correct:
`4 = 2 + 1 + 1`. Nevertheless, the caches at labels 0 and 3 are invalid.
A smart constructor supplied with these malformed children can retain that
failure while producing a correct and locally consistent root. The example
refutes only root-level checks; correct local equations at every node, with
the fixed empty summary, imply full validity by structural induction.

## Hypothetical measured expectations

The following recurrences refer only to the explicitly chosen hypothetical
natural-number tariff. They do not assert literal book helper counts, Lean
runtime costs or target-machine costs without their execution/tariff bridges.

For a full fold, charge one at every empty or node call and add the actual
combine callback cost at each node, evaluated on its returned child summaries.
If n is the number of internal nodes and these actual callback costs are c_v,
then

```text
W_fold = 2*n + 1 + sum_v c_v.
```

There are n+1 empty calls and n node calls. If every executed callback costs
at most K, this yields `W_fold <= (K+2)*n+1`; the premise need only cover
executed callbacks, although a uniform callback contract would suffice.
For the fixture the bound is `4*K+9`; the empty tree costs one.

For a cached smart constructor, charge each of its two actual root-cache
reads by one, its constructor entry by one, and retain the actual combine
callback cost c. It does not traverse either child. Its exact local work is
`3+c`, bounded by `K+3` under `c<=K`. Its cache-correctness conclusion needs
valid children and the callback's value contract; its work bound only needs
the applicable callback-cost premise.

The source/API preflights decide whether either measured computation belongs
in the smallest shared unit. In particular, the retained leftist-heap source
uses zero cost for its auxiliary cached reader and smart constructor; these
positive-charge observations must not be substituted for that selective tariff.

## Evidence limits

The contributor read the existing carrier and independently checked these
expectations. No file writes, implementation, compiler, checker, project hash
helper, enumeration, Git/ref, cache or remote operation was performed by that
contributor. Root's transcription changes no formal source or chapter status.
