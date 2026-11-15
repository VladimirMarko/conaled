# Chapter 5 Exercise 5.9: reachable persistent counterexample families

Prepared 2026-11-03 by chapter05_failure_families. This is source and mathematical
preparation, not a Lean implementation, checked theorem, independent acceptance
review, or chapter-frontier advance. Chapter 2 remains earliest unaccepted.
Only this report was written; no compiler, Git, cache, process, resource, tracker
or coverage action was taken. The arguments below are proved on paper from the
printed recurrences and remain obligations for the eventual formal development.

## Source and interpretation

The user-supplied book is `research-pfds/source-assets/okasaki-book-2003.pdf`,
SHA256 `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
Printed page p is PDF page p+12. Exercise 5.9 is on p55. Relevant programs are
binomial heaps Fig3.4 p24, splay heaps Fig5.5 p50, and pairing heaps Fig5.6 p54;
their amortized claims are on pp45–46,49–53. The source's queue counterexample
and explanation are on pp54–55 and thesis §3.2 p19. I read the supplied Chapter5
text and Chapter3 binomial preparation/code, and visually checked book pp50,54,
55,198,199. The page images control comparison signs. No manuscript text is
reproduced here beyond necessary identifiers and mathematical formulas.

The primary cost interpretation is the chapter's strict, immutable source
execution with unit-cost primitive comparisons, cached-rank access/arithmetic
and constructor dispatch, refined by the explicit counters below. These are modeled source operations, not claims
about Lean allocation, compiler optimizations or arbitrary-cost comparison code.
Each selected counter gives a lower bound on any compatible positive unit-work
model, and the printed branches have a constant upper overhead per counted call
or link. Thus the stated asymptotic separations also hold for ordinary complete
source-work counts under those assumptions.

Construct the distinguished heap **once**, retain that version q, then evaluate
the indicated update on q separately m times. Every update receives the same q;
its output is not the next update's input. Its result may be retained or discarded
after strict evaluation. Reusing an already computed result m times is a
different program. The construction prefix is included in every bound below.
All chosen priorities are distinct within an input/result heap, so the examples
do not depend on tied-root policies or erase duplicate-occurrence semantics.

| Family | Construction and saved input | Repeated update | Total public operations | Actual work separation |
| --- | --- | --- | --- | --- |
| Binomial | n=2^k−1 ascending inserts, k≥1 | n separate `insert (n+1,q)` | 2n | Θ(n log(n+1)) versus claimed O(n) insertion sum |
| Splay | n ascending inserts 1,…,n | n separate `insert (0,q)` | 2n | Θ(n²) versus O(n log(n+2)) |
| Splay alternative | Same saved left spine | n separate `deleteMin q` | 2n | Θ(n²) versus O(n log(n+1)) |
| Pairing | Insert 0, then 1,…,n; n≥2 | n separate `deleteMin q` | 2n+1 | Θ(n²) versus O(n log(n+2)) |

The ephemeral theorems themselves remain valid: these branching workloads fail
their single-use trajectory premise. No bound is claimed for every persistent
workload; one unbounded family suffices to refute a universal extension.

## 1. Binomial insertion: repeatedly spend the same carry credits

Let B_j be the source heap obtained by sequential insertion of the distinct keys
1,…,j into empty. The ordinary binomial invariant gives increasing top ranks
at exactly the one bits of j. In particular B_n for n=2^k−1 has exactly one tree
of each rank 0,…,k−1. The existing Chapter3 preparation identifies the required
shape/size/carry lemmas; none is assumed already accepted by this note.

Inserting the fresh key n+1 creates a rank-0 singleton. `insTree` encounters a
tree of the same rank, links, and recurs on the tail. After i links the carry
has rank i and the remaining forest begins at rank i, until the rank-k carry
reaches the empty tail. Therefore there are exactly k calls to `link` and k+1
calls to `insTree`, including the terminating call. The output is a valid rank-k
tree with n+1 occurrences. Keys influence link roots, not this rank recurrence.

For a construction insertion j, let c_j be its number of links and b_j the
number of trees afterward. Then

`b_j + c_j = b_(j−1) + 1`.

Using the book's cost `c_j+1`, this gives the subtraction-free local identity

`(c_j+1) + b_j = b_(j−1) + 2`.

Starting with zero trees and telescoping the actual construction trajectory,
the n-insertion construction costs exactly `2n−k`. This is an independent
calculation from the counter, rather than use of the amortized upper bound we
are challenging outside its domain. An implementation should first prove the
balanced equality `buildCost + k = 2n`, avoiding truncated-subtraction issues.

Now perform m separate insertions into the unchanged B_n. Their total cost in
the same model is `m(k+1)`. With m=n, the complete workload costs

`T_k = 2n−k + n(k+1) = (k+3)n−k`.

It has Q_k=2n public operations and maximum heap size n+1. Since
`T_k / Q_k ≥ (k+1)/2`, no fixed constant bounds total work by Q_k for all k.
Here k=log2(n+1), giving Θ(n log(n+1)) work, although summing the claimed
constant insertion charges would give O(n). Construction cost is already paid
once; charging it again for every branch would conceal the failed premise.

Independent expected case: k=3, n=7. Construction costs `1+2+1+3+1+2+1=11`;
each independent eighth insertion costs4, with3links. Seven such insertions
give39 modeled steps over14public insertions. The final heap in each branch has
rank3 and8occurrences; the retained input still has ranks0,1,2 and7occurrences.

## 2. Splay heaps: cheaply construct a left spine, repeatedly traverse it

Define L_0=E and L_j=T(L_(j−1),j,E). Ascending insertion of1,…,n builds exactly
L_n. At step j>1, the old root j−1 is below the pivot j and has empty right child,
so the printed `partition` takes the immediate `(oldTree,E)` branch. The first
insertion also makes one partition call. Each insertion has constant actual
work; the whole construction has Θ(n) work. The tree is a valid ordered heap:
its inorder sequence is exactly1,…,n, with no right subtree or repeated key.

### Preferred insertion family

Partitioning L_n around0 always chooses the root-greater-than-pivot branch. For
n≥2 the left child's root is also greater, so the source follows its left-left
case and recurs on L_(n−2). Let P(n) count partition calls, including base calls:

`P(0)=1`, `P(1)=1`, `P(n)=1+P(n−2)` for n≥2.

Consequently `P(n)=floor(n/2)+1`. The number of priority comparisons is even
more direct: `K(0)=0`, `K(1)=1`, `K(n)=2+K(n−2)`, hence K(n)=n. Insertion adds
one root constructor after partition. Its contents are exactly0,…,n, and all
printed rotations preserve the ordered occurrence relation. Each invocation is
on the saved L_n, so no later invocation benefits from the previous rotations.

There are n repeated insertions. Construction makes n−1 key comparisons and the
repeated calls make n², giving exactly `n²+n−1` key comparisons for n≥1. The
whole strict source work is Θ(n²). In the book's partition-call convention plus
one unit per inserted root, the same workload has the explicit selected count
`2n + n(floor(n/2)+2)`; this is not equated with every other primitive count.

There are2n public operations, and all heaps have size≤n+1. Summing the chapter's
O(log size) amortized insertion envelope would therefore give at most
O(n(1+log(n+2))). The actual/claimed ratio grows on the order of n/log n. This
family uses the insertion bound discussed with Theorem5.2; it does not depend
on misclassifying the non-restructuring `findMin` query as logarithmic.

Independent expected case: n=4 yields left spine4,3,2,1. `partition 0` makes3
calls and4key comparisons, returns an empty lower part and an ordered upper
part containing1,…,4; `insert0` then adds the new root. Four independent inserts
make16comparisons after the construction's3, for19total.

### Alternative deletion family

On L_n, the printed `deleteMin` has two constant terminal cases: n=1 returns E;
n=2 returns the singleton2. For n≥3 it recurs on L_(n−2), then rebuilds the two
remaining nodes. Its invocation count therefore satisfies

`D(1)=D(2)=1`, `D(n)=1+D(n−2)` for n≥3,

so `D(n)=ceil(n/2)`. The number of new tree nodes is n−1: zero for n=1, one for
n=2, and two plus the recursive count otherwise. Every output contains exactly
2,…,n, while the saved L_n remains unchanged. Repeating deletion n times costs
Θ(n²), including the Θ(n) construction, over2n public operations. This defeats
the uniform extension of Exercise5.6's O(log n) amortized deletion bound.

`deleteMin` performs **zero priority comparisons**. Its linear work must be
observed through recursive calls, node construction or corresponding transition
work. A comparison-only measurement cannot establish this alternative. Repeated
`findMin` is also linear on L_n, but pp51–52 already deny a standalone logarithmic
amortized bound for that unchanging query; it is not the desired new failure.

Independent deletion case: L_4 requires2calls and3newnodes and returns
T(T(E,2,E),3,T(E,4,E)). Every repeated call has those same observations.

## 3. Pairing heaps: repeatedly delete the root of a wide star

Insert0 into empty, then insert the distinct positive keys1,…,n sequentially.
The saved heap is exactly

`Q_n = T(0,[T(n,[]),T(n−1,[]),…,T(1,[])])`.

For each positive insertion j, singleton-first `merge` compares j with0, retains
the existing minimum root and prepends the new singleton child. The construction
uses n+1 public insertions, n comparisons and Θ(n) complete work. Q_n is
well-formed: every child is nonempty, root0 is below every descendant, and the
contents are exactly0,…,n.

`deleteMin Q_n` invokes the literal two-pass `mergePairs` on n nonempty leaves.
For a list of h nonempty heaps, its recursive result is nonempty when h>0.
Each pair performs one nonempty/nonempty merge. Its outer merge performs one
more comparison exactly when a nonempty residual result remains. Thus, letting
C(h) count root comparisons,

`C(0)=C(1)=0`,
`C(h)=1+C(h−2)+(if h>2 then 1 else 0)` for h≥2,

and induction gives C(h)=h−1 for h≥1. The final outer merge with E in the even
case is a real call but contributes no root comparison. This is why simply
counting two comparisons per pair would be wrong. There are
`floor(h/2)+1` mergePairs invocations and `2 floor(h/2)` merge invocations;
complete work is Θ(h) under the declared source unit model.

Repeating `deleteMin Q_n` m=n times yields n(n−1) comparisons after the
construction's n, exactly n² in total. The workload has2n+1public operations,
maximum heap size n+1, and Θ(n²) total work. Even the chapter's weaker proved
O(log n) amortized envelope for insertion/merge/deletion would sum only to
O(n(1+log(n+2))). No conjectured stronger insertion or meld bound is needed.

Independent expected case: n=4 gives root0 with children4,3,2,1. First-pass
merges(4,3) and(2,1) each compare once; the latter's merge with E adds none;
the outer merge between their nonempty results compares once. Thus each deletion
has3comparisons. Four deletions plus four construction comparisons total16.
Every result contains exactly1,2,3,4 and has minimum1; the saved Q_4 retains0.

## Formalization obligations and union boundaries

Use the actual source algorithms and measured refinements developed in their
own chapters. Prove each reachable-family equation through their public
operation/correctness laws, then the observed recurrence and arithmetic bound.
Do not define a cost to be the desired asymptotic answer. Reuse conaled's
Measured/Workload composition for the construction prefix; the repeated branch
phase must explicitly preserve and select the saved version instead of feeding
each returned value into the next call. A small client with a saved heap and a
separate current result suffices; no universal graph executor is required solely
for these examples. The client can later connect to the persistent trace model.

Formal asymptotic rejection should retain quantifiers: there is no uniform C
bounding every workload in these families by the summed claimed envelope.
Using the subsequence n=2^k can reduce the splay/pairing separation to exponential
versus linear growth in k. Fixed small examples discriminate recurrences and
premises but do not prove that no asymptotic constant exists.

All empty operations retain source failures in the public heap interface. These
counterexamples simply satisfy the nonempty premises of every deletion. They
do not alter merge/findMin/isEmpty or replace the six-operation heap contract
with a set or deduplicating model. Distinct chosen keys are a specialization,
not a restriction imposed on general heap semantics. Integer comparison is
charged under the stated unit model, not assumed constant on every machine.

The AppendixA Haskell binomial `link` on p198 uses `≤`, matching the main SML
`Elem.leq`. Its `removeMinTree` on p198 uses `<`, and pairing `merge` on p199
uses `<`, unlike the corresponding non-strict main SML tests. Splay partition
uses the non-strict comparison in both. The present distinct-priority
families avoid those tie differences for their extensional shape/carry arguments.
This does **not** transport strict costs automatically to call-by-need. Haskell
cost claims require an explicit demand on each separately created result and
a proved account of actual sharing/forcing. For example, replicating one bound
update result is sharing that result rather than making n updates. Lazy
construction may also postpone subtree work. No Haskell runtime or full forcing
correspondence is claimed by this report.

The book's historical pairing-heap conjecture and empirical speed rankings are
not used. The thesis's p19 persistence explanation supports the common premise
failure, while its later memoized/debit machinery has separate obligations.
In particular, these examples do not contradict at-most-one forcing of a given
eligible memoized body: a saved immutable input is not automatically a cache of
every function application to that input. No existing foundation or whole-union
coverage row is discharged by this paper preparation.

## Visual source-reading correction, 2026-11-03

The initial report incorrectly grouped binomial `link` with the strict-comparison
variants. Reinspection of the existing 200dpi page images
`research-pfds/chapter05/book-p198-detail.png` and `book-p199-detail.png`,
individually at normal high detail, confirms `≤` for `link` on printed p198
(PDF210), `<` for `removeMinTree` on the same page, and `<` for pairing `merge`
on printed p199 (PDF211). These are pages of the exact book identified above.
This corrects our source reading; it is not an erratum in the book.

The initial report is preserved byte-for-byte as
`chapter05-persistent-counterexample-readiness-initial.md`, SHA256
`fea7d43b2446d297d4452a06712de740e18d870f2864605e31f1adabbeb0cbbc`.
Only the inaccurate comparison generalization and this provenance note changed.
All distinct-priority families, recurrences, expectations, construction costs,
asymptotic arguments and strict-versus-call-by-need boundaries remain unchanged.
