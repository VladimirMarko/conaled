# Thesis Chapter 6 source inventory (preparation only)

Prepared 2026-11-04 by `/root/native_setup`. This is a complete source-reading
inventory of thesis Chapter 6, not an implementation, statement review,
compiler result, proof, or acceptance decision. **Every semantic, invariant,
correspondence, termination, persistence and cost obligation below remains
unproved.** The local identifiers in this note organize source preparation;
they do not create or close tracker items. No chapter advances through this
record.

## 1. Source identity, inspection extent and ownership

The inspected source is Chris Okasaki, *Purely Functional Data Structures*,
CMU-CS-96-177, September 1996, at
`research-pfds/source-assets/okasaki-thesis-1996.pdf`. The actual local file
has 162 PDF pages, 628877 bytes, and SHA256:

`f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`

The hash was checked against the task's expected identity. Printed Arabic
page `p` corresponds to one-based PDF page `p + 12`. This pass read all of
printed pages 61-84 / PDF pages 73-96, including the opening examples,
sections 6.1-6.6, all ten figures, Definitions 6.1-6.3, Theorem 6.1, Lemma
6.2 and its proof, practitioner advice, discussion, footnote and related
work. There are no labeled exercises in these chapter pages.

The PDF skill was applied to this read-only manuscript inspection. Text was
extracted with `/usr/bin/pdftotext -layout`; `/usr/bin/pdftoppm` rendered all
24 pages to PNG, and every page was visually inspected. In particular, the
code, subscripts, inequalities, floor expressions and all diagram edges were
read from the page images. Text extraction damages these features and is not
the controlling evidence for a comparison operator. The renderer emitted
Type 3 glyph bounding-box warnings; the inspected pages remained legible.
Extraction and rendered pages are research intermediates under
`research-pfds/tmp/pdfs/thesis-chapter06-045/`, outside `session/`. They are
not manuscript content to add to the recovery payload.

Read together with these retained records:

- `book-thesis-union.md`: chapter crosswalk, `T1.12`, `T1.13`, and `TU.SEG`.
- `union-scope-reconciliation.md`: current ownership and the already recorded
  skew-list corrections `UNION-SRC-001` and `UNION-SRC-002`.
- `chapter03-union-inventory.md`: ordinary binomial source obligations and
  the separately owned Chapter 3 material.
- The binomial sections of `chapter03-binomial-redblack-readiness.md`:
  helper preconditions, tied-root observations, source/backend differences
  and the coupled meld-cost obligation.
- The chapter navigation in `book-full-inventory.md`. Its book inspection
  evidence is historical; this pass did not inspect a book PDF.

The book PDF is absent from this recovery. Book locations and owners below
are inherited crosswalk information, not a new book reading. This inventory
does **not** establish full book Chapter 9 coverage, its nineteen exercises,
or Haskell-appendix correspondence. Thesis Chapter 8's other numerical
templates and scheduling variants also remain separately owned.

| Thesis material | Existing owner | Boundary retained here |
| --- | --- | --- |
| Definition 6.2, binomial parts of Figures 6.2/6.3, heap signature and ordinary binomial implementation in section 6.2.2 | Book 3 / 10003 | Reconfirm the shared ordinary-binomial obligations, including the thesis's direct minimum scan. Do not reopen or move the existing Chapter 3 work. |
| Positional arithmetic, leaf trees/pennants, binary random-access lists, segmented numbers, canonical skew numbers and skew data structures | Book 9 / 10009 | Later numerical-representation work; ordinary binomial coverage does not discharge it. |
| Section 6.3.1's segmented binomial lists/heaps using real-time deques and bulk linking | Supplemental 10016 / `TU.SEG`, associated with Book 9 | This distinct thesis sketch is not closed by a book segmentation exercise or a generic number-system theorem. |
| Skew-list and skew-heap cost claims | `T1.12` and `T1.13` with Book 9 | Forward contracts remain unproved; the smaller index-sensitive list bound must also be retained. |
| Comparison with other book realizations and appendix code | Existing later chapter and integration owners | Requires the missing book source and implementation-level comparison; no fresh equivalence claim is made here. |

Thesis Chapter 6 is numerical representations. It must not be confused with
book Chapter 6's persistent amortization material.

## 2. Complete source-item and figure ledger

All rows below are source-accounting entries with unproved formal obligations.

| Local family | Printed pages | Content to retain |
| --- | --- | --- |
| `T6-INTRO` | 61-62 | Unary lists/naturals, tail/predecessor and append/addition analogy; size erasure and the conditions needed to transport arithmetic algorithms to containers. |
| `T6-POS` | 62 | Least-significant-first digits, fixed weights and allowed digit sets, represented value, ordinary bases, redundancy, exclusion of trailing zeros, dense/sparse encodings. |
| `T6-BINARY` | 63 | Dense binary increment/decrement/addition; sparse-by-weight carry/borrow/increment/decrement/addition. |
| `T6-TREES` | 64-65 | Three precise tree families, logical element counts, equal-rank link/unlink, rank-3 examples, constant local work under stated layout conditions. |
| `T6-BRAL` | 66-69 | Full random-access-list interface, dense binary leaf-tree representation, every helper/public operation, errors, path copying and logarithmic costs. |
| `T6-BIN` | 68, 70-73 | Fixed-order heap interface, ordinary binomial forest, full code, matching minimum observation/removal, logarithmic costs. |
| `T6-SEGNUM` | 72, 74 | Cascading carry/borrow examples; alternating blocks, normalizing pseudo-constructors, constant-step increment/decrement. |
| `T6-SEGCOLL` | 75-76 | Binomial bulk linking/unlinking, common deque representation, segment-root minimum invariant, list/heap operation claims. |
| `T6-SKEWNUM` | 76-77 | Weights `2^(i+1)-1`, canonical form, Theorem 6.1, sparse weight code, constant-step increment/decrement. |
| `T6-SKEWRAL` | 77-79 | Complete node-valued trees in preorder, root-only weights, full list code with explicit source corrections, constant end operations and index-sensitive access/update. |
| `T6-SKEWHEAP` | 80-83 | Auxiliary-element trees, Lemma 6.2, regular/skew links, normalization, all heap operations and worst-case bounds. |
| `T6-DISC` | 82 | Negative-length/negative-heap analogies and the explicitly speculative non-integral-number question. |
| `T6-RELATED` | 82, 84 | External numerical representations, random-access-list variants, finger access, binomial history and variable digit alphabets; contextual/cited-result classification. |

| Figure | Printed page | Required source/instance obligation |
| --- | --- | --- |
| 6.1 | 63 | Both binary-number implementations, including all helper domains and the actual nested addition/carry recursion. |
| 6.2(a-c) | 65 | Rank-3 leaf tree, binomial tree and pennant: each stores eight elements, but the leaf tree has fifteen structural nodes. Match all three shapes, not just their cardinalities. |
| 6.3(a-c) | 65 | Link two rank-`r` trees into rank `r+1` in each representation; preserve the depicted components and justify inverse decomposition, with base ranks treated explicitly. |
| 6.4 | 66 | Polymorphic random-access-list operations and distinct `EMPTY`/`INDEX` observations. |
| 6.5 | 67 | The sequence `[0,1,2,3,4,5,6]` split into leaf trees of weights 1, 2 and 4, with exact left-to-right leaf order. |
| 6.6 | 69 | Complete binary random-access-list listing, including empty and invalid-index cases omitted from some inline snippets. |
| 6.7 | 70 | `ORDERED` and `HEAP` signatures, fixed comparator identity across merge operands, and nonempty-operation errors. |
| 6.8 | 73 | Complete ordinary binomial heap; despite the page's running section heading, this figure belongs to section 6.2.2. |
| 6.9 | 79 | Complete skew random-access list, retaining the printed boundary/type/syntax defects as corrections rather than asserting literal executable equivalence. |
| 6.10 | 83 | Complete skew binomial heap; its position under a related-work running heading does not change its algorithmic ownership. |

## 3. Common semantic and resource obligations

Use an independent observation of represented contents. Lists require an
ordered sequence, with multiplicity; heaps require exact occurrences and
minimum observations, not just a set of priorities. Logical size counts
stored elements. It does not automatically count structural nodes, cached
metadata, allocated cells, or unique addresses in a shared persistent graph.

Each cached size/rank/block length needs an exact correctness predicate.
The source's `int` fields do not make negative sizes or arbitrary integers
valid. Likewise, its signed indices must preserve out-of-bounds behavior,
including negative input; replacing them silently by natural subtraction
can change an erroneous branch into a different result. A formal interface
may expose a valid-index type and a separate checked integer wrapper, but
the relationship to the source's failure observations still needs proof.

Specify comparator laws separately from the Boolean comparator field in an
SML signature. Root-minimum arguments need suitable totality/transitivity
and non-strict comparisons. Repeated occurrences and distinct payloads with
tied priorities remain legitimate. Heaps that can be merged use the same
element type and fixed order. The source's phrase about arbitrary tie
breaking does not erase the concrete code's choices or the requirement that
minimum observation and removal agree.

All operation bounds claimed in this chapter are worst-case bounds under a
declared abstract cost model. State charges for pattern matching, list/deque
access, constructor/path reconstruction, rank/size reads, comparisons and
integer operations. Unit-cost arithmetic on cached integers is a modeling
premise, not a proof about Lean's arbitrary-precision runtime or all machine
integer sizes. If nonconstant element comparisons or integer bit costs are
included, retain their contribution explicitly. The real-time-deque premise
in section 6.3.1 must itself support worst-case operations on persistent
versions; an amortized queue/deque premise would not establish the claim.

For a total finite-size statement, include constant overhead at size zero or
one. One useful target convention is
`L(n) = 1 + floor(log2(n+1))`; this note proves no bound using that function.
For meld/addition, fix the parameter to include both operands, or state the
two-operand bound before simplifying it. A maximum-rank argument, a bound on
the number of nonzero trees, and a dense digit-list length are different
facts and must not be interchanged.

Pure functional output laws should retain observations of old values after
updates. Any stronger copied-cell, fresh-allocation, or unchanged-address
claim needs an actual immutable-store interpretation. Naming an operation
path copying does not establish Lean runtime sharing. Source-aware costs
must be measured on the chosen operation and connected to its uninstrumented
result; equality of final values alone transports no cost bound.

## 4. Positional arithmetic and tree templates

### T6-INTRO / T6-POS: erasure and canonical digit meaning

Relate unary list length to the unary natural representation, including
empty/zero, cons/successor, nonempty tail/predecessor and append/addition.
The displayed append/addition recurse over the first argument, so their
linear-work statement needs that parameter. The introductory analogy is a
design principle with realization premises: an arithmetic operation of low
cost does not by itself provide ordering, minimum selection, indexed lookup,
or cheap tree restructuring for an arbitrary container. [pp61-62.]

Define the value of a finite digit sequence as `sum_i b_i * w_i`, where
index zero is least significant. Preserve the allowed digit sets, the
ordinary-base condition, and the absence of trailing high-order zeros.
Distinguish empty zero from noncanonical zero padding. Account for the
unary and ordinary binary cases and the redundant binary digit set
`{0,1,2}`. The three printed encodings of decimal 13, `1011`, `1201` and
`122`, are least-significant-first examples to connect to that value map.
The binary encoding of 73, `1001001`, gives weights 1, 8 and 64. [pp62,64.]

### T6-BINARY: both implementations and helper domains

For Figure 6.1's dense representation, prove normalization, numeric meaning
and termination of increment, decrement on positive input, and addition.
In particular, decrement of the singleton one yields empty, not a trailing
zero representation. Decrement of empty is not supplied by this arithmetic
listing; specify its partial domain or a separately identified checked
wrapper. Do not infer an `EMPTY` exception here from the later container
signature.

For sparse-by-weight numbers, every weight must be a positive power of two
and the list strictly increasing. The carry helper needs the incoming
power-of-two weight no greater than the first existing weight, if present;
only under that premise does its non-`<` branch justify an equal-weight
carry. Borrow needs a nonempty valid list and a target power-of-two weight
no greater than its first weight. Its doubling recursion then reaches that
weight while producing the lower weights. On arbitrary integers or an
oversized target, the printed helper is not an unrestricted terminating
subtraction algorithm. Establish value changes of `+w` and `-w`, then the
public increment/decrement cases at weight 1. [p63.]

The two additions must preserve the respective canonical forms and compute
the sum. Account for the actual nested `inc`/`carry` calls. Proving a
logarithmic depth and independently charging a logarithmic carry at every
level only gives a weaker product bound; a coupled count of consumed digits
and carries is needed for the source's logarithmic binary-addition claim.
Relate dense digits to sparse weights through a proved representation map,
without assuming identical traversal or allocation costs. [pp61-63.]

### T6-TREES: shapes, element counts and local links

Definitions 6.1-6.3 require separate carriers/validity predicates or checked
interpretations, with the following distinctions preserved. [pp64-65.]

- A complete binary leaf tree of rank zero is a leaf; a higher-rank tree
  has two equal-rank children one rank lower. Rank `r` gives `2^(r+1)-1`
  structural nodes but only `2^r` elements, all at leaves.
- A binomial tree of rank `r` has child ranks exactly `r-1,...,0` in the
  displayed ordinary representation. Prove equivalence with the equal-rank
  linking definition and derive `2^r` stored elements. This is the shared
  Chapter 3 family, not a new proof owner.
- A pennant is a singleton at rank zero; at positive rank `r` it has a
  root and one complete node-valued binary child of rank `r-1`. It therefore
  stores `1 + (2^r-1) = 2^r` elements.

For every Figure 6.3 link, require equal valid input ranks, identify the
actual retained components, and derive rank increment and occurrence
preservation. Unlink requires positive rank and returns two lower-rank
components. Pennant rank zero needs its own base case because the general
diagram contains subtrees labeled `r-1`. The local constant-work claim is
conditional on retaining the layout without a traversal that rearranges
elements. It is not a theorem that every such link preserves an arbitrary
list order or heap order without an appropriate realization. [p64.]

## 5. Binary random-access lists

### T6-BRAL-01: representation and observations

At digit position `r`, `One t` contains a valid complete binary leaf tree
of rank `r`; `Zero` contains no tree. The final digit, if any, is nonzero.
Every internal size field is the exact number of leaves and its children
have equal size. Abstract contents concatenate the trees' left-to-right
leaf sequences in digit order. This is a dense representation even though
the number of actual trees is the number of set bits. [pp66-69.]

Derive the forest's binary size equation, the bound of
`floor(log2(n+1))` on the number of trees, the separate dense-digit length
bound for nonempty input, and the maximum tree depth bound. Connect the
Figure 6.5 instance to exact contents `[0,1,2,3,4,5,6]`, not just size seven.

### T6-BRAL-02: carry, borrow and the public list operations

The size-computing link builds a node with the incoming tree on the left
and the old tree on the right. Its equal-rank precondition is supplied by
`insTree`'s current digit offset. Establish that insertion carries the new
prefix through the digits, preserves all invariants and implements `cons`.

Generalize `borrowTree` to an explicit starting rank. It returns a tree of
that rank containing the first block and a representation of the remainder.
The lone final `One` case removes the digit altogether. A nonfinal `One`
becomes `Zero`; a leading `Zero` recursively borrows a larger node, returns
its left subtree and reinstalls its right subtree as the lower digit.
The rank invariant must justify the node pattern in that recursive case.
At starting rank zero the returned tree is a leaf, which justifies the
printed `head` pattern. [pp67-69.]

Prove empty/isEmpty, cons/head/tail sequence laws and `EMPTY` behavior from
the complete Figure 6.6. The source head calls borrowTree and constructs
its residual result even though it projects only the element. Do not replace
that source recurrence silently with a different constant-head algorithm.

### T6-BRAL-03: indexed traversal and persistent replacement

Lookup skips zero digits and whole trees using their exact weights, then
uses the cached half-size to choose the correct leaf subtree. Here the
printed strict test `i < w div 2` is correct: internal nodes store no list
element. Do not apply the later skew-list correction to this leaf-tree code.
Prove lookup of every valid zero-based index and `INDEX` on every invalid
signed index, using the complete figure's leaf and empty-list error cases.

Update reconstructs the traversed forest prefix and root-to-leaf path,
retaining unchanged siblings, size fields and the suffix. Its observation
must replace exactly one sequence element, preserve length/shape/caches,
and preserve old-version observations. It must report `INDEX` rather than
invent a default element for an invalid index. [pp68-69.]

### T6-BRAL-04: actual worst-case work

Cons/head/tail perform bounded local work per visited digit. Lookup/update
first traverse a digit prefix and then one tree path; these are added phases,
not nested logarithmic traversals. Derive the source's logarithmic worst-case
bounds for all five operations, including path reconstruction for update and
borrow reconstruction for head/tail. Empty/isEmpty have direct constant
observations. These results are unproved and do not follow from the abstract
random-access-list signature alone. [p68.]

## 6. Ordinary binomial heaps: retain the Chapter 3 boundary

`T6-BIN` is the same ordinary-binomial source family already inventoried for
Chapter 3. The complete thesis listing has been re-read here so that this
complete chapter inventory does not omit it. [Definition 6.2, pp64-65;
section 6.2.2, pp68,70-73; Figures 6.7/6.8.]

Retain all of these unproved obligations and their existing owner:

1. Exact root-plus-descendant occurrences, recursively lawful heap order,
   correct cached ranks, descending child ranks and strictly increasing
   top ranks. Logical size is the sum of `2^rank` over the forest.
2. Equal-rank link, with the first root selected on a non-strict tie;
   `insTree` under its incoming-rank lower-bound condition; insertion of a
   singleton. The size `2^k-1` carry case must account for `k` actual links.
3. The literal `merge`/`insTree` recurrence, preserving exact occurrences
   and rank validity. A joint link/traversal accounting argument is required
   for the logarithmic bound, not independent logarithmic bounds multiplied.
4. Direct recursive `findMin`, plus `getMin`'s chosen tree and residual
   forest. The thesis implementation is the direct-minimum variant already
   associated with book Exercise 3.5. Matching tie choices give the required
   minimum-observation/removal agreement; a different backend's own minimum
   law is not automatically a literal source correspondence.
5. Delete the selected root occurrence, reverse the selected tree's
   decreasing-rank children, then meld them with the residual forest.
   Charge the reversal. A forest with one high-rank tree can still have
   many children to process, so forest-root count alone is insufficient.
6. Empty/isEmpty and the distinct failures of findMin/deleteMin on empty;
   singleton deletion succeeds with empty output. Insert, merge, findMin
   and deleteMin have the stated logarithmic worst-case targets, with total
   element count as the size parameter and both inputs included for merge.

The fixed-order signature on p70 is relevant to both ordinary and later skew
heaps. Do not weaken these contents laws to keyed replacement or assume that
all tied payloads are identical. The retained Chapter 3 readiness note already
describes concrete source/backend tie differences; this pass did not inspect
or change any dependency implementation. A proof of this section would not
prove binary random-access lists, segmented collections or skew binomial
heaps merely because they reuse ranks and links.

## 7. Segmented binary numbers and the separate bulk-link sketch

### T6-SEGNUM: normalized blocks and bounded recursion

Represent a binary string by alternating positive-length zero/one blocks,
with a final one block whenever nonempty. Relate expansion to the canonical
dense representation and to numeric value. Negative lengths, zero-length
stored blocks, adjacent equal block kinds and trailing zero blocks are
outside the valid domain. [pp72,74.]

The `zeros` and `ones` pseudo-constructors merge adjacent equal blocks,
drop an empty prefix, and additionally discard a high-order zero block.
Prove the numeric prefix laws and normalized output for nonnegative supplied
lengths and valid tails. The branch order in the printed equations handles
the overlap between a zero-length prefix and a matching first block.

Increment shrinks a leading zero block and introduces a one, or turns an
entire leading one block into zeros and increments the next block. The next
block is zero or absent, so the recursive call cannot propagate through a
second one block. Decrement on positive input has the dual bounded behavior;
its recursive call after a zero block reaches a one block because trailing
zeros are forbidden. Cover length-one blocks, block merging, empty after
decrementing one, and empty before increment. No zero-input decrement branch
is supplied. [p74.]

Prove the `+1`/`-1` meaning and preservation of validity on those domains.
Count a fixed number of block inspections, constructor operations and
integer operations, independent of the length encoded in the first block.
This is the source's worst-case constant-step claim under the integer model;
expanding the blocks into ordinary digits inside the implementation would
lose it. Retain the earlier `2^k-1` carry and `2^k` borrow contrasts. [pp72,74.]

### T6-SEGCOLL-01: common sequences and bulk restructuring

Section 6.3.1 supplies a construction sketch, not complete code. Its
unproved implementation and proof obligations remain `TU.SEG` / 10016.

The sequence for a contiguous one segment and the sequence of a binomial
node's children must use the same representation and compatible orientation.
Both need access to their smallest tree, and node decomposition needs access
to the largest child. The source therefore chooses real-time deques for
both, instead of the earlier increasing-list/decreasing-list pair. Prove
the required end operations, sequence observations and persistent worst-case
cost premises for that actual deque realization. [p75.]

A payload plus a segment of ranks `0,...,r-1` becomes a rank-`r` tree by
wrapping the entire sequence; decomposition returns the root and that
sequence. Its size relation is `1 + sum_(i<r) 2^i = 2^r`. Realizing this as
a loop of ordinary links or reversing a whole child list would not have the
claimed constant cost. Make all metadata and ownership of the retained
sequence explicit. The statement that only binomial trees support this
bulk behavior concerns the three displayed layouts, not every imaginable
representation of trees. [p75.]

### T6-SEGCOLL-02: list order and heap minima are separate obligations

For segmented binomial random-access lists, specify the actual traversal
that realizes the ordered list and prove cons/head/tail, lookup/update,
errors and persistence. The switch from leaf trees to binomial trees must
preserve the entire sequence through bulk link/unlink, not just cardinality.
Supply the missing normalizing helpers and their valid domains; no complete
second list listing is printed on pp75-76.

For segmented heaps, ordinary heap order is not enough. The smallest-ranked
tree in each segment must have a root no greater than all other roots in
that segment. Preserve the appropriate corresponding child-sequence
invariants recursively. To form a tree from a new element and a rank-zero-
starting segment, compare the new element with the first root only; promote
the smaller and place the larger in the rank-zero child. Prove that this
single comparison preserves the occurrences and all minimum invariants.

When adjoining a rank-`r` tree before a segment starting at rank `r+1`, the
source splits that first tree into two rank-`r` trees. Of the resulting three
rank-`r` trees, retain the one with the smallest root and link the other two
into rank `r+1`. Establish segment-minimum preservation relative to the
untouched remainder, not just minimum among those three. Specify consistent
tied choices, all boundary cases, and how every public heap operation restores
this invariant. [p75.]

### T6-SEGCOLL-03: complete the claimed cost transfers

The targets are constant worst-case list cons/head/tail and heap insertion;
logarithmic list lookup/update and heap merge/findMin/deleteMin. [pp75-76.]
They require actual algorithms beyond the sketch. In particular, a real-time
deque's end bounds do not supply arbitrary-index access, and the fact that a
number increments in constant work does not prove a heap's minimum repair
or full merge/deletion bound. Show how the number of relevant ranks, segments
and tree steps is bounded, charge every normalization phase, and connect
the costs to the selected source-faithful constructions. No book exercise
or ordinary binomial proof closes these missing obligations.

## 8. Canonical skew binary numbers

### T6-SKEWNUM-01: Theorem 6.1 and representation correspondence

The weights are `w_i = 2^(i+1)-1`, and digits belong to `{0,1,2}`.
Canonical form permits a digit 2 only at the lowest nonzero position, with
no high-order zero padding. Theorem 6.1 asserts existence and uniqueness
of such a representation for every natural number and attributes it to
Myers; the chapter does not give a separate proof. Construct and prove this
result, including zero, rather than assume a canonical encoder with its
desired laws. Retain the printed decimal-92 example `002101`. [p76.]

The concrete sparse list records the weight of every represented tree/digit
occurrence. Weights are valid skew weights in increasing order, except for
a possible equality between the first two; there are no other duplicates.
Relate this invariant to the canonical digit condition and numeric value
given by the sum of weights. Unrestricted sorted integer lists do not have
this meaning. The ordinary unannotated dense digit list would have to scan
for the first nonzero digit; the source's sparse choice supplies direct
access without such a scan. [pp76-77.]

### T6-SKEWNUM-02: actual increment/decrement and constant work

If the first two weights agree, increment replaces them by `1+w+w`;
otherwise it adds weight 1. The identity `1+2*w_i = w_(i+1)` explains the
former branch. The new weight may equal the following weight, but only as
the allowed leading duplicate. The shorter-list cases also add weight 1.
Prove numeric increment and canonical preservation for every branch.

Decrement removes a leading weight 1; otherwise it splits the first weight
into two copies of its half, rounded down. Validity and `w>1` justify a
positive lower skew weight, using `floor((2^(k+1)-1)/2) = 2^k-1`.
Require nonempty input, cover both singleton and duplicate cases, and prove
numeric decrement and canonical preservation. The printed arithmetic code
has no empty decrement case. Each operation performs a bounded number of
list and integer operations, yielding the stated worst-case constant target
in the declared unit model. [p77.]

No general skew-addition implementation is supplied here. The later heap
merge deliberately switches to ordinary binary-style rank normalization;
it is not evidence that the same sparse skew-number addition was implemented.

## 9. Skew binary random-access lists

### T6-SKEWRAL-01: shape, root-only weights and order

Each tree is a complete binary tree storing a value at every node, including
the root. Its rank-`r` size is `2^(r+1)-1`. Only each top-level tree has a
cached weight; recursive traversal passes the derived half-weight rather
than consulting nonexistent internal caches. The forest weights satisfy
the canonical sparse skew condition. Contents are left-to-right preorder
within a tree, then concatenation across trees. A leaf has weight 1; a node
has odd weight `2*m+1` and two weight-`m` children. [pp77-79.]

### T6-SKEWRAL-02: constant end operations

Cons checks at most two initial weights. Equal weights combine both trees
beneath the new root; otherwise a new leaf is prepended. Prove the sequence
prefix law and canonical validity, including the case in which the combined
weight equals the next existing weight. Head reads the first root. Tail
either removes a leaf or replaces a node with its two children, each assigned
the derived half-weight, in left-then-right order. Cover empty errors,
singleton exhaustion and restoration of the permitted leading duplicate.
These are the constant worst-case operations in `T1.12`. [pp78-79.]

### T6-SKEWRAL-03: corrected indexed access/update

First skip whole trees by exact weight. Inside a node, index zero selects
the root; positive indices `1,...,m` select the left child with index `i-1`,
and indices `m+1,...,2*m` select the right child with index `i-1-m`.
The required condition is therefore `i <= m` after the root case. The printed
strict condition is a source defect, documented in section 12 below.

Prove valid lookup and exact single-position replacement using the corrected
boundary, all `EMPTY`/`INDEX` observations appropriate to the public operation,
shape/weight preservation and retained old versions. The successful public
update must retain the pair `(w, updatedTree)`; the figure's bare-tree result
is a separate type defect. A corrected formalization must document these
repairs and prove the intended preorder specification, not assert equality
to the literal ill-typed/incorrect listing. [pp78-79.]

### T6-SKEWRAL-04: logarithmic and index-sensitive costs

Derive a logarithmic forest-length bound and logarithmic maximum tree depth
from valid weights and the single permitted duplication. Lookup/update
traverse one forest prefix and one tree path, with corresponding path-copy
work for update, so their phases give the `O(log n)` target in `T1.12`.

Also retain the stronger p78 claim `O(min(i, log n))`: each unsuccessful
step discards at least one preceding sequence element. For valid zero-based
index `i`, a total formal bound needs constant overhead, for example a
constant times `1 + min(i, floor(log2(n+1)))`. Prove both the index and
size bounds for the same measured recurrence before combining them. The
literal uncorrected program is not an implementation of this access contract.
The practitioner box's speed/preference claims are contextual advice, not
additional verified runtime rankings.

## 10. Skew binomial heaps

### T6-SKEWHEAP-01: actual size and Lemma 6.2

A tree retains the ordinary binomial child ranks `r-1,...,0`, but each node
of rank `r` also stores an auxiliary list of at most `r` elements. Count all
these auxiliary occurrences in the logical contents and size. Heap order
requires the root below its auxiliary elements and child roots, recursively
giving the required descendant minimum. Correct cached ranks, child shapes
and auxiliary-length bounds are separate invariant clauses. [p80.]

Lemma 6.2 states `2^r <= size(t) <= 2^(r+1)-1`. Formalize the printed
induction, including the empty sum and empty auxiliary list at rank zero:
the lower bound adds one root and the lower child bounds, while the upper
bound adds one root, at most `r` auxiliary elements, and the upper child
bounds. Derive that every rank-`r` tree is larger than any rank-`r-1` tree.
Do not strengthen this to a fixed size for a rank. [p80.]

The forest ranks increase except that its first two may agree. There is no
longer an exact skew-digit representation of its element count. Preserve
the p81 size-four examples: one size-four rank-2 tree; two size-two rank-1
trees; a size-three rank-1 tree with a singleton; or a size-two rank-1 tree
with two singletons. Their ranks/auxiliary contents differ while the total
size agrees. A logarithmic forest/rank bound must use Lemma 6.2 and rank
multiplicity, not a false fixed-weight equation. [pp80-81.]

### T6-SKEWHEAP-02: regular link, skew link and insertion

Regular link combines equal-rank valid trees, keeps the smaller root and
its auxiliary list, and adds the other entire tree as the new largest-rank
child. The retained auxiliary list still fits the increased rank. Skew link
first performs that regular link, then compares its root with one extra
element; it keeps the smaller root and prepends the other element to the
auxiliary list. Its length increases by one, so the old-rank bound must
justify the new-rank bound. Prove exact occurrences, heap order, ranks and
the concrete non-strict tie choices for both links. [p80.]

Insertion inspects at most two forest roots. If their ranks agree it uses
one skew link with the inserted element; otherwise it prepends a rank-zero
singleton. Prove preservation of the leading-duplicate condition, including
a possible equality between the newly combined rank and the next rank.
No whole-forest normalization is performed by this constant-time insertion.
Replacing it by an ordinary recursive carry would lose `T1.13`'s claim.
[pp81,83.]

### T6-SKEWHEAP-03: normalization, meld and minimum selection

`insTree` and `mergeTrees` use regular links, not skew links. They require
the same incoming-rank and strictly-increasing-forest conditions as the
ordinary binomial helpers. Removing the first tree from a valid skew forest
leaves a strictly increasing tail; this justifies `normalize` calling
`insTree` once on that tail. It can cascade, so it is logarithmic rather
than constant in general. Prove normalization preserves contents and heap
order while eliminating the leading duplicate. Then prove meld by first
normalizing both operands and using the actual `mergeTrees` recurrence.
[pp81,83.]

FindMin scans roots directly, unaffected by a possible rank duplication.
Prove root minimum over auxiliary elements and descendants, and the same
selected-root agreement with `getMin` used by deletion. Earlier tied roots
are selected by the printed non-strict recursive choice. All minima and
removals must retain exact occurrences, including equal-priority roots with
different auxiliary lists and subtrees. Empty calls raise `EMPTY`.

### T6-SKEWHEAP-04: deletion, auxiliary reinsertion and costs

Deleting the minimum first extracts its tree and residual forest, discards
only the selected root, reverses its descending children, normalizes the
residual forest, and merges those two increasing-rank forests. Finally it
reinserts every auxiliary element using the constant-time public insertion.
Account for the actual order of `insertAll`, all occurrences, size decreasing
by one, final validity, singleton exhaustion and empty failure. The source
calls `mergeTrees` after the necessary normalization; its children already
have distinct ranks. [pp81-83.]

The four deletion phases have additive logarithmic targets: find/extract,
reverse children, normalize/meld, and reinsert the auxiliary list. The last
phase uses `length(auxiliary) <= rank <= O(log n)` and constant insertion.
It would not follow by charging a logarithmic ordinary insertion per item.
The meld bound again needs coupled accounting across helper calls. With
Lemma 6.2's rank and forest bounds, establish `T1.13`: constant worst-case
insert, logarithmic worst-case merge/findMin/deleteMin. Empty/isEmpty have
their direct constant behavior. These exact primitive capabilities are also
relevant to later heap bootstrapping, but no generic bootstrapping result is
proved by this inventory. [pp82-83.]

## 11. Consolidated unproved cost obligations

The table records source targets, not accepted theorems. `n` counts logical
elements for containers and represented numeric magnitude for number
representations; addition/meld must state a combined or two-input parameter.
`L(n)` includes constant overhead as described in section 3.

| Family | Operations and target | Source |
| --- | --- | --- |
| Unary introduction | Increment/cons constant; displayed addition/append linear in the first operand's unary length | pp61-62 |
| Ordinary dense/sparse binary arithmetic | Increment, positive decrement and addition logarithmic in magnitude; actual carry/borrow chains retained | pp61-64,72 |
| Three tree templates | Equal-rank local link and positive-rank unlink constant under the stated layout/rearrangement condition | pp64-65 |
| Binary random-access list | Cons/head/tail/lookup/update `O(L(n))`, including actual borrow and path-copy work | p68 |
| Ordinary binomial heap | Insert/merge/findMin/deleteMin `O(L(n))`; helper coupling and reversal charged | pp71-73 |
| Segmented binary arithmetic | Increment and positive decrement constant in block operations under the integer-cost model | pp72,74 |
| Segmented binomial list | Cons/head/tail constant; lookup/update `O(L(n))`, conditional on the actual missing realization and real-time deques | pp75-76 / `TU.SEG` |
| Segmented binomial heap | Insert constant; merge/findMin/deleteMin `O(L(n))`, including segment-minimum maintenance | pp75-76 / `TU.SEG` |
| Canonical sparse skew arithmetic | Increment and positive decrement constant; no general skew-addition code supplied | pp76-77 |
| Skew binary random-access list | Cons/head/tail constant; lookup/update logarithmic, with `1+min(i,log2(n+1))` as the refined total-bound target on valid indices | pp78-79 / `T1.12` |
| Skew binomial heap | Insert constant; merge/findMin/deleteMin `O(L(n))`, including auxiliary reinsertion | pp80-83 / `T1.13` |

Constant empty/isEmpty behavior and observable failure paths must be included
in the actual implementation contracts. No amortized bound, measured elapsed
time, assumed interface law or focused example substitutes for the stated
worst-case source claim.

## 12. Source corrections and unresolved qualifications

### Reconfirmed UNION-SRC-001: skew-list boundary

The page images on printed pp78-79 visibly use `i < w div 2` in skew
lookupTree, and Figure 6.9 uses the same strict condition in updateTree.
This pass independently reconfirms the thesis side of the retained union
correction; it is not a newly discovered discrepancy or a new book check.

Here is a hand calculation from the printed equations, **not an executed
program or Lean-checked counterexample**. A valid tree of weight 3 has root
`a`, left leaf `b`, right leaf `c`, and preorder `[a,b,c]`. At index 1, the
literal test is `1 < 1`, so it takes the right branch and passes index
`1-1-1 = -1` to the right leaf. Figure 6.9 then raises `INDEX` instead of
returning `b`. Its updateTree fails at the same boundary. For a tree of weight
`2*m+1`, the left subtree occupies positions 1 through `m`; use `i <= m`
after the root case in the corrected intended algorithm. Retain a later
checked negative specialization of the literal branch and a correctness
proof for the corrected one.

The prior reconciliation records its separate book/Haskell comparisons.
Those sources were not present or re-inspected here. A fresh whole-book or
all-source-code equivalence claim would be unjustified.

### Reconfirmed UNION-SRC-002: missing weight wrapper and syntax

Figure 6.9 declares a list of `(weight, tree)` pairs, but its successful
public update branch prepends the bare updated tree to that list. The source
image confirms the missing pair. The intended repair retains
`(w, updatedTree)` and needs the unchanged-size/correct-cache proof. Treat it
as a type correction, not a second valid semantic realization.

The displayed cons on both p78 and p79 has an extra closing parenthesis
after the combined-tree list tail. Removing that unmatched parenthesis is
a syntax correction, not a new mathematical theorem. These three defects
must remain separately explained even if one source-correction coverage row
eventually groups them.

### Other domains and missing details

- Arithmetic decrement functions omit zero input; helper code assumes
  positive lengths, lawful weights, equal link ranks and ordered tails.
  Malformed raw values may fail to match or fail to terminate. Prove the
  intended valid domains instead of making unrestricted helper claims.
- The segmented collection section provides no complete data type or
  operation listing. Its traversal order, normalization and segment-minimum
  preservation must be supplied and reviewed before its costs can be proved.
- Skew-heap rank does not determine exact size, unlike the earlier binary
  templates; auxiliary elements are part of the contents and cost argument.
- Source logarithms suppress constant work at zero/singleton and index zero.
  Formal statements need explicit finite boundary conventions. The refined
  access bound is on valid nonnegative indices, not a bound with a negative
  integer inserted into a logarithm/minimum expression.
- The printed local structure equations and idealized integer arithmetic
  need a declared semantic/cost interpretation. No unrestricted runtime,
  overflow or physical-sharing claim is established by the prose.

These are future source-accounting obligations. They are not findings against
the current common integration candidate or evidence about its active gate.

## 13. Discussion, historical claims and external results

The opening arithmetic/container analogy and the practitioner comments on
pp76,78 are design motivation and empirical advice. Preserve that
classification; this inventory proves no speed ranking or universal
impossibility result for competing representations.

Section 6.5's negative-length examples concern difference-list-like
transformations and signed bookkeeping, not the natural-number length of
an ordinary finite list. Keep the displayed 15 plus negative 10 yielding 5
as an explanatory example with its semantic qualification. The two-heap
positive/negative-element discussion cites an external deletion scheme,
including deletion before insertion and negative net size. No complete
implementation or correctness theorem for that scheme is given here. Its
assumptions and cancellation semantics would need the cited construction if
reused. The question about non-integral/floating-point representations for
approximation is expressly speculative in this source, not a solved
algorithm or a claim about current research. The footnote credits Wadler
for the difference-list observation. [p82.]

Section 6.6 retains these external-result distinctions. [pp82,84.]

- AVL, Braun and leftist left-perfect leaf implementations are cited as
  random-access-list alternatives. Their quoted logarithmic access/update
  and logarithmic cons/tail bounds, including Braun's index-sensitive
  access, are cited comparisons rather than new local implementations.
- Myers's skew-number skip-pointer list has constant end operations,
  logarithmic lookup and linear-in-index update. The text says removing
  redundant pointers gives a structure isomorphic to the present skew
  list. This is a cited correspondence with missing external-definition
  premises, not a proved local isomorphism supplied by naming the structures.
- Kaplan-Tarjan deques and finger-search trees have the cited nearest-end
  or finger-distance random access. Preserve the distance
  `d = min(i, n-1-i)` and boundary/constant conventions if transporting
  such bounds. Their arbitrary-position insertion/deletion and the later
  Chapter 8 simplification are separate constructions.
- Vuillemin, Brown and King supply the binomial-heap history; Fagerberg's
  position-dependent digit alphabets permit cost tradeoffs between insertion/
  meld and deletion; Brodal-Okasaki is cited for an earlier skew-heap form.
  Historical attribution and an external tradeoff are not additional
  algorithms silently implemented in Figure 6.10.

No cited external paper was newly retrieved or read in this task. The chapter's
explicit local algorithm and theorem obligations remain as enumerated above;
external premises must be supplied if a later proof relies on those results.

## 14. Later checked specializations and stopping point

Useful future cases should instantiate the public general contracts rather
than merely restate expected values:

- Binary arithmetic: zero/one, digit gaps, all-ones carry and power-of-two
  borrow; reject overlarge helper weights and preserve no trailing zeros.
  Connect dense/sparse outputs through their value and normalization maps.
- Tree templates: ranks zero through three, all rank-3 diagram counts,
  equal-rank link/unlink and the pennant base case. Distinguish structural
  nodes from stored leaf elements.
- Binary lists: the full Figure 6.5 sequence, leading zeros, singleton
  borrow, indices at both sides of each half/tree boundary, negative and
  past-end indices, and retained old contents after a path-copy update.
- Ordinary heaps: the already owned Chapter 3 carry/meld cases, empty and
  singleton behavior, earlier tied roots with different descendants,
  and deletion of one high-rank tree with many children.
- Segmented numbers: zero, singleton and long blocks; pseudo-constructor
  zero lengths; merging adjacent blocks; carry/borrow crossing exactly one
  neighboring block. Measured work must not scale with the block's encoded
  length.
- Segmented collections: exact list order across bulk decomposition, both
  deque ends, and all three possible winners when a rank-`r+1` tree is
  split for segment-minimum repair. Include tied roots and untouched
  nonempty segments to test the full minimum invariant.
- Skew numbers/lists: empty, one, permitted first duplicate, a newly combined
  weight equal to the next weight, splitting a non-leaf head, and decimal
  92's canonical digits. Check the weight-3/index-1 negative source case,
  its corrected lookup/update, the retained weight pair, every preorder
  boundary, and the index-zero constant cost.
- Skew heaps: rank-zero auxiliary emptiness, the lower/upper size bounds,
  the four size-four distributions, cascading normalization of a leading
  duplicate, regular versus skew links, and deletion with a nonempty
  auxiliary list. Retain every auxiliary occurrence and test tied minimum
  roots with different child/auxiliary contents.

No example, theorem, compiler command or test implementing these cases was
written or run. No Lean/Lake, project source/ref, dependency/runtime,
controller, requirement/tracker, or GitHub mutation occurred. Root's active
validation process was not controlled. The only durable artifact authored
by this task is this inventory; root owns its checkpoint inclusion/upload.

The complete thesis Chapter 6 source-preparation pass is finished at the
stated extent. All formal obligations remain **unproved**, including Theorem
6.1, Lemma 6.2, `TU.SEG`, `T1.12` and `T1.13`. Book Chapter 9's complete
text/exercise/appendix comparison, actual implementations, exact-candidate
validation, independent reviews and acceptance remain future work in the
existing chapter order.
