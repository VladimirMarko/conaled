# Book/thesis union: scope reconciliation and source discrepancies

Prepared 2026-11-03 by `/root/union_scope_reconcile`. This is planning and
primary-source inspection, not a formal review, implementation, proof, or
acceptance decision. No repository source, ticket, coverage row, Git ref,
compiler output, or validation process was changed. Chapter 2 remains the
earliest unaccepted chapter. Later chapters must still receive their complete
item-level source inspection.

## Sources and extent

The governing scope is `requirements/REQUEST-union-v2.md`, supplementing the
preserved original request. Read the historical `book-source-inventory.md`
together with the later `book-full-inventory.md` and `book-thesis-union.md`;
the original inventory's missing-book-page statements are superseded evidence,
not current blockers.

The exact sources remain:

- Book, supplied Cambridge 2003 digital-print copy, 232 PDF pages:
  SHA256 `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
- Thesis, CMU-CS-96-177 (1996), 162 PDF pages:
  SHA256 `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.

Both use physical one-based PDF page = printed Arabic page + 12. Exact source
paths, attachment identity, retrieval URL and recovery policy remain in
`union-source-identities.json`. No manuscript or page image is added to this
note or its checkpoint.

This pass compared the existing complete navigation inventories, all current
supplemental rows, all sixteen forward contracts, the thesis contents, and
targeted thesis/book passages. The important code discrepancies below were
checked on rendered page images, including enlarged comparison operators.
Text extraction loses the equality stroke in some scanned `<=` operators;
it must not decide the comparison by itself. This is not an exhaustive
line-by-line comparison of all later chapters or Appendix A.

## Existing ownership remains sound

The coverage ledger contains all **83 book exercise headings**, all
**16 `T1.*` forward cost contracts**, and the existing supplemental families
`TU.A`, `TU.SEG`, `TU.DIG123`, `TU.SCHEDULE`, `TU.FORCE`, `TU.TRACE`,
`TU.MODULES`, `TU.BOOTVAR`, and `TU.A.4.PURE`. Headings are not the count of
exercise subparts, and these rows are not an exhaustive count of algorithms,
invariants or cost obligations. All sixteen forward contracts remain open.

The main chapter split should be retained:

| Thesis material | Book owner / local ticket | Detail to preserve |
| --- | --- | --- |
| Chapter 2, pp7-12 / PDF19-24 | Book4 / 10004, with 10014 and 10019 foundations | Demand and forcing behavior; neither values alone nor a generic thunk proves source timing. |
| Chapter 3, pp13-38 / PDF25-50 | Book5-6 / 10005-10006; trace foundation10017 | Classical analysis, its persistence failure, and persistent debit accounting are different obligations. |
| Chapter 4, pp39-48 / PDF51-60 | Book7 / 10007 | Real-time queue and mergesort scheduling. |
| Chapter 5, pp49-60 / PDF61-72 | Book8 / 10008 | Rebuilding and the earlier output-restricted-deque constructions. |
| Chapter 6, pp61-84 / PDF73-96 | Direct binomial heap material in Book3 / 10003; numerical material in Book9 / 10009 | The separate segmented-binomial sketch remains10016; do not close it with a book segmentation exercise alone. |
| Chapter 7, pp85-104 / PDF97-116 | Book10 / 10010 | Generic bootstrapping, uniform/nonuniform representations, and both extra queue variants remain explicit. |
| Chapter 8, pp105-126 / PDF117-138 | Numerical templates in Book9 / 10009 and10015; queues/deques in Book11 / 10011 | Scheduled digits are not identical to scheduled binomial heaps; the details below add comparison obligations. |
| Chapter 9, pp127-130 / PDF139-142 | Integration / 10012 | Historical claims, engineering discussion and open problems require classification, not invented solutions. |
| Thesis Appendix A, pp131-136 / PDF143-148 | 10014,10019,10020 and10012 integration | Distinct from book Appendix A, pp185-206 / PDF197-218. |

No change to the implementation frontier follows from this reconciliation.

## Verified source corrections to retain

### UNION-SRC-001: skew-list lookup/update boundary

**Sources:** thesis p78 / PDF90 (prose lookup) and p79 / PDF91
(Figure6.9, lookup and update); book p133 / PDF145 (prose lookup).
The printed recursive decision uses `i < w div 2`. The complete book
Figure9.7, p134 / PDF146, instead uses `i <= w div 2`; the Haskell listing
on p196 / PDF208 also uses `<=` for both operations. All these comparisons
were checked visually, including enlargements.

This difference is substantive. Consider the valid complete tree of weight3
with preorder contents `[a,b,c]`: root `a`, left leaf `b`, right leaf `c`.
Looking up index1 in the erroneous branch tests `1 < 1`, goes right, and
passes index `1-1-1 = -1` to the right leaf. The complete thesis listing then
raises its index exception instead of returning `b`. Its analogous update
branch fails at the same boundary. In a tree of weight `2*m+1`, index `m`
is the last left-subtree element, so the correct branch condition after the
root case is `i <= m` (equivalently `i-1 < m` on positive indices).

**Disposition:** record a source correction, not an alternative correct
algorithm. The Chapter9 realization should prove the intended preorder
contract using the corrected boundary and preserve a negative specialization
showing why the literal erroneous branch does not refine it. A silent
all-source-code correspondence claim would be false.

**Proposed owner:**10009, with10012 checking the Haskell correspondence.
Suggested detailed coverage row: `B9-SKEW-BOUNDARY-CORRECTION`, citing both
sources and distinguishing corrected full listings from the prose snippet.

### UNION-SRC-002: skew-list top-level update loses its weight wrapper

**Source:** thesis Figure6.9, p79 / PDF91, visually checked. The declared list
carrier consists of `(int * Tree)` pairs. Its successful top-level update
branch prepends the bare `updateTree` result to the unchanged list of pairs.
This does not have the declared representation type. Book Figure9.7,
p134 / PDF146, and Haskell p196 / PDF208 retain `(w, updatedTree)`.

**Disposition:** carry the cached weight into the rebuilt list cell, prove
that it still equals the unchanged tree size, and document the type correction.
This is not a second semantic realization that could be accepted literally.
The thesis's displayed `cons` also has an extra closing parenthesis on pp78-79;
that is a syntax correction and requires no invented mathematical theorem.

**Proposed owner:**10009, with10012 checking the appendix. This can be part
of the same source-correction row as UNION-SRC-001, but retain both reasons.

### UNION-SRC-003: simple catenable deque drops the surviving front element

**Sources:** thesis p118 / PDF130 and Figure8.4, p119 / PDF131. The complete
figure was visually checked. In the deep `tail` case, when the front has two
elements and the middle is empty, it returns only the rear deque. The book's
prose on p177 / PDF189 and complete Figure11.3 on p178 / PDF190 instead
prepend the remaining front element to the rear. The book figure was visually
checked. Its Haskell counterpart appears on p192 / PDF204.

With its intended sized primitive-deque interface supplied, there is a
reachable, valid counterexample using only public construction: catenate
shallow deques `[a,b]` and `[c,d]`. The source constructs a deep
deque with front `[a,b]`, empty middle and rear `[c,d]`. Its intended contents
are `[a,b,c,d]`. The literal thesis `tail` returns `[c,d]`, whereas the required
result is `[b,c,d]`. Thus validity alone does not repair the discrepancy.

**Disposition:** preserve `b` when collapsing the deep representation, and
record the symmetric `init` obligation. The corrected book rule supplies the
intended operation; do not assert that the literal erroneous thesis rule has
the same list semantics. Keep this boundary as a connected specialization.

**Proposed owner:**10011, suggested row `TU-SIMPLE-CAT-BOUNDARY-CORRECTION`;
10012 owns the appendix comparison.

## Additional realization details needing explicit later rows

### UNION-VAR-001: catenation thresholds differ

In the advanced implicit catenable deque, thesis Figure8.5 p122 / PDF134
uses `< 3` for the shallow/deep and deep/shallow catenation cases, whereas
book Figure11.4 p181 / PDF193 uses `< 4`. Both were visually checked. The
book Haskell code p193 / PDF205 follows `< 4`. The shallow/shallow split uses
`< 4` in both main-text versions.

At exactly three shallow elements, the thesis creates a new boundary segment
of size3 and suspends insertion of the old boundary into the recursive part;
the book appends those three elements to the existing boundary and leaves
that recursive component alone. The allocation, forcing and debit behavior
therefore differ even if the eventual element sequence agrees. Size3 is also
the dangerous boundary in the stated debit analysis (thesis pp121,124 /
PDF133,136; book pp182,184 / PDF194,196).

**Proposed owner:**10011, with a `TU-CAT-THRESHOLD` row and10012 appendix
comparison. Preserve both realizations or prove a suitable comparison and
their required cost premises. This inspection does **not** conclude that the
thesis threshold is incorrect or that its printed debit constant follows;
that mathematical check remains part of the chapter's detailed work.

### UNION-VAR-002: restricted implicit deques are distinct specializations

Thesis p115 / PDF127 explicitly describes both output-restricted and
input-restricted implicit deques: front digits have sizes1/2/3; rear digits
have sizes0/1 for the output-restricted case and1/2 for the input-restricted
case. These are not the earlier rebuilding-based restricted deques in
thesis p53 / PDF65 (Book8).

Book p172 / PDF184 gives the more general end-capability/digit table;
Exercise11.2 on p175 / PDF187 requests full deques. A checked general
construction could cover the restricted variants, but full-deque correctness
alone does not establish the smaller-buffer specializations or their resource
contracts. **Proposed owner:**10011; retain explicit specialization rows when
its complete ledger is opened. This is a clarification of the existing
chapter scope, not a demand to reproduce externally cited deque papers.

### UNION-PREMISE-001: primitive size access must be accounted for

The thesis `DEQUE` signature on p53 / PDF65 has no `size` entry, yet its
simple and advanced catenable functors use `D.size` on pp119,122-123 /
PDF131,134-135. Book Figure11.3 p178 / PDF190 avoids size access for the
simple version using a fixed number of empty/tail observations. The advanced
book functor explicitly adds a size-function assumption on p181 / PDF193;
Appendix A introduces a separate `Sized` class on p192 / PDF204.

**Proposed owners:**10011 and10012. State the necessary primitive capability
and its cost, or prove a bounded threshold observation from ordinary deque
operations. A whole-deque length traversal cannot be silently counted as
constant time. Retain the separation between operations, semantic laws and
cost assumptions; no shared library API change is proposed by this note.

## Remaining source-accounting cautions

- The sharper simple-catenation bound is
  `O(min(log n1, log n2))` in thesis p118 / PDF130 and book p177 / PDF189.
  Keep it in the detailed10011 specification; the introductory `T1.10`
  summary is not the strongest whole-chapter statement.
- Thesis §6.5 p82 / PDF94 discusses negative-size analogies, difference
  lists and a positive/negative heap sketch, then speculates about
  non-integral representations. These deserve an explicit contextual/sketch
  classification under10009. They do not silently import complete external
  papers or establish an approximation algorithm.
- The current ledger's `TU.A.4.PURE` row still names predecessor `ea8afa1`,
  while the corrected10019 candidate is `361f5f3`;10020 is a further
  cross-cutting consequence. Root should reconcile those evidence pointers
  without marking either candidate accepted or retroactively broadening the
  older review scope. This note does not change them.

All suggested rows are pending source-accounting work for their owners. No
new theorem, implementation, completed chapter, or accepted cost contract is
claimed here. The preserved review and exact-candidate gates remain unchanged.
