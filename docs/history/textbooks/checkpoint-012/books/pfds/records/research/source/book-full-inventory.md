# Uploaded PFDS book: source inventory and Chapter 2 obligations

Inspected 2026-11-02 by `/root/book_inventory`. This is a source/accounting
report, not a proof-completion or chapter-acceptance decision. No repository
source, requirement, ticket, index, or branch was changed by this inspection.

## Source identity and pagination

User-provided Cambridge book, Chris Okasaki, *Purely Functional Data Structures*.
The visually inspected copyright page (physical PDF page 6) states first
publication in 1998, first paperback edition in 1999, and transfer to digital
printing in 2003; ISBNs 0521631246 and 0521663504. This agrees with the previously
inspected publisher frontmatter. PDF metadata is secondary: it names Okasaki
and identifies an ABBYY FineReader scan; it is not used as proof of edition.

- Source SHA-256: `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
- Size: 9,356,709 bytes; physical PDF page count: 232.
- Approved attached source identity: `libfile_330c4ca848c881919fd79d1f521ddd08`.
- Current source path: `research-pfds/source-assets/okasaki-book-2003.pdf`.
- Numbered main page `p` is physical PDF page `p + 12` (one-based), hence
  zero-based PyMuPDF index `p + 11`. Main text runs through printed page 220.
- Physical pages 7–9 contain the detailed contents (printed v–vii); the preface
  is physical pages 11–12 (printed ix–x). The PDF bookmark for the preface
  incorrectly points to physical page 7, so bookmarks must not replace inspection.

The existing OCR layer is useful for finding headings, but it sometimes loses
page numbers or punctuation (for example Exercise 2.3 appears as `23`, and
printed 77/147/177 can be misread as 11/141/111). Scanned page images are primary.
All Chapter 1 and Chapter 2 pages, the publication page, and the three-page TOC
were rendered and visually inspected. Temporary renders are under
`research-pfds/full-book-render/pdf-NNN.png` with physical one-based numbers.
The source PDF and render/OCR derivatives remain outside repository/checkpoint
payloads under the project's manuscript-exclusion policy. Durable source
identities and inspection notes suffice to identify the user attachment again.

## Source-completeness result

**The previous printed-page-6 source blocker is resolved.** Physical PDF page
18 was rendered and visually inspected: it is blank. Chapter 1 therefore
contains printed pages 1–5 of prose followed by a blank page 6. All Chapter 2
pages 7–16, including its later search-tree material and Exercises 2.1–2.6,
are present and legible in physical PDF pages 19–28.

The file supplies the full contents, eleven chapters, Appendix A, bibliography,
and index in the expected order and span. A whole-file OCR/header scan found
five blank main-page slots (6, 30, 38, 114, 206); rendering each produced only
white pixels. All seven OCR page-number anomalies (7, 8, 9, 77, 88, 147, 177)
were resolved by visual inspection of their rendered page headers/footers.
Printed page220 was also visually checked at the end of the index. This
establishes source availability and navigation, not exhaustive
mathematical inspection of every later chapter. Chapter-specific reading and
formal statement review remain necessary before accepting later coverage.

## Chapter 1, fully inspected

There are no numbered exercises, mathematical theorem/lemma statements,
algorithms, or code listings in Chapter 1. The five sections are expository:

| Source | Content and disposition |
| --- | --- |
| 1.1, pp1–2 | Immutable updates and preservation of old versions; contrast with ephemeral data. Preserve this as a requirement on later models, not a proof of all functional-language implementations. |
| 1.2, pp2–3 | Strict versus demand-driven evaluation, including memoization. Later chapters own operational and cost semantics; qualitative introductory comparisons are not unrestricted impossibility axioms. |
| 1.3, pp3–4 | Distinguishes abstraction, realization, value/version, logical persistent identity, operator, and invocation. Pointer/root equality does not define logical identity across versions. |
| 1.4, p4 | Reusable design techniques with representative implementations; maps to conaled's interface/law/representation separation. |
| 1.5, pp4–5 | Roadmap through later techniques and Appendix A; all technical obligations remain with their actual chapters. |
| p6 | Visually verified blank; no omitted substantive item. |

The existing section-by-section interpretation in
`conaled/docs/research/pfds-reconstruction.md` remains substantively consistent
with the inspected book, but its source-gap prose must be updated. The full
book-plus-thesis request adds a separate union-accounting requirement; this
book-only inspection does not determine the thesis Chapter 1 disposition.

## Chapter 2: complete item-level inventory

All source references below use printed pages; add 12 for physical PDF pages.
`Current` refers to candidate 70a1477's source/focused-compilation evidence, not
to completed integrated audit or chapter acceptance. These IDs are source-ledger
identifiers proposed for tracking; they are not new GitHub/local ticket numbers.

| ID | Source item | Required formal content | Current coverage / remaining work |
| --- | --- | --- | --- |
| B2-PERSIST | p7 introductory contract | New versions coexist with old ones; unaffected immutable cells can be shared. Keep value correctness, retained old observations, and root/cell identity separate. | SharedList heap extension and `Represents.mono`/allocation retention supply a list instance; a branching tree instance is still needed. |
| B2-STACK | pp7–8, Fig2.1 | Abstract stack operators: empty, emptiness test, cons, head and tail; empty head/tail fail. Operator interface and laws must be separate. | SharedList supplies relevant concrete operations/failure facts, but no complete chapter stack interface and laws/correspondence yet. |
| B2-STACK-LIST | p8, Fig2.2 | Built-in-list implementation of the stack signature and its observation/refinement laws. | Existing Lean List semantics may be reused; chapter-level implementation/correspondence remains. |
| B2-STACK-CUSTOM | p8, Fig2.3 | Distinct custom inductive stack implementation; equivalence to ordinary lists through the public stack laws, including empty failures. | Not supplied by SharedList. |
| B2-APPEND-ABSTRACT | p9 generic append | Generic recursive append expressed through stack operations; prove list concatenation observation and agreement for both stack realizations. Identify assumptions behind per-operation cost. | SharedList's traversal is a concrete realization, not the missing generic-interface proof. |
| B2-APPEND-LIST | p9 pattern-matching append | Concrete list recursion agrees with the generic append and standard concatenation. | Public SharedList result observes `xs ++ ys`; the abstract/direct correspondence is still required. |
| B2-APPEND-SHARING | pp9–10, Fig2.5 | Copy the whole left spine, retain both inputs, and reach the exact original right root after the copied prefix. State O(n) copying under the chosen allocation model. | `appendRun_correct` supplies exact left-length allocation, left-length+1 visits, heap extension and actual right-root sharing. Distinguish copying from visits. |
| B2-UPDATE | pp10–11, Fig2.6 | Indexed replacement succeeds exactly on valid indices, preserves all other elements and the old version, copies only the affected prefix, and shares the untouched tail. Out-of-range access fails. | `updateRun_success`/`updateRun_failure` supply this for natural indices with exact allocation and visits. An explicit source-integer/domain disposition is needed; see notes below. |
| B2-E2.1 | p11 | All suffixes in decreasing length, including empty; O(n) generation and O(n) shared representation space. | `suffixesRun_correct`, chain/reachability/closure/distinctness results and Resources.SharedList cover the explicit model. Keep the counterexample showing why equal suffix values alone are insufficient. |
| B2-ORDER | pp11–12,14; Fig2.9 | Ordered element interface plus laws; binary empty/node trees; strict left<root<right invariant over all descendants. Separate general-tree representation from BST order. | Not supplied by the list prerequisite. Existing conaled ordered-map interfaces may be reused if their hypotheses match. |
| B2-SET | p12, Fig2.7 | Minimal set abstraction with empty, insertion and membership; observation as finite membership/set content, preserving ordering and uniqueness. | New realization/interface correspondence needed. Deletion, enumeration and rank selection are mentioned as possible extensions, not specified algorithms in this chapter. |
| B2-MEMBER | p12; Fig2.9 p14 | Directed membership search is correct for ordered trees; count primitive element comparisons independently of visits. | New proof and measured execution needed. Baseline uses up to two comparisons per visited nonempty node. |
| B2-INSERT | pp13–14; Fig2.8/2.9 | Search-path insertion preserves BST validity, inserts exactly the target element, retains old tree observations, and shares every off-path subtree by actual root identity. | New path-copy tree realization and sharing theorem needed. For an existing element, the displayed algorithm returns the matched subtree but still rebuilds ancestor nodes. |
| B2-E2.2 | pp14–15 | Membership with a candidate carried down the path and equality checked only at termination; at most d+1 element comparisons, plus correctness. | New optimized traversal/proof needed. Define d precisely (e.g. maximum number of nonempty nodes on a path) to avoid an off-by-one depth convention. |
| B2-E2.3 | p15 | Duplicate insertion avoids all copying through an exception/abort propagated to one outer handler; absent insertion remains correct. | New algorithm/refinement needed. A mere final value equality is insufficient: duplicate case must retain original root and allocate no cells, with one outer handling boundary. |
| B2-E2.4 | p15 | Combine candidate comparisons with allocation avoidance: no unnecessary copying, at most d+1 comparisons, correct insertion. | Requires one combined implementation and its joint semantic/resource/sharing result; proving the two separate variants does not complete it. |
| B2-E2.5a | p15 | Complete repeated-element binary tree of natural depth d, in O(d) construction time using intra-object sharing. | New general-tree DAG realization needed. Unfolded size is 2^d−1 under empty-depth0, while identical left/right child roots share the recursively built subtree. This is deliberately not a strict set BST. |
| B2-E2.5b | p15 | Repeated-element tree of arbitrary natural size n; at every node, unfolded child sizes differ by at most one; O(log n) construction using paired sizes via `create2`. | New algorithm and size/balance/sharing/cost proof needed. The pair must have unfolded sizes m and m+1. Use a total small-size bound such as O(log(n+1)) with the source asymptotic relation stated. Height balance alone is weaker than the requested child-size balance. |
| B2-E2.6 | pp15–16, Fig2.10 | Ordered finite-map adaptation with empty, bind and lookup; lookup failure is observable. Key order controls traversal while values remain polymorphic. | New finite-map realization/correspondence needed. State replacement semantics for an existing binding and preserve missing-key failure. The source's common NOTFOUND exception needs an explicit Lean error/Option interpretation. |
| B2-NOTES | pp15–16 section2.3 | Historical attribution and contrast with other persistence methods, including methods that are not purely functional. | Bibliographic/context classification; does not silently import every cited external algorithm or result into the required implementation scope. |

### Consequential interpretation checks

1. **Failure is observable.** Empty tail failure and successful singleton tail
   are different results. The existing root model correctly retains `none`
   versus `some none`. Likewise finite-map absence must remain distinguishable
   from a successfully stored value.
2. **Source integer domains need a stated mapping.** The source update code uses
   integer decrement; negative indices never reach the zero branch and eventually
   fail at the empty list. The existing `Nat` theorem covers meaningful
   nonnegative indices. Chapter completion should either document that domain
   restriction and account for negative source inputs separately, or add a
   corresponding integer wrapper/traversal. Do not claim an all-integer execution
   refinement from a natural-index theorem alone. Natural depths/sizes in E2.5
   are the intended mathematical domain and should be explicit as well.
3. **Element-comparison count is not traversal count.** E2.2/E2.4 require an
   explicit primitive `<`/equality comparison measure. Counting each node once
   and naming it a comparison would not prove the requested optimization.
4. **Duplicate insertion still copies ancestors in the displayed baseline.**
   The equality branch returns its original subtree, but surrounding recursive
   constructors have already committed to rebuilding ancestors on successful
   return. An exception/abort solution must propagate before those allocations.
5. **E2.5 concerns DAG sharing, not just inductive syntax.** Equal child values
   do not establish equal allocated roots, and unfolded node count differs from
   allocated-cell count. Its repeated equal keys are incompatible with strict
   BST order at nontrivial depth, so do not make orderedness a premise for the
   general-tree construction theorem.
6. **Context is not an unbounded new algorithm requirement.** The imperative
   append diagram motivates ownership/destructive use; it is not a universal
   statement that every alias instantly changes value. Garbage collection,
   external persistence techniques, and suggested augmented-set operations need
   explicit contextual disposition, not unsupported runtime claims.

## Full-book navigation inventory

The detailed TOC matches the prior publisher inventory. Later chapter bodies
have not all received chapter-level mathematical statement inspection in this
pass. The table records source availability and numbered exercise headings.
Subparts within an exercise remain distinct proof obligations during detailed
chapter accounting.

| Chapter | Printed span | Main topics | Distinct exercise headings |
| --- | --- | --- | --- |
| 1 | 1–6 | Introduction and terminology | None |
| 2 | 7–16 | Persistent lists, sets, sharing | 2.1–2.6 (6) |
| 3 | 17–30 | Leftist/binomial heaps, red-black trees | 3.1–3.10 (10) |
| 4 | 31–38 | Suspensions and streams | 4.1–4.2 (2) |
| 5 | 39–56 | Amortized methods, queues, heaps, persistence difficulty | 5.1–5.9 (9) |
| 6 | 57–82 | Persistent lazy amortization, banker/physicist analyses | 6.1–6.7 (7) |
| 7 | 83–98 | Scheduling and removal of amortization | 7.1–7.4 (4) |
| 8 | 99–114 | Rebuilding, queues, deques | 8.1–8.7 (7) |
| 9 | 115–140 | Numerical representations and derived structures | 9.1–9.19 (19) |
| 10 | 141–170 | Bootstrapping, catenation, tries | 10.1–10.15 (15) |
| 11 | 171–184 | Implicit recursive slowdown, catenable deques | 11.1–11.4 (4) |
| Appendix A | 185–206 | Haskell interface/implementation correspondence; p206 blank | No numbered exercises |

The heading index totals **83 distinct numbered exercises**, excluding their
subparts. `book-exercise-index.json` gives each heading its printed and physical
PDF page. Its sequence was checked against all consecutive chapter-local
exercise identifiers; the source OCR's `23` was visually corrected to `2.3`,
and a prose cross-reference to Exercise3.7 in Chapter6 was excluded. It also finds 12 distinct numbered theorem/lemma results:
Lemma5.1, Theorem5.2, Theorems6.1–6.2, Theorem7.1, Lemma7.2, Theorem8.1,
Theorem9.1, Lemma9.2, Theorem10.1, and Theorems11.1–11.2. These counts do not
exhaust unnumbered algorithms, invariant arguments, complexity claims, or source
code obligations; they are not a completion metric by themselves.

### Appendix A navigation

Its own contents on p185 lists queues (186–189), deques (189–190), catenable
lists (190–191), catenable deques (191–193), random-access lists (194–196),
heaps (197–201), sortable collections (202), sets (202–203), and finite maps
(204–205). Specific structures include batched/banker/physicist/Hood–Melville/
bootstrapped/implicit queues; banker deques; bootstrapped catenable lists;
simple/implicit catenable deques; binary/skew/alternative random-access lists;
leftist/binomial/splay/pairing/lazy-pairing/skew-binomial/bootstrapped heaps;
bottom-up mergesort; unbalanced/red-black sets; and tries/trie-of-trees.

The appendix does not claim to translate every main-text implementation. Its
class/module signatures, partial results, polymorphic recursion and evaluation
strategy must be compared to the corresponding primary chapter realization;
merely listing equal data-structure names is insufficient. A whole-appendix
semantic/cost correspondence review is pending with its integration ticket.

## Handoff

The parent can resolve the prior book source-gap status, revise the Chapter1
accounting candidate for the supplied book-plus-thesis scope, and then subject
that candidate to the existing required reviews. Chapter2's source inventory
is now concrete; no source-access blocker remains for its exercises. Current
SharedList work discharges a substantial list/sharing prerequisite but does not
complete the full chapter. This report does not change any acceptance decision.
