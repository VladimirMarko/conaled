# PFDS source inventory

Inspected 2026-11-02. This is an evidence inventory, not a coverage or proof-completion claim. Downloaded manuscripts, scans, and OCR are temporary research inputs outside the checkpoint's `session/` and repository trees; this record contains bibliographic metadata and paraphrased observations only.

## Edition and authoritative sources

The target is Chris Okasaki, *Purely Functional Data Structures*, Cambridge University Press, first published 1998; first paperback edition 1999. The inspected publisher frontmatter identifies ISBN 0521631246 (hardback) and 0521663504 (paperback), with digital printing in 2003. The current publisher record identifies DOI `10.1017/CBO9780511530104` and ISBN 9780521663502. The publisher reports 232 physical pages; numbered main text ends at 220.

| Evidence | URL | Locally verified extent |
| --- | --- | --- |
| Publisher book record | https://www.cambridge.org/core/books/purely-functional-data-structures/0409255DA1B48FA731859AC72E34D494 | Chapter titles and page spans |
| Publisher frontmatter | https://assets.cambridge.org/97805216/63502/frontmatter/9780521663502_frontmatter.pdf | 8 scanned pages; publication data, full detailed contents, preface |
| Publisher excerpt | https://assets.cambridge.org/97805216/63502/excerpt/9780521663502_excerpt.pdf | 10 scanned pages corresponding to printed pp. 1–5 and 7–11; printed p. 6 is omitted between chapters |
| Author's dissertation at CMU | https://www.cs.cmu.edu/~rwh/students/okasaki.pdf | Full 1996 dissertation, report CMU-CS-96-177; different organization and coverage from the book |

SHA-256 of retrieved PDFs:

```text
frontmatter 6fdfe24ac29b98252139a1aa483c1a56fba8f5807545d9ce788dc059c57148cb
excerpt     a39a8a3adb7e2d718a1395ad040e84403bf9c2bf669ebe4722aa850bea92f87b
thesis      f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072
```

The frontmatter's printed TOC pp. v–vii was visually checked after OCR. The public excerpt contains inspected Chapter 1 pp. 1–5, the list discussion in Chapter 2 pp. 7–11, and the beginning of its search-tree discussion. Printed p. 6 is omitted and remains uninspected. Full Chapter 2 pp. 12–16 and Chapters 3–11 remain uninspected at book-text level.

Source-review correction: this inventory originally called pp. 1–5 the "complete substantive" introduction, based on the ended roadmap and the publisher's omission of p. 6. That inference was superseded after source review: apparent blankness is not inspected evidence, and the Chapter 1 source-completeness gate remains open. See `../reviews/chapter01.md` and `source-gate-followup.md`.

## Section map

The following is a compact topic map with exact section identifiers and start pages. Labels below summarize the contents rather than transcribe the prose.

| Chapter, printed pages | Sections and topics (start page) |
| --- | --- |
| 1, 1–6 | 1.1 functional/imperative differences (1); 1.2 strict/lazy evaluation (2); 1.3 terminology (3); 1.4 methodological approach (4); 1.5 roadmap (4) |
| 2, 7–16 | 2.1 lists (7); 2.2 binary search trees (11); 2.3 notes (15) |
| 3, 17–30 | 3.1 leftist heaps (17); 3.2 binomial heaps (20); 3.3 red-black trees (24); 3.4 notes (29) |
| 4, 31–38 | 4.1 suspension notation (31); 4.2 streams (34); 4.3 notes (37) |
| 5, 39–56 | 5.1 amortized analysis (39); 5.2 queues (42); 5.3 binomial heaps (45); 5.4 splay heaps (46); 5.5 pairing heaps (52); 5.6 persistence difficulty (54); 5.7 notes (55) |
| 6, 57–82 | 6.1 traces/logical time (57); 6.2 reconciling persistence/amortization (58), with laziness 6.2.1 (59) and analysis framework 6.2.2 (59); 6.3 banker analysis (61), justification 6.3.1 (62), queues 6.3.2 (64), debit inheritance 6.3.3 (67); 6.4 physicist analysis (68), binomial heaps 6.4.1 (70), queues 6.4.2 (72), shared bottom-up mergesort 6.4.3 (74); 6.5 lazy pairing heaps (79); 6.6 notes (81) |
| 7, 83–98 | 7.1 scheduling (84); 7.2 real-time queues (86); 7.3 binomial heaps (89); 7.4 shared bottom-up mergesort (94); 7.5 notes (97) |
| 8, 99–114 | 8.1 batched rebuilding (99); 8.2 global rebuilding (101), Hood–Melville queues 8.2.1 (102); 8.3 lazy rebuilding (104); 8.4 deques (106), restricted output 8.4.1 (107), banker deques 8.4.2 (108), real-time deques 8.4.3 (111); 8.5 notes (113) |
| 9, 115–140 | 9.1 positional systems (116); 9.2 binary numbers (116), random-access lists 9.2.1 (119), zeroless digits 9.2.2 (122), lazy digits 9.2.3 (125), segmented digits 9.2.4 (127); 9.3 skew binary (130), random-access lists 9.3.1 (132), binomial heaps 9.3.2 (134); 9.4 bases three/four (138); 9.5 notes (140) |
| 10, 141–170 | 10.1 decomposition (142), non-uniform recursion in SML 10.1.1 (143), binary random-access lists 10.1.2 (144), bootstrapped queues 10.1.3 (146); 10.2 abstraction (151), catenable lists 10.2.1 (153), merging heaps 10.2.2 (158); 10.3 aggregate types (163), tries 10.3.1 (163), generalized tries 10.3.2 (166); 10.4 notes (169) |
| 11, 171–184 | 11.1 queues/deques (171); 11.2 catenable deques (175); 11.3 notes (184) |
| Appendix A, 185–206 | Haskell translations; correspondence with chapter implementations must be checked |

Bibliography occupies 207–216; index 217–220. These are source-navigation material, not independent algorithm milestones.

## Chapter 1 inspection

No numbered theorem, exercise, algorithm, or code listing appears in inspected Chapter 1 pp. 1–5; this statement does not account for uninspected p. 6. The inspected text motivates immutable updates and the availability of multiple versions; distinguishes eager evaluation from demand-driven evaluation with memoization; separates an abstract interface, its implementation, a value/version, and an identity across versions; and explains the later chapters' design techniques.

For a formal coverage ledger, these are conceptual commitments and terminology, not standalone universally quantified claims supplied by the source. Cost claims require an explicit evaluation/allocation model; Lean's immutable value semantics alone do not prove physical sharing or amortized bounds. The chapter's broad discussion of strict/lazy evaluation should not be silently converted into an unrestricted impossibility theorem. Later chapters supply the technical hypotheses and examples. A chapter-1 completion decision therefore needs explicit non-formal classifications and links to the project interfaces that realize these distinctions, rather than invented introductory theorems.

## Chapter 2 obligations actually inspected

| Printed pages | Source item | Formal content to account for |
| --- | --- | --- |
| 7–8 | Stack interface and two representations | Empty/test/cons/head/tail behavior, including empty-operation failure; equivalence of built-in lists and a custom inductive stack |
| 9–10 | Append | Functional concatenation semantics; traversal/copy cost proportional to the first argument; preservation of both original versions; entire second argument may be shared |
| 10 | Indexed update | Successful replacement semantics and out-of-range failure; copying exactly the affected prefix under the chosen allocation model; unchanged suffix may be shared |
| 11 | Exercise 2.1 | Return every suffix in decreasing length, including the empty suffix; establish linear time and linear shared representation space, not total size of fully expanded nested lists |
| 11 | Search-tree introduction | Empty/node representation; every left key smaller and every right key larger than the node key; element type equipped with a total order |

No authoritative text of Exercises 2.2–2.6 has yet been inspected. Secondary solutions can suggest an inventory, but do not close that evidence gap.

## Dissertation limitation and retrieval notes

The 1996 dissertation has nine numbered chapters; its Chapter 2 concerns laziness, not book Chapter 2's persistence. It omits the book's early introduction to lists/search trees and familiar heaps/balanced trees. Book-only additions also include material such as tries. The dissertation is a valuable primary technical source for later techniques, but its proof/algorithm inventory cannot certify complete coverage of the book.

Legacy author pages at Columbia returned 404, and a publisher university-press storefront returned 403. These were not bypassed. The CMU thesis path uses `/~rwh/students/okasaki.pdf`, not `/~rwh/theses/okasaki.pdf`. The general web tool's initial `open` failed, but both search engines subsequently returned results. Direct public publisher downloads succeeded.

The publisher-permitted Google Books preview at https://books.google.com/books?id=SxPzSTcTalAC&printsec=frontcover advertises a page inventory, but direct reads of pp. 12–16 returned an explicit viewing-limit restriction and no page image. That route was stopped. A page's presence in that advertised inventory must not be treated as inspected content or usable access.

Companion-code investigation found an attributed author note mirrored at https://github.com/mmottl/pure-fun/blob/main/README-Okasaki.md. The note says the author's online SML listings needed special lazy-evaluation support; the placeholder suspension constructor did not itself deliver the book's timing guarantees. The repository's current source is an OCaml translation through Chapter 9, not an original complete SML distribution. Another source-code pointer led to https://github.com/dcolish/purely-fun, an incomplete multi-language reimplementation. Neither repository supplies authoritative book exercise coverage. No code from these sources was copied into conaled.

Temporary inspection files: `/workspace/scratch/ca9a61d0bf30/research-pfds/`. Chapter 1 OCR is `excerpt-01.ocr.txt` through `excerpt-05.ocr.txt`; Chapter 2's inspected portion is `excerpt-06.ocr.txt` through `excerpt-10.ocr.txt`. These temporary files are not required checkpoint payloads: reproduce them from the cited URLs and hashes when needed.
