# PFDS source-completeness follow-up

Checked 2026-11-02 by the independent source-gate agent while the formal candidate
was under validation. This is a bounded public-source check, not an exhaustive
claim about every possible authorized edition or library subscription.

## Result

The missing-source gates remain unresolved. No new book pages were obtained.
Printed p6 has not been inspected, and the apparent blank page is still an
inference. No publicly accessible full-book text from the author, publisher, or
an identified authorized distributor was found in this follow-up.

## Evidence

1. The publisher listing identifies the Introduction as pp1–6. It displays a
   personal/institutional access requirement for it and the other chapters, and
   reports zero accessible chapter items in the public session. Abstracts and
   bibliographic spans do not establish the omitted page's contents.
   <https://www.cambridge.org/core/books/purely-functional-data-structures/0409255DA1B48FA731859AC72E34D494/listing>
2. A separately hosted Cambridge reading sample was located on a book retailer's
   asset host. It is another ten-page copy of the same excerpt, not an expanded
   source. Its SHA-256 is
   `44ab9cede4a494a472bbae46caace3faf4af17a395c3447532cbeef0af3aeaf7`.
   All ten pages render identically to the already inspected publisher excerpt
   when rendered with PyMuPDF at the identity matrix. Consequently it also
   contains printed pp1–5 and7–11 and does not resolve p6 or later pages.
   <https://beckassets.blob.core.windows.net/product/readingsample/332049/9780521663502_excerpt_001.pdf>
3. Targeted searches again returned the 1996 dissertation and the publisher's
   excerpt/frontmatter. The dissertation remains a distinct nine-chapter work
   and cannot certify the book's full exercise or algorithm inventory. Full-book
   mirrors without identified distribution authorization were not followed.
4. No Google Books preview route was retried, no access restriction was bypassed,
   and no sign-in, purchase, user Library search, or other workspace access was
   attempted.

## Additional input needed

The most useful single input is an attached complete copy of the Cambridge book
used by the user, including its edition/publication page. For the currently
identified 1998/1999 edition (ISBN 0521631246 / 0521663504), the exact presently
uninspected mathematical scope is printed p6 and pp12–206, including all exercise
statements, diagrams, code and Appendix A. A legible p6 scan or equivalent
publisher/author evidence explicitly establishing its contents would resolve
the immediate chapter-1 source gate. The remaining pages are still needed before
claiming complete later-chapter coverage. Bibliography pp207–216 would also be
useful for the book's cited technical claims; index pp217–220 is navigation.

The older source inventory had used the phrase "complete substantive" when
describing pp1–5. At the parent's request, it was subsequently corrected to
distinguish inspected pp1–5 from uninspected p6, retaining an explicit note that
the earlier inference was superseded after source review. The reviewed
repository prose and chapter-1 review record already qualify that claim.

## Reproducibility

The retailer PDF was downloaded only into the existing temporary
`research-pfds/` source directory, outside checkpoint payloads. The ten rendered
page comparisons all returned `True`; the source PDFs themselves are excluded
from the durability archive. This report preserves the finding and source URLs
without copying the book text.
