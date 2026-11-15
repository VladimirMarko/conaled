# XD01-DOC-001: natural-merge source attribution

Recorded 2026-11-02. Required provenance correction, low severity. The finding
was raised during `/root/book_inventory`'s read-only natural-run preparation.
Root independently inspected the saved primary source and archive membership.
This continues the existing implementation/review loop; it is not final
Standards/Spec review and closes no acceptance gate.

## Finding and immutable starting state

The original builder draft `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8`
attributes `Natural_Mergesort.thy` to Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. That revision identifies the
separately inspected Isabelle `Sorting.thy`, not the AFP theory. The earlier
design preflight contains the same attribution.

Affected original files:

| File | Original SHA-256 |
| --- | --- |
| `docs/research/fdsa-difference-list-costs.md` in the builder draft | `635f53c8823e2d6f0d54939b5966a90661e54c5861094bf70aa09bec9b7f43a1` |
| `research/difference-list-cost-preflight.md` in this control directory | `a0bd75c09ea1208c880dc87d5e8abe88be207c1e411b118519e7cf6237984232` |

Before editing, the pinned Nix Git read showed branch
`work/fdsa-builder-costs` at ffeaf8a, with empty status, staged diff and
unstaged diff. There were no existing edits to preserve in this checkout.
The original unit base remains
`a14977b9e316cc484ffad8a470d26b15615956c0`; the original frozen requirements
and full unit scope remain unchanged.

## Verified source identity

The Chapter 2 source inventory already records the correct attribution:

- Dated archive:
  <https://isa-afp.org/release/afp-Efficient-Mergesort-2026-10-26.tar.gz>.
- Archive SHA-256:
  `148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708`;
  5,506 bytes in the saved source input.
- Exact archive member: `Efficient-Mergesort/Natural_Mergesort.thy`.
- Theory SHA-256:
  `2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51`;
  6,723 bytes. Root checked that the archive member exactly matches the
  saved reading copy `book-source/Natural_Mergesort.thy`.
- Its actual theory header imports `HOL-Data_Structures.Sorting`.
- The separate `Sorting.thy` input at the recorded Isabelle revision has
  SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.

The archive postdates the July 27, 2026 book. The inspected correspondence
does not assert that every theory is the exact July development.

## Correction and retained history

The current builder note is corrected to distinguish the dated AFP archive
and exact theory hash from the imported Isabelle theory's revision. No Lean
definition, theorem, example, import or reconstruction claim is changed.
The earlier pre-implementation report is retained byte-for-byte as historical
evidence; this finding explicitly corrects its source-attribution sentence.
Consumers must read this erratum with that report. Its original hash in the
handoff remains historical rather than being silently replaced.

State at this report's creation: documentation correction written, candidate
commit and final independent review pending. Root will append the successor
commit identity and whitespace validation after capture. The whole unit
remains uncompiled and unaccepted. The active old Chapter 1 validation
checkout, source, process and cache are unaffected.

## Committed correction

Successor candidate: `62809ced86c561c7a6cce8b71e727177a3f17fb8`. The one-file commit is
`docs(resources): correct natural-merge source provenance (#174)`. Both
whitespace checks passed and the checkout is clean. Corrected note SHA-256:
`fd01432541c9b27ad83def6192e4a3b75d6b77ae7490ec11a2bf665324f1246e`
(10,679 bytes). All Lean sources and the frozen requirements are unchanged.
Finding disposition: correction implemented, independent final confirmation
pending with the whole uncompiled unit. Original evidence remains retained.
