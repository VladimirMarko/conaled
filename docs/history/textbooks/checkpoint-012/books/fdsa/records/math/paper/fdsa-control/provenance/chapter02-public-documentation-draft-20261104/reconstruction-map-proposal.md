# Narrow reconstruction-map proposal

Status: source documentation preparation only; no patch is applied.

Base: `f673ee87195e4aaeef4b41767a7468c70ad6214f`, path `docs/research/fdsa-reconstruction-map.md`.
The base file has 617 lines, 40,461 bytes and SHA-256
`0981ce90f2a8491125c921e120d536ad3576d551d8b1606f8de3cb16a34df63b`.

The accompanying patch makes these bounded documentation updates:

1. Replace the Chapter 2 table row with the link to the complete 112-obligation
   note, retaining the separate validation/acceptance boundary.
2. Add a Chapter 2 section immediately before shared insertion costs. It states
   the selected stable floor-left exercise, actual child/run cost semantics,
   two distinct probability experiments and required gates.
3. Reconcile the existing XD01/XM01/XQ01/XU01/XU02/XU03 paragraphs with their
   now-authored Chapter 2 clients. Historical component evidence remains in
   its exact records. No source-correction successor is called compiled or
   accepted by this proposal.

The original accepted Chapter 1 discussion, complete chapter queue, foundation
prefix, appendix correspondence and remaining Chapter 3/10/14 obligations are
retained. No theorem interface, root import, source pin or validation policy is
changed. No generic theorem framework is introduced.

`reconstruction-map-replacements.json` records each exact old/new block.
`fdsa-reconstruction-map.proposed.patch` is the reviewable narrow diff. The
proposal was constructed from the immutable Git blob and checked by exact
single-occurrence replacement; no tracked file or worktree index was written.
The proposed full text has SHA-256 `f4cbe9a83ebbb62a7b22f0542e26b6678b7c7fb0586a3079619b29ea89e00ca1`.

The public note is `fdsa-sorting.md`. The separate `public-example-imports.lean`
contains exactly 23 proposed additions to **each** of `SquareApplications.lean`
and `ProofAudit.lean`; existing imports remain. Import closure and named-source
reference checks are static only, with their exact result in `static-check.json`.
