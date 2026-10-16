# ADR 0001 — Separate the proof kernel, application libraries, and compositions

**Status:** Accepted. Toolchain pin updated on 2026-10-16 from Lean/Mathlib
4.19.0 to the matching stable 4.35.0 releases. The module boundaries and proof
dependency policy are unchanged.

## Context

The first delivery established exact representation squares and two source
compilers. The applications require real analysis, finite sums, polynomial
algebra, ordered intervals, and language semantics. Reimplementing all of those
foundations would obscure the new correctness arguments.

## Decision

Keep the original five foundation modules and their namespaces stable. Add
`SquareKit` for application-independent constructions, `Applications/<domain>`
for implementations with their semantic proofs, and `Examples` for compositions
between domains. Use Lean **4.35.0** and pin Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679` (release `v4.35.0`), with its complete
transitive dependency manifest. The original foundation still builds without
Mathlib. Every application theorem is a Lean declaration; no Markdown proof is
used as an unverified dependency of code.

Preserve the original delivery as Git tag `foundation-v1`. Commit architecture,
application families, and integration in separate changes. The Git history
records implementation/integration order, not publication chronology. Package
the source and a Git bundle so history survives artifact download.

## Alternatives

* Stay dependency-free: attractive for the original core, expensive and
  distracting for genuine Fréchet derivatives and general Fourier transforms.
* Make every interpretation an instance of one large CCC interface: would force
  unnecessary or false closure claims on matrices, circuits, and analyses.
* Put everything in one demonstration file: makes independent reuse and proof
  boundaries difficult to audit.

## Consequences

Some application definitions over the real and complex numbers are
noncomputable mathematical specifications. Concrete integer/rational and
finite syntax backends remain executable where their operations are
computable. Mathlib theorems are checked proof dependencies, not new axioms
declared by this project. The audit records foundational axioms explicitly.
Compiler correctness remains relative to the supplied primitive semantics;
the provided application primitive instances prove their obligations.

Research copies of upstream manuscripts and caches are excluded from the
deliverable. References and pinned source revisions document provenance.
