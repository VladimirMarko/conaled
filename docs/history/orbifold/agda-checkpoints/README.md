# Supplied Agda formalization checkpoints

The later [Myers checkpoint 080 and consumer reports](checkpoint-080/README.md)
were supplied on 2026-11-08 and have their own evidence inventory and fresh
ordinary-Agda replay. The historical checkpoint 22 and Kock inventory below
remains unchanged; it does not describe the later Myers development.

The user supplied these incomplete formalizations during the orbifold-motion
reassessment on 2026-11-04. The archives are preserved byte-for-byte:

- [Myers checkpoint 22](myers-orbifolds-agda-checkpoint-022.tar.gz)
- [Kock SDG checkpoint](kock-sdg-agda-checkpoint.tar.gz)

They are source and recovery artifacts, outside the integrated Lean build.
This inventory inspected metadata and representative source; it did not run
archive scripts, rebuild Agda modules, or perform a complete theorem audit.
The successful checks described below are supplied receipts. Parameterized
proofs contain substantial mathematics; neither receipt establishes a model
of all their ambient geometric hypotheses.

[inspection.json](inspection.json) records archive byte sizes and SHA-256
identities. This session verified every manifest entry (1,696 Myers and 158
Kock files) and all source hashes in the supplied receipts (357 and 146,
respectively), with no mismatches. These checks establish correspondence to
the supplied metadata, not fresh type checking or theorem correctness.

## Myers checkpoint 22

Archive paths below are relative to `myers-agda-checkpoint/`. The archive
contains `formalization/`, pinned `dependencies/cubical-0.9/`, a native compiler
setup kit, recovery notes, and `MANIFEST.json`. Compiler binaries and generated
interfaces are excluded. The intended source is Myers,
[arXiv:2205.15887v1](https://arxiv.org/abs/2205.15887v1).

`formalization/CHECKPOINT.json` identifies checkpoint 22 and reports 357 checked
modules. `formalization/validation/latest-check.json` records exit code zero,
Agda 2.8.0.2, and Cubical commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. Acceptance is limited to the import
closure of `formalization/src/Everything.agda`. The project library file and
the inspected main theorem specify:

```text
--safe --cubical --guardedness --no-import-sorts --cohesion
```

The source uses genuine Cubical identity, univalence, truncations and higher
inductive constructions. Native crisp binders are enabled; flat splitting is
not. Additional crisp structural laws remain explicit parameters, as explained
in `formalization/CRISP_FOUNDATION.md`, `CRISP_IDENTITY.md` and `CRISP_LIMITS.md`.

The inspected `formalization/src/Orbifolds/FullProperEtaleOrbifolds.agda`
exports `Context.Presentation.Ordinary.proper-etale-completion-orbifold`.
It applies `ProperEtaleManifoldOrbifolds` and the proved
`FullInfinitesimalMicrolinearity` bridge to conclude that the actual groupoid
completion is an orbifold with the full infinitesimal-variety definition.
The desired microlinearity and properly finite identities are conclusions,
not assumed fields. See `formalization/PROPER-ETALE-ORBIFOLD-SCOPE.md` for
the claimed correspondence with the paper's Theorem 6.3.7.

Its displayed inputs include a crisp commutative ring and Kock-field structure;
crisp identity and flat induction/computation rules; order compatibility and
constancy; ordinary manifold structures on objects and total arrows; the
real-flat axiom, crisp excluded middle, tinyness of the infinitesimal generator,
flat/truncation distribution, and crystalline preservation of crisp pullbacks;
covering, interval compactness and positive-line equivalence; and actual
Dubuc–Penon properness of source-target and crystalline étaleness of source.
Some rules are required at multiple universes. These inputs must survive any
reuse assessment. External topological properness is a separate comparison,
documented in `formalization/PROPERNESS-SCOPE.md`.

Read `formalization/STATUS.md`, `paper-inventory.json` and the correction notes
before selecting more results. The paper inventory is not a completion claim.

## Kock SDG checkpoint

Archive paths here are relative to `kock-sdg-agda/`. The target is Kock's
[Synthetic Differential Geometry, second edition](https://users-math.au.dk/kock/sdg99.pdf),
not his later *Synthetic Geometry of Manifolds*. `pins.json` records the book
and compiler identities. There are no external library dependencies.
`validation/latest.json` reports a fresh Agda 2.8.0.2 check, exit code zero,
146 modules, and flags `--safe --without-K`. `src/Everything.agda` is the
aggregate entrypoint. This is not a Cubical development.

In the inspected `src/SDG/Axiom.agda`, a commutative ring is a parameter;
`KockLawvere` supplies slope, affine expansion and uniqueness. It is an
interface for an assumption, not an inhabitant or a model. The inspected
`src/SDG/ChapterI/Section07Linear.agda` constructs tangent-fiber module laws
and tangent module maps from infinitesimal linearity, with explicit setness
and function-extensionality hypotheses where used. These are derived results,
not merely a list of desired tangent operations.

`STATUS.json` and `docs/BOOK-MAP.md` report extensive Part I work on calculus,
Taylor expansions, tangents, flows, Lie brackets, integration and forms, with
remaining qualifications in I.6, I.8, I.15 and I.16. I.17 is active; later
parts and appendices are unfinished. `docs/COVERAGE-I-06-16.md` gives finer
scope. Higher KL, integration, order, extensionality and related requirements
are explicit where needed. No geometric model is constructed. The status
inventory was read, but every listed theorem was not independently inspected.

## Use in the follow-up work

[#310](https://github.com/VladimirMarko/conaled/issues/310) should use these
as existing source evidence when comparing mathematical settings and author
interfaces, including substantial synthetic proofs already expressed in Agda.
The movement experiment should identify which tangent, flow or connection
prerequisites can actually be reused and which require new proofs.

[#321](https://github.com/VladimirMarko/conaled/issues/321) should start from
the pinned sources, accepted import closures, receipts and explicit ambient
interfaces when assessing the Cubical route. Keep the non-Cubical Kock source
distinct: shared mathematics does not establish direct library compatibility.
Record a new independent rebuild before treating supplied checks as locally
reproduced. A source comparison, an executable realization and a constructed
smooth model have separate acceptance obligations; none is supplied merely
by restoring these archives.

## Later curated mathematical snapshot

The [096-10 source archive](checkpoint-096-10-source/README.md) preserves the
later project and pinned dependency sources, mathematical notes and isolated
pending additions. It removes nested recovery history and runtime packaging.
Its independent properness replay has a separate scope from the older checkpoints
and does not certify the entire newer development.
