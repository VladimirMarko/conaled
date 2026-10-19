# Standalone orbifold formalization: reviewed reference archive

**Reference material, outside the production library and build.** Use this
collection for selected proof arguments and source criticism. Use current
Mathlib and repository interfaces for implementation. The archive is not a
model of cohesive HoTT, a completed formalization of Myers, or an architecture
template for this repository.

Read the [reuse review](../../../research/orbifold-archive-reuse.md) before
selecting code and the [paper review](../../../research/orbifold-paper-foundations-assessment.md)
before interpreting a claim as a result of the paper. The intended foundational
milestone is [#36](https://github.com/VladimirMarko/conaled/issues/36), not its
already completed graph-proof slice #38.

## What is preserved

[checkpoint-078.tar.gz](checkpoint-078.tar.gz) is the original user-supplied
checkpoint, imported from `/home/vlad/Downloads/orbifolds/` on 2026-10-19.
Its SHA-256 is
`788934695d97bd71e34271f29bed615c4106c9acc4b8736804f196e39cad2c9b`.
It contains the complete standalone sources, paper inventory, coverage maps,
audits and historical verification records. Keeping the compressed original
allows reproduction without exposing its alternative interfaces as ordinary
repository source modules. Its internal instructions and status reports describe
the producing session; they are historical evidence, not current agent guidance.

The accompanying chat response was not copied into this repository. Its useful
scope claims have been reviewed in the linked notes; its session attachment
links and checkpoint narration are unnecessary here. Those reviews are the
maintained reading interface. Future curation may replace or omit obsolete
explanations and examples; byte-for-byte preservation applies only to the
compressed provenance artifact, not to recommendations for reuse.

## Select by purpose

Paths below are relative to `orbifolds-lean/` inside the archive.

| Purpose | Start here | Required boundary |
|---|---|---|
| Check paper scope or the association correction | `docs/COVERAGE.md`, `docs/paper_inventory.md`, `Orbifolds/Finiteness/PrintedCounterexample.lean`, `AssociationCharacterization.lean` | Item mappings include fragments and support; they are not counts of completed internal theorems. Confirm the versioned paper statement. |
| Reuse constructive finiteness arguments | `Orbifolds/Finiteness/EnumerableEmbeddingCriterion.lean` and closure proofs | Native types and predicates need translation for internal use. For classical clients, compare existing finite-type APIs first. |
| Study inertia or torsor evaluation | `Orbifolds/External/Inertia.lean`, `InertiaFiniteness.lean`, `TorsorEvaluation.lean` and related equivariance proofs | Adapt to current groupoid/action interfaces. These results provide neither univalence nor microlinearity. |
| Study constructive compactness proofs | `Orbifolds/External/Compactness/` | Native `DPCompact` holds classically for every type; native `PenonOpen` holds for every predicate. These formulas do not certify ordinary geometric compactness, properness or openness. |
| Examine orthogonality closure | `Orbifolds/Category/` | Ordinary hom-set orthogonality lacks the internal and higher comparison needed for microlinearity. |
| Check invalid native translations | `Orbifolds/Foundations/` | Obstructions apply to the stated native interpretation; they do not refute constructed categorical SDG models. |

The custom `GroupData`, `Action`, `GroupoidData`, `TypeIso` and `Cat` hierarchy
exists because the isolated development used Std alone. **Do not adopt that
hierarchy as this library's design.** Begin with Mathlib's groups, actions,
equivalences and categories and the repository's existing adapters. Retain a
proof's mathematical argument while replacing its packaging where appropriate.

## When promoting a result

1. Name the production consumer and exact intended statement. Check current
   declarations and Mathlib for an existing result before creating an adapter.
2. Classify the contribution as external mathematics, an internal derivation,
   model validity, or a comparison theorem. Ordinary Lean validity and an axiom
   audit alone do not establish internal derivability.
3. Review assumptions and definitions against that statement, including
   satisfiability, isotropy data and any missing geometric hypotheses. The
   supplied-cover lemma, for example, assumes rather than constructs its cover.
4. Port through existing interfaces, retain meaningful checked specializations,
   and run production source-coverage and proof-audit checks. Only then describe
   the result as integrated. Link the original member path for provenance.

Completing #36 may enable translations and comparisons; it will not
automatically reinterpret these native Lean proofs. #34 can use suitable
external algebra independently. Neither workstream should infer numerical
simulation, smoothness or geometric descent from the archive's algebraic results.

## Reproduction boundary

Extract into a temporary directory outside the repository. The archive's
toolchain is Lean 4.33.0-rc1. Review also rebuilt its mathematical sources
unchanged with Lean 4.35.0 and ran both `Audit.lean` and `FullAudit.lean`:
337 project declarations, no dependencies outside `propext`, `Quot.sound`,
and `Classical.choice`, and no unsafe or partial declarations. The detailed
review records the scope of that check. It is not the production repository
audit and does not verify that every statement captures the paper's meaning.

Use the repository's direnv shell, then in the extracted `orbifolds-lean` run:

```sh
lake +leanprover/lean4:v4.35.0 build
lake +leanprover/lean4:v4.35.0 env lean Audit.lean
lake +leanprover/lean4:v4.35.0 env lean FullAudit.lean
```

Keep extracted files and build artifacts outside production import paths.
