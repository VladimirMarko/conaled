# Reuse assessment of the standalone orbifold development

Assessment against repository commit `10a2d6b55364cae66d87d293726b6ea79288dd7f`,
2026-10-19. Source: `/home/vlad/Downloads/orbifolds/`, checkpoint 078 archive,
SHA-256 `788934695d97bd71e34271f29bed615c4106c9acc4b8736804f196e39cad2c9b`.
The archive's `docs/COVERAGE.md` and actual Lean declarations are the scope
evidence; `orbifolds-response.md` is a summary, not the verification authority.
The checkpoint is now retained behind the
[curated archive guide](../history/orbifold/standalone-formalization/README.md).
The user clarified that the intended milestone was completion of #36; the
#38 discussion below explains the narrower infrastructure boundary.

The archive contains reusable external mathematics and constructive proof plans.
It does not contain the internal microlinearity or orbifold comparison theorem.
Its most promising additions are selected inertia, torsor, and constructive
finiteness results. Importing its entire replacement algebra/category hierarchy
would duplicate existing interfaces and increase integration work.

The companion [paper assessment](orbifold-paper-foundations-assessment.md)
checks the primary-source statements and foundational requirements.

## What #38 changes

[#38](https://github.com/VladimirMarko/conaled/issues/38) is already closed.
Its scope is typed regular-logic graph derivations, Set soundness, and comparison
with existing squares. In [Logic.lean](../../SquareKit/Internal/Logic.lean),
`Derives` has explicit rule constructors and no admission of arbitrary external
validity. An ordinary theorem about Lean types is therefore not automatically
an internal derivation. Completing #38 neither changes the truth of the archive's
external theorems nor gives them synthetic geometric meaning.

Even the compactness proofs require more than #38's equality/conjunction/
existential fragment: they quantify over predicates and use disjunction and
universal quantification. The finiteness proofs additionally use finite objects,
subtypes, dependent constructions and, in the embedding criterion, a quotient.
Their rule and object requirements need individual translation and interpretation.
Absence of `Classical.choice` does not establish that such a translation exists.

If the intended milestone was completion of
[#36](https://github.com/VladimirMarko/conaled/issues/36), the answer is different:
these constructive arguments could shorten selected internal proofs, after
translation into the supported language and comparison of definitions. They
still would not supply the missing microlinearity, higher/cohesive structure,
descent, or proper étale comparison arguments.

Current #36 work already goes beyond #38: see the constructed
[geometric KL interface](../../SquareKit/SmoothGeometricKL.lean),
[manifold interpretation](../../SquareKit/SmoothManifoldInterpretation.lean),
and [implementation evidence](algebraic-kl-model.md). The latest issue checkpoint
places full faithfulness in #95 and targeted Myers requirements in #96. This
assessment does not replace that sequence or restart set-level SDG foundations.

## Reuse by component

| Archive component | Use before further #36 work | Integration judgment |
|---|---|---|
| Groups, actions, action groupoids, stabilizers | Ordinary symmetry semantics | Mostly duplicate Mathlib and `Applications/Orbifolds/Equivariant.lean`; retain useful cases, use existing interfaces. |
| Torsor evaluation and its equivariance | Proofs identifying points with equivariant maps/bijections from the regular action | Useful algebraic proof reference if a consumer needs this identification. No univalent torsor universe or delooping theorem. Adapt `TypeIso`, `GroupData`, and action records to standard interfaces. |
| Inertia groupoid and finite homs | Ordinary objects `(x, α : Aut x)` and commuting arrows | Strong candidate for a bounded addition; adapt to Mathlib groupoids and establish a consumer before importing. Does not prove an inertia orbifold is microlinear. |
| Constructive finiteness, corrected association, embedding criterion | Valid external combinatorics; future internal proof plans | Preserve distinctions and proof dependencies for internal use. For ordinary classical finite-action clients, first compare with existing `Finite`/`Fintype` results. |
| DP compactness/properness and Penon predicates | Constructive derivation examples | Cannot certify geometric compactness or properness of the simulator. Translate into a non-Boolean internal interpretation before geometric use. |
| Orthogonality closure under products, pullbacks, retracts | Ordinary categorical lemmas | Adapt only where existing categorical APIs lack the needed statement. Hom-set orthogonality alone is not microlinearity. |
| Native equality/KL obstruction results | Regression specifications for invalid foundational shortcuts | Useful safeguards; current model construction already respects the external/internal distinction. |
| Paper inventory and counterexample | Immediate statement-review evidence | Preserve with versioned provenance; coverage mappings are not completed theorem counts. |

Sources for the table are the archive's `Orbifolds/External/`,
`Orbifolds/Finiteness/`, `Orbifolds/Category/`, `Orbifolds/Foundations/`,
and `docs/COVERAGE.md`. No exhaustive Mathlib novelty search was performed;
candidate additions still need that check.

## Consequences for #34

The repository already has explicit action functors, coordinate-change groupoid
equivalences, stabilizer comparison and orbit squares in
[Equivariant.lean](../../Applications/Orbifolds/Equivariant.lean).
[QuarterTurn.lean](../../Applications/Orbifolds/QuarterTurn.lean) proves apex and
nonzero stabilizer statements, smooth actions, and tangent compatibility for
the disk-to-ellipse coordinate change. These are closer to #34's geometric
requirements than the archive's two-element action on a singleton.

The numerical work is also already separate: see
[numerical-motion.md](numerical-motion.md). The archive adds no motion law,
connection, numerical step, integration error bound or renderer. It can support
the simulator's symmetry mathematics, but does not remove its dynamics or
execution obligations.

A useful selective port would construct inertia through existing groupoid
interfaces and specialize it to the quarter-turn action. At the origin there
are four automorphism-labelled objects over that point; away from the origin
only the identity label occurs. In the inertia groupoid, automorphisms at a
labelled object are the centralizer of that label in the stabilizer. These are
proposed independent expectations for checked specializations, not new checked
results of this assessment. Use them only if the workstream needs this view of
isotropy; they are not a prerequisite for basic motion simulation.

## Statement-review findings

The archive correctly retains symmetry labels as data in `Type`. Its torsor
evaluation theorem establishes an ordinary type equivalence, not identities
in a univalent universe. Its inertia theorem establishes finite ordinary hom
types, not the missing microlinearity conclusion. The subsingleton-cover lemma
assumes the cover, its smallness, and finite indexing; it does not produce the
geometric cover needed by the paper.

The external compactness distinction is observable. A scratch Lean check proved
`DPCompact K` for every ordinary type `K`, using classical case analysis on the
fixed proposition. Another proved `PenonOpen U` for every ordinary predicate
`U`, using decidable equality. Thus these predicates cannot distinguish compact
geometric spaces or open subsets in the intended sense in this interpretation.
This does not invalidate their constructive proofs; it limits what their native
statements certify. The scratch checks introduce no production declarations.

The paper's printed association uniqueness direction in Proposition 6.1.7
really permits every type to be associated to one label. The archive separates
that counterexample from the corrected condition, in which each label represents
at most one point. See the [primary text](https://arxiv.org/html/2205.15887v1#S6.SS1.Thmthm7)
and the companion assessment. This is valuable source criticism, not a reason
to discard the broader program.

## Verification and next preparation

Extracted the archive into `/tmp/conaled-orbifold-review/orbifolds-lean` and
rebuilt its sources unchanged using `lake +leanprover/lean4:v4.35.0 build`
inside the repository's direnv environment. Build passed. Both `Audit.lean`
and `FullAudit.lean` passed on 4.35.0. The latter reported 337 project
declarations, 156 theorem declarations, no unexpected axiom dependencies, and
no unsafe or partial declarations. The archive hash matches its handoff.
These counts describe checked declarations, not coverage of Myers's theorems.

This checks standalone compatibility and proof dependencies, not an integrated
library port. No production Lean files were changed; the repository's full
380-module check was not rerun. Integration still requires standard-interface
adapters, retained cases, source-coverage registration and the repository audit.

For later HoTT/SDG source selection, begin with the exact theorem chosen in #96
and identify its missing rules and model properties. Future formalization
handoffs should include this repository's current APIs, an exact target
statement, and a checked path from derivation through interpretation to a
consumer. Ask for constructed instances and comparison theorems, with proof
plans explicitly distinguished from implementation. More isolated native
encodings would repeat the translation work exposed here. Targeted library/book
selection and the authoring-format handoff are now acceptance items in
[#96](https://github.com/VladimirMarko/conaled/issues/96), after its theorem
selection and dependency analysis.
