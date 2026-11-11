# Visual Algebra and conaled

Assessment date: 2026-11-11. Positive for a bounded development connecting
labelled diagrams to existing semantics and checked examples. This does not
justify porting an algebra textbook or starting a separate algebra hierarchy.
The proposals below record the initial assessment. The labelled-path bridge
now has a [checked implementation and scope record](schreier-interpretation.md);
the other proposals remain design inferences.

## What is different

Matthew Macauley's Visual Algebra develops algebra through diagrams of
generators, actions, cosets, quotients and related constructions. The subject
remains classical algebra. Its representations and choice of examples make
relationships visible that a presentation by axioms alone can obscure. The
[author's course hub](https://www.math.clemson.edu/~macaule/visualalgebra/index.html)
provides the teaching sequence; his
[Cayley-graph article](https://arxiv.org/html/2402.19438v1) provides a compact
entry point with explicit conventions and examples.

There is also mathematical exploration beyond the usual introductory examples.
[Dihedralizing the quaternions](https://arxiv.org/html/2310.13087v1) investigates
families obtained by varying roots of unity and adding reflections, comparing
matrix realizations and diagrams. Its diquaternion, semidihedral and semiabelian
examples are possible later clients. The Pauli group obtained from quaternion matrices and a reflection is a
promising later comparison of matrix and finite-action realizations. Their
unfamiliarity does not establish a replacement for classical group theory. In particular, a subgroup lattice is
not a complete invariant of a group, and the article discusses that limitation.

## Sources to use

| Source | Best use and limitation |
|---|---|
| [Visual Algebra hub](https://www.math.clemson.edu/~macaule/visualalgebra/index.html) and [older resource page](https://www.math.clemson.edu/~macaule/visualalgebra.html) | Curriculum, slides and exercises, especially generators, maps, actions, extensions and universal constructions. Prefer the current hub when versions differ. |
| [Visual Algebra lecture index](https://www.math.clemson.edu/~macaule/visualalgebra/youtube/) | Guided explanation with linked slides. The older Visual Group Theory course is a separate series; do not assume identical coverage or notation. |
| [Revealing the Hidden Beauty of Finite Groups with Cayley Graphs, v1](https://arxiv.org/html/2402.19438v1) | Short, versioned source for diagram conventions and example selection. It reads right-multiplication paths from left to right. Check formulas against actual group operations before formalization. |
| [Dihedralizing the quaternions, v1](https://arxiv.org/html/2310.13087v1) | Detailed source for less familiar finite groups and comparisons. Record presentations and orders, not names alone: indexing conventions vary. |
| [Fall 2026 Algebra I course](https://www.math.clemson.edu/~macaule/classes/f26_math4120/index.html) | The indexed page says the textbook was finished that summer but was not yet published. Do not treat older “forthcoming” notices as proof of current availability or assume access to the whole manuscript. |
| Pinned Mathlib source, listed below | Implementation authority for the interfaces and theorems already available to this checkout. |

Clemson pages were intermittently inaccessible through direct web fetches;
indexed first-party page text supplied the course/resource inventory. The two
versioned arXiv articles were directly readable. This assessment does not claim
to have read the full textbook or watched the complete lecture series.
Use original explanations and generated diagrams for conaled. The older
teaching page states CC BY-NC-SA 4.0; verify each asset's terms before copying
slides or artwork. No upstream images or manuscripts are imported here.

## Existing implementation and the actual gap

Inspected at conaled commit `76ce2e9f8c848f4a21a0285a570e15b0482b211b`, with
Mathlib pinned by `lake-manifest.json` to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

- Mathlib `Combinatorics/Quiver/Schreier.lean` already defines
  `Quiver.SchreierGraph`, labelled directed edges, `evalWord`, `pathFromWord`,
  `reachable_iff` and `map_smul_of_comp_labelling_eq`. Reuse these rather than
  recreating Cayley/Schreier graphs or proving reachability from scratch.
- Mathlib `Combinatorics/SimpleGraph/Cayley.lean` supplies `SimpleGraph.mulCayley`.
  Its undirected, unlabelled adjacency omits data needed for word semantics.
- [Equivariant.lean](../../Applications/Orbifolds/Equivariant.lean) already
  supplies `actionFunctor`, `orbitMap`, composable `orbitSquare`, and coordinate
  changes with action-groupoid and stabilizer equivalences.
- [FiniteActionPresentation.lean](../../Applications/Orbifolds/FiniteActionPresentation.lean)
  identifies labelled action arrows with Mathlib `ActionCategory` arrows.
  [Its examples](../../Examples/FiniteActionPresentation.lean) already test
  noncommuting composition and an ineffective action. Related work is completed
  in [#435](https://github.com/VladimirMarko/conaled/issues/435); do not reopen
  finite-action presentation construction.

The missing connection identified by this inspection is a reusable interpretation
of generator paths into those existing labelled action arrows, compatible with
equivariant maps, and finite visual examples consuming that interpretation.
A search of the repository and issue-title inventory found no existing task
owning that connection. The orbit/groupoid distinction is already established
in [GLOSSARY.md](../../GLOSSARY.md); it is not a new discovery of this assessment.

## Proposed synthesis and its mathematical boundaries

Use an action `G ↷ X` and a generator map `ι : S → G`. A directed generator
edge records its label and source, with target `ι(s) • x`. Interpret a path
as a group-labelled action arrow. Compose through the existing `ActionCategory`
and equivariant functors. Require only action data for evaluation; generation
is an additional hypothesis for reaching every group arrow. Finite enumerations
belong to finite export, not the mathematical interface.

The following were the intended contracts. The
[implementation record](schreier-interpretation.md) identifies checked Lean
results for items 1–3; item 4 remains a boundary on later coset consumers:

1. For a left action, executing label `g` and then `h` yields label `h * g`.
   Mathlib's `evalWord` multiplies list entries in written order, while its
   `pathFromWord` traverses the tail before the head. Macauley's right-action
   reading uses the other convention. An adapter must state which sequence
   denotes chronological execution and prove the comparison.
2. Equal evaluated labels give equal action arrows at a fixed source.
   Equal endpoints alone do not: a nontrivial trivial action has distinct
   stabilizer labels at the same point. Raw paths can also differ while their
   labels agree. No faithfulness of raw-path interpretation is promised.
3. Symmetrified path reachability describes the orbit under the generated
   subgroup. It describes the whole group orbit only with a generation
   hypothesis. Reuse Mathlib's theorem with precisely that distinction.
4. A coset action exists for a subgroup without requiring normality. A quotient
   group requires normality. Any later quotient visualization must keep those
   claims separate. A Schreier diagram is not automatically a Cayley diagram.

Recover regular actions as Cayley examples and nonfree actions as Schreier
examples through the same interface. Use a noncommuting finite group to expose
composition-order mistakes, and an ineffective action to expose loss of
isotropy. These examples test the library's preservation contracts and the
[language direction](../language-direction.md), rather than introducing a
new frontend solely for attractive notation.

## Follow-up scope

Created [#465](https://github.com/VladimirMarko/conaled/issues/465) for the
labelled-path semantics bridge and
[#466](https://github.com/VladimirMarko/conaled/issues/466) for finite diagrams
with checked edge data. The second is blocked by the first, recorded as a native
GitHub dependency. They should be coordinated with the existing
[transport workstream #200](https://github.com/VladimirMarko/conaled/issues/200)
and use [orbifold work #32](https://github.com/VladimirMarko/conaled/issues/32)
as a consumer, without adding geometry to the algebraic interface.

Defer a complete textbook port, a new interactive graph application, general
presentation word-problem solvers, and a catalogue of exotic groups. Extensions
and matrix realizations become worthwhile follow-ups when a concrete consumer
needs their comparison theorem. A finite diagram can document an action;
it does not establish smoothness, properness, a universal presentation theorem,
or completeness of a group invariant.
