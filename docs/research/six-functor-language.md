# Six-functor reasoning as a language application

Research assessment, 2026-11-15. Local declarations inspected at
`3953578fa05e34e5311780a1d4acd7dbd60690d5`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`.

Six-functor reasoning belongs within the ambition of the
[setting-parametric language](../language-direction.md). It is a demanding
application of reasoning across families of mathematical settings. A motivic
realization is a substantial mathematical development within that scope.
Neither abstraction nor specialization is a reason to exclude it.

The owner's clarification on 2026-11-15 makes both shared interpretation and
transport between settings explicit goals of the whole language effort, whenever
their mathematical requirements hold. This investigation should develop both
capabilities and their relationship. It should also assess expansion into wider
frameworks that recover existing constructions and support additional mathematics.

This note separates published mathematical results, inspected Lean declarations,
and proposed design tests. It proposes research, not an architecture adoption or
a claim that conaled already implements a six-functor language.

## Voevodsky's project and what survives

Voevodsky's [2014 account, *The Origins and Motivations of Univalent Foundations*](https://www.ias.edu/ideas/2014/voevodsky-origins)
names **2-theories** as the higher-dimensional mathematics whose verification
burden helped push him toward proof assistants around 2000. His concern combined
the effort of precise exposition with experience of errors surviving expert
scrutiny. That supports the recollection behind this investigation; it does not
identify every intended component of 2-theories.

The surviving [*Cross functors* draft](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Unfinished_papers/Motives/2theories/Abstract/2015_td_copy.pdf)
is filed under `Motives/2theories`. Its first-page footnote dates most work to
December 1998–March 1999 and records the later title change from *The four
functors formalism*. Section 1 develops exchange data over a category with
fiber products, valued in a 2-category. The preliminary Proposition 0.4 is
especially relevant to proof tooling: it asserts independence from the sequence
of adjunction transformations, but supplies an illustration instead of a full
proof. It is a research source, not a checked library dependency.

The contemporary [IAS lecture description](https://www.ias.edu/math/sp/motivic_homotopy_theory_program)
distinguishes the abstract cross-functor theory, homotopy-invariant cross functors
on schemes, and a motivic stable-homotopy construction. It also names derived
categories of ℓ-adic sheaves as an example. Thus the historical project already
combined reusable formal reasoning with domain realizations.

Deligne's lecture notes are listed in the
[IAS publications archive](https://www.math.ias.edu/vladimir/publications?o=asc&s=title).
The annotated archive links used in the preceding conversation were inaccessible
during this investigation; the original Cross functors PDF was accessible.
This note therefore does not repeat unverified claims about the completeness of
every surviving manuscript. Neither these records nor the present investigation
establish that all of 2-theories became six-functor formalism, or that Voevodsky
completed the original project in a proof assistant.

## Later mathematics and the abstract interface

Ayoub's [*Les six opérations de Grothendieck…*, Astérisque 314 (2007)](https://www.numdam.org/item/AST_2007__314__R1_0/)
and [volume 315, abstract and contents](https://smf.emath.fr/sites/default/files/2025-09/AST_2007__315__1_0__sample.pdf)
document a developed motivic program: six operations, constructibility and
exactness, nearby motives, and construction of stable homotopy categories of
schemes. These publications establish a continuation of the mathematical subject;
they are not evidence that every intended 2-theory was completed.

Scholze's [*Six-Functor Formalisms*, October 2025 revision](https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf),
Definitions 2.3–2.5 and the opening of Lecture III, packages the operations as a
lax symmetric monoidal functor

\[
D:\operatorname{Corr}(C,E)\longrightarrow\operatorname{Cat}_{\infty}.
\]

Here $C$ has finite limits; $E$ contains isomorphisms and is closed under
composition, pullback, and diagonals. A correspondence $X\leftarrow W\to Y$,
whose right leg lies in $E$, acts by pullback followed by exceptional
pushforward. Requiring right adjoints to tensoring, pullback and exceptional
pushforward supplies the other operations. The six are

\[
f^*\dashv f_*,\qquad f_!\dashv f^!,\qquad
(-\otimes A)\dashv\underline{\operatorname{Hom}}(A,-).
\]

The correspondence presentation encodes composition and base change coherently;
adjoints acquire the corresponding coherences. Lecture IV's construction
theorem has additional hypotheses, not supplied merely by this definition.
Lecture VII, the appendix on D-modules, and Lecture XI treat different
realizations. This is a useful modern entry point, with a distinction between
specifying the formalism and constructing an example.

[Cnossen–Lenz–Linskens, *Universality of span 2-categories…*, v2 (2026)](https://arxiv.org/abs/2505.19192v2),
abstract, characterizes extensions to suitable higher span
categories using adjoints and Beck–Chevalley conditions. Its assumptions include
specified classes of morphisms and adjointability requirements; it does not
turn arbitrary pull–push data into a six-functor formalism. The universal-property
approach is a candidate for deriving compatibility once, instead of asking
every client to prove each diagram separately.

The literature continues beyond the 2025 survey. [Carmeli–Kapon–Nissan,
*Six functor formalisms via internal higher algebra* (September 2026)](https://arxiv.org/abs/2609.37520v1)
reports an extension to a lax symmetric monoidal functor of $(\infty,2)$-categories
using classes of $D$-proper and $D$-étale maps. This note checked its abstract,
not its proof. The proposed comparison should examine its internal higher
algebra against the span approach before choosing a foundation.

**Assessment:** modern constructions supersede the unfinished draft as our main
implementation reference. The original verification problem remains relevant.
Calling the subject obsolete would confuse improved solutions with disappearance
of the problem.

## What the local library actually provides

The inspected declarations already contain adjunction and base-change machinery.
Introducing mates from scratch would duplicate existing work.

| Evidence | Contract and limit |
|---|---|
| [`GeometricMorphism`](../../SquareKit/Internal/GeometricMorphism.lean) | Stores inverse image, direct image, their adjunction, and finite-limit preservation of inverse image. Its morphisms retain all natural transformations of inverse images. This is a specific ordinary-category interface. |
| [`GeometricMorphism.onSlices` and `along`](../../SquareKit/Internal/GeometricSlice.lean) | Construct slice adjunctions. `along` requires an exponentiable map, expressed by `Closed (Over.mk s)`, as well as pullbacks. |
| [`pullbackPost`](../../SquareKit/Internal/GeometricMixedChange.lean) | Compares context pullback with ambient inverse image using finite-limit preservation. `pullbackPost_fst` and `pullbackPost_snd` retain both projections. Identity, ambient composition and context composition have named theorems. `mixedGeometricIso` additionally assumes the relevant slice objects are closed. |
| [`DependentBaseChange`](../../SquareKit/DependentBaseChange.lean) | For an actual `IsPullback`, constructs `leftComparison` and its canonical mate `pullbackComparison`. `WithAdjunction.mate` uses specified right adjoints; `mate_conjugate` proves invertibility by iterated mates and conjugation. Evaluation and `curry_baseChange` laws expose usable behavior. |
| [`AdjointComparison.mate`](../../SquareKit/AdjointComparison.lean) | Proves compatibility when both chosen right adjoints change by their canonical uniqueness isomorphisms. |
| [`IndexedWitnessAdjunctions.NonPullback`](../../Examples/IndexedWitnessAdjunctions.lean) | `not_pullback`, `not_invertible` and `inverse_mate_not_invertible` provide failure controls. An invertible transformation need not have an invertible mate. |

Pinned Mathlib's
[`Adjunction/Mates.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Adjunction/Mates.lean)
already proves `mateEquiv_vcomp`, `mateEquiv_hcomp` and `mateEquiv_square`.
Its general mate equivalence must be distinguished from `conjugateIsoEquiv`,
which transports isomorphisms in its more restricted situation. Mathlib also
contains a [bicategorical mate implementation](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean).
Local [higher path transport](../../SquareKit/Internal/PathTransport/TwoStrongInverse.lean)
already uses mates and their composition law.

These are useful specializations and comparison points. They do not establish a
language for an arbitrary family of stable higher categories with six operations.
In particular, finite-limit-preserving geometric inverse image is not a
substitute for the tensor, exceptional operations, and higher coherence required
by the wider application. The remaining question is how existing constructions
participate in that application, not whether a particular local proof resembles
a base-change diagram.

## Language and foundation requirements to investigate

The following are **design inferences** from the application and the repository's
language direction, not theorems proved by this note.

An author needs to name a family $D(X)$, express objects and arrows in its
members, move them along base maps, and compare composite routes. The requirements
of an argument must include the relevant classes of base maps and the laws
actually consumed. For example, forming a comparison and using its inverse are
different requirements. The existing noninvertible-mate example should remain
an acceptance control when automation hides diagram manipulations.

Model provision and argument authoring need distinct evidence. A realization
must supply the chosen operations and laws. An author should then reuse an
argument without rebuilding those operations or spelling out their coherence
at every occurrence. A printed formula with several interpretations is
insufficient if each interpretation needs a separately written proof.

We should compare an ordinary bicategorical treatment for arguments it supports,
a correspondence-based higher treatment, and the internal higher-algebra route.
Truncation must state which observations survive: equality of arrows in a
homotopy category does not by itself retain specified higher witnesses. Conversely,
a useful ordinary-category specialization should remain usable without importing
every higher construction.

Lean is the implementation and verification host; this does not settle the
source foundation. A design must explain where higher categories and their
coherence live, which judgments the author uses, how interpretations act on
them, and how universe sizes are controlled. Native proof irrelevance must not
erase data the source contract intends to observe. The study should compare
encodings and checked interpretations before proposing new kernel principles.
The current [proof-dependency policy](../adr/0010-composition-and-proof-audit.md)
continues to apply. No decision to add univalence as an axiom follows here.

## Research agenda and acceptance evidence

[#555](https://github.com/VladimirMarko/conaled/issues/555) owns the full
six-functor language application. Two independent investigations start that
program; neither redefines the ambition around today's easiest Lean example.

**Existing comparison reuse, [#556](https://github.com/VladimirMarko/conaled/issues/556).** Assess `GeometricMixedChange`,
`DependentBaseChange`, `AdjointComparison`, and their consumers against Mathlib's
mates and pasting laws. Determine which local obligations derive from existing
universal properties and which carry additional witness contracts. A bounded
experiment should recover actual projections, evaluation, identity and composition
behavior under the original hypotheses. It should retain the noninvertibility
control, include a nonidentity change of setting, and report repeated author
effort separately from framework setup. A finding that the present interface is
already appropriate is an acceptable result. A cosmetic rewrite is not evidence
of architectural improvement.

The comparison should assess what a wider coherence framework would let us
express or prove beyond the current clients. Recover those clients as concrete
specializations under their existing assumptions and witness contracts. Record
the additional capability, required structure, and remaining work even when the
first experiment does not implement it. Retaining a suitable native interface
for one client does not settle the broader framework question.

**A reusable six-functor argument, [#557](https://github.com/VladimirMarko/conaled/issues/557).** Select a published argument that consumes
tensor, base change and adjunction or duality, then record its precise assumptions
before choosing an encoding. Candidate families include projection-formula-based
cohomological calculations and duality arguments. [Gallauer's introduction,
§§1–2](https://mgallauer.warwick.ac.uk/docs/m6ff.pdf) supplies examples and separates
coefficient-system construction from the resulting operations; it is a reading
input, not the frozen benchmark specification.

Trace every step of the selected argument to its required operations and
coherences. Compare an ordinary presentation with a higher correspondence
presentation under the same observational contract. Identify at least two
mathematically distinct realizations, with an explicit motivic route retained.
State what each supplies and which additional geometry remains to be proved.
Assess the author's ability to reuse the argument and to receive a precise
missing-obligation report when a realization lacks a hypothesis.

An initial argument may use only a fragment of the six operations. Record the
unused operations explicitly and supply a second sourced argument or an owned
gap for exceptional pullback, internal Hom, and any untested higher structure.
For example, proposed author syntax for a base-change step must identify the
input object's category, the square, its admissibility evidence, and the
comparison being applied; elaboration should recover routine composites without
inventing invertibility evidence. This is a proposed interface obligation,
not an implemented syntax design.

Separate expressing one argument, instantiating it in two realizations, and
transporting it along a map between those realizations. The last achievement
needs a preservation contract for the map; two independent interpretations do
not supply it. Both forms of reuse are intended capabilities. Alongside the
multiple-realization argument, select a concrete connection between settings and
work through transport at the paper level: state the preserved operations,
comparison transformations, coherence and witnesses, and show which conclusion
transports. The connection need not join the first two chosen realizations if
no suitable route exists. If a proposed route fails, identify the mathematical
obstruction or missing hypothesis and retain a scoped owner for the remaining
transport investigation. Merely listing the distinction does not complete this
part of #557. Report which obstacles concern mathematical libraries, which concern
the chosen encoding, and which concern the intended source judgments.

The first deliverable may be a paper-level capability assessment and dependency
map. Any checked checkpoint must state its truncation and interpretation scope.
It cannot stand in for constructing the motivic categories, verifying their
exceptional operations, or establishing the higher interpretation contract.
Keep those residual obligations assigned under #555 after bounded work finishes.
Completing #556 or the first assessment in #557 does not close #555.

Continuing coordination belongs with [#235](https://github.com/VladimirMarko/conaled/issues/235)
and the language efforts [#200](https://github.com/VladimirMarko/conaled/issues/200)
and [#36](https://github.com/VladimirMarko/conaled/issues/36). Dependent coherence
connects to [#289](https://github.com/VladimirMarko/conaled/issues/289), reusable
proof requirements to [#290](https://github.com/VladimirMarko/conaled/issues/290),
foundation-relative interfaces to [#493](https://github.com/VladimirMarko/conaled/issues/493),
and coherence automation to [#548](https://github.com/VladimirMarko/conaled/issues/548).
Those connections should share evidence without treating one bounded coherence
experiment as completion of the six-functor application.
