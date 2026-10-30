# Compositional verified programs

Shared vocabulary for organizing the monorepo's development efforts,
mathematics, and executable systems.

## Development efforts and standards

**Workstream**:
A sustained development effort with related research questions and deliverables,
such as FRP, orbifold simulation, or hardware architecture derivation. A
workstream can contribute to several shared components and executable systems.
_Avoid_: Application as a name for an entire development effort.

**Construction and observation**:
The workstream studying how program construction, observation, interpretation,
and extension fit together through explicit compatibility laws.
_Avoid_: Duality as the name for the whole workstream; duality is one research direction within it.

**Capability parity**:
Coverage of a named reference's constructions and proved behavior under
comparable assumptions. A parity claim is relative to an explicit scope and
reference revision.

**Architectural quality**:
The generality, expressive power, composability, and caller effort of the
interfaces through which capabilities are provided. Matching capabilities alone
does not establish matching architectural quality.

## Mathematical and compiler components

**Foundation**:
Reusable mathematical structure and proof principles shared across domains,
including categorical operations, semantic equivalence, and law transport.

**Compiler frontend**:
A source language, its typing and meaning, and its translation into the
categorical operations required to interpret its programs.

**Compiler backend**:
An interpretation of those operations in a target representation, with the
preservation obligations needed for compiler correctness. A backend can describe
a mathematical analysis as well as executable code or hardware.

**Transport route**:
A translation of specified judgments together with a map of their semantic
interpretations and a comparison connecting the two. Its preservation contract
does not by itself provide reflection back to the source.

**Internal setting construction**:
A construction of a setting from presentation data expressed within a base
language, with interpretation and substitution rules for those data.
_Avoid_: External model parameter as a synonym for an internally presented setting.

**Specialization**:
A general construction instantiated with particular objects, operations,
representations, or assumptions. Its guarantees follow by discharging the
construction's requirements.

**Mathematical application**:
A use of a theorem or construction to establish a result in a particular
setting. It may combine several specializations and additional proofs.
_Avoid_: Unqualified application when software or a workstream is also in view.

**Domain library**:
Reusable definitions, operations, and proofs for a subject such as reactive
computation, geometry, or circuits. A domain library can support multiple
workstreams and systems.

**Sheaf torsor**:
A sheaf over a base with a group-sheaf action that is locally isomorphic to
the regular action of that group. Local triviality permits a torsor with no
global section; global triviality is equivalent to having a global section.
_Avoid_: Trivial torsor as a synonym for locally trivial torsor.

**Effective descent**:
Recovery of global objects and their morphisms from compatible local objects
and morphisms on a cover. For torsors, compatibility retains equivariant
isomorphisms and their cocycle equations, not only isomorphism classes.

**Action quotient**:
A groupoid-valued quotient of a group action whose objects over a parameter
are torsors equipped with equivariant maps into the acted-on space.
Its arrows retain stabilizers, including elements that act trivially.
_Avoid_: Orbit set as a synonym when isotropy or transport matters.

**Homotopy pullback**:
A pullback whose objects include a comparison isomorphism between their two
images. Its arrows must commute with that comparison. For groupoids this is
an isocomma groupoid; a strict equality of images omits boundary data.

## Realizations and executable systems

**Realization**:
A representation or implementation connected to a specification by a stated
semantic contract. Different realizations can preserve exact meaning or meet
different approximation and observation contracts.

**Software application**:
A runnable system serving a user-facing purpose, such as an orbifold simulator.
It can compose several domain libraries and realizations.
_Avoid_: Application without qualification in architectural discussions.

**Hardware architecture derivation**:
The development of hardware realizations from shared specifications through
explicit choices about locality, communication, storage, spatial duplication,
and temporal reuse, with contracts relating the resulting observations.
