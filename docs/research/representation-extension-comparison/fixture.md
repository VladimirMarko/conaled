# Frozen comparison fixture for #287

This contract is frozen before route comparison. Changes require an explicit
revision and rerunning both routes against the revised contract.

## Theory, judgments and models

Use classical many-sorted first-order logic with equality and nonempty sorts.
The old signature has sorts A, B, a binary predicate R on A, and a unary
predicate P on A. T consists exactly of reflexivity, symmetry and transitivity
of R; P is unrestricted. Terms are variables. Source judgments are well-sorted
terms, formulas in finite typed contexts, and sequents Γ ⊨ φ with finite formula
premises, interpreted by ordinary Tarskian satisfaction. When syntactic
consequence is discussed, fix any sound and complete classical many-sorted
first-order calculus; proof trees are not identified with truth values.

Admit every set model M of T with nonempty A and B, including infinite ones.
Morphisms f:M→N are pairs of functions on A and B preserving R and P in the
forward direction. They need not reflect predicates or preserve arbitrary
first-order formulas. Isomorphisms have inverse morphisms. Old observations
are all old formulas with assignments, and old sentences as a special case;
comparison along isomorphisms preserves them. No preservation of those
observations along arbitrary homomorphisms is requested.

## Extensions and witness contract

First add C representing A×B with projections. Next add Q representing A/R
with a quotient map. Compare direct set constructions, presented through
existing local interpretation/representation interfaces where they fit, with
explicit first-order Morita extension axioms for these same sorts. Neither
route may restrict the old model class after seeing a failing case.

Required model contract: every admitted old model expands, with reduct equal
to that old model in the canonical set construction, and any other expansion
is isomorphic over the old model. Extend every chosen morphism functorially.
Recover old interpretations after composing the extensions by an explicit
comparison fixing old carriers. Distinguish this from construction in just one
selected model.

Witnesses are external set-valued dependent data, not an extra first-order
proof-relevance axiom. Given E over A and coherent bijections E(a)→E(a') for
R(a,a'), retain an equivariant chosen section as a section over Q, together
with fiber comparison isomorphisms. State identity and composition laws and
prove descent for the particular construction used. Do not promise descent
for representative-sensitive sections. Require a concrete successful dependent
case and a concrete failed representative-sensitive case. Exact recovery of
arbitrary chosen source proof trees, judgmental equality, and a natural
representative selector are not required and must not be inferred.

## Fixed controls and assessment

Use the two-element set A={0,1}, singleton B, universal R and empty P for the
symmetric no-natural-selector control. Its swap automorphism must remain
admitted. For a separate failed extension add c:A and P(c), using the same
empty-P old model; also exhibit a selected model where this extension works.

Assess semantic old-consequence reflection separately from proof-object
transport. Compare author and model-builder obligations on the same fragment.
Assess dependent Morita/coherence only under the exact source hypotheses;
retain existing higher-identity clients. Separate mathematical suitability,
Lean encoding feasibility and measured author effectiveness. Paper derivations
are acceptable; no Lean verification is claimed by this fixture.
