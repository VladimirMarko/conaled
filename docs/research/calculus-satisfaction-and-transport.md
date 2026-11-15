# Satisfaction and proof transport between dependent calculi

The rule engine need not coincide with one chosen dependent calculus. The
useful target is a collection of independently specified calculi, certified
interpretations, and composition theorems for their stated preservation
contracts. This is a recommendation for the next experiment, not a new checked
framework or an architecture decision.

This note continues [the theory-network comparison](theory-network-comparison.md),
which already studied institutions, LF and MMT, including a successful base
interpretation whose extension is impossible. It also uses the completed
[reference calculus](reference-dependent-calculus.md) and
[pair-contract comparison](primitive-dependent-sums.md). Literature was consulted
on 2026-11-06. No Lean declarations change here.

The 2026-11-07 discussion authorized the bounded experiment in
[#339](https://github.com/VladimirMarko/conaled/issues/339). Changes of underlying
logic and a combined satisfaction/computation interface remain separately
scoped in [#340](https://github.com/VladimirMarko/conaled/issues/340). The
[denotation-boundary inspection](denotation-boundaries-and-settings.md) checks
the actual type-valued parser specification, Felix's exposed representations,
and the distinction between semantic equality and an executable reduction
strategy. It supersedes any reading of the Boolean-observer warning as a
description of the library's primary parser semantics.

## What corresponds to an implementation and a specification?

There are three different objects to connect:

1. A raw expression is candidate syntax. It need not have a typing derivation.
2. A calculus specifies admissible judgments and derivations. A derivation
   certifies a judgment under that calculus's assumptions.
3. An interpretation assigns mathematical meanings and validates the rules
   used by those derivations. A backend implementation can supply such an
   interpretation when it meets the relevant contract.

Thus an engine expression can play the implementation role in a representation
comparison, while an engine theory can play the specification role for a
semantic model. The analogy depends on which connection is under discussion.
A raw expression does not acquire correctness merely by receiving a denotation.
Likewise, a semantic soundness theorem does not identify all target derivations
with source derivations.

The current forward translation compiles reference derivations into an explicit
extension of the guarded engine. It does not promise an arbitrary-expression
reverse compiler. Selective reflection would answer a different question:
if the target proves a translated source claim, may that proof be used as a
source proof? Without reflection, reconstruction, or a separate validity
argument, forward preservation alone does not justify that use.

## The existing MakeLawful mechanism

[CategoryMap](../../SquareKit/CategoryMap.lean) separates raw maps, equivalence,
and operation-preservation laws. `RawMap.induced` defines source equivalence
by equivalence of observations. `inducedLaws` needs preservation of identity
and composition; `comp_laws` composes lawful maps. `transportLaws` transfers
category laws using preservation and reflection of the chosen equivalence.
For the induced equivalence, `induced_reflects` supplies reflection directly.
It does not require an injective decoder or equality of raw representations.

This is already the user's proposed pattern in a categorical fragment. If an
independently chosen source equivalence must be retained, reflection is an
additional obligation. If equivalence is induced by observation, the meaning
of source equality changes accordingly. Neither choice proves preservation
of independently observable data that the observation discards.

For dependent calculi, a prospective generalization must also account for
context extension, substitution, type dependencies and chosen identity data.
It should derive proof preservation from primitive rule interpretations and
composition, rather than demand every client's final theorem as an input.
The present mechanism is evidence for the pattern, not a theorem covering
arbitrary dependent calculi.

[GuardedTheory](../../SquareKit/GuardedTheory.lean) already provides another
part of the proposed machinery: `Model.rules` validates primitive rules,
`Derivation.sound` extends that evidence to complete derivations, and
`Derivation.substitute` acts on proofs. `Hom.eval`, `Hom.identity` and
`Hom.compose` support interpretation through algebra maps over one signature.
These are existing compositional results. They do not yet supply a general
view between independently specified dependent calculi. Engine `Atom.eq` is
interpreted as host equality; modeled identity types are separate signature
structure, so those equalities must not be silently identified.

## Existing mathematical frameworks

Goguen and Burstall's institutions organize signatures, sentences, models and
satisfaction. For a signature map sigma, sentences translate forward and models
reduce backward. Their satisfaction condition is

```text
M' satisfies translate(sigma, phi)
  iff reduct(sigma, M') satisfies phi.
```

This is a semantic commuting condition. Restricting reducts to theory models
requires the translated axioms to hold. It does not construct missing law
proofs or preserve a selected witness merely from the truth of an existential
sentence. Changing logics requires additional structure beyond a signature
map inside one institution. See Definition 1 and Section 2.2 of
[Institutions](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf).
The earlier local comparison supplies a concrete application and its limits.

Bauer, Haselwarter and Lumsdaine distinguish raw, acceptable and well-presented
type theories and prove metatheorems under stated conditions. This is a direct
precedent for separating expressive rule data from evidence of good behavior.
It offers a class of theories to reason about, without forcing every theory to
have identical rules. See
[A general definition of dependent type theories](https://arxiv.org/abs/2009.05539).

Haselwarter and Bauer prove general structural results and translations between
contextual and context-free presentations of finitary type theories. This
supports generic treatment of a specified class, subject to its hypotheses.
It does not supply translations between every pair of distinct calculi or
certify our encoding automatically. See
[Finitary type theories with and without contexts](https://arxiv.org/abs/2112.00539).

Bezem, Coquand, Dybjer and Escardo describe finitely presented generalized
algebraic theories through categories with families carrying extra structure,
and construct initial models. Their morphisms preserve the specified structure
strictly. This is a candidate for generating syntax and interpretations from
suitable presentations; matching our weak or higher comparisons requires a
separate assessment. See
[A Note on Generalized Algebraic Theories and Categories with Families](https://arxiv.org/abs/2012.08370).

The local [LF/MMT assessment](theory-network-comparison.md#mmt-source-hypotheses-and-encoding-audit)
records another option: publish theories and total views with an adequate
encoding. Its successful paper composition does not constitute a checked
cross-logic implementation. A framework can make composition generic after
its conditions are discharged; it cannot make an invalid view total.

## Dependency holes and one-hole contexts

A typed metavariable records an unknown term together with its permitted
context and expected type. The Lean elaboration paper encodes a hole in context
`x:A, y:B` by an application `?m x y`, with a corresponding dependent function
type for `?m`. Solving constraints produces explicit, checked terms. General
higher-order unification is not a complete automatic solution method. See
[Elaboration in Dependent Type Theory](https://leodemoura.github.io/files/elaboration.pdf),
Sections 2 and 3. This is the closest cited mechanism to the proposed dependency
holes, though it is not a translation between object logics by itself.

McBride's derivative identifies one-hole contexts for regular datatypes; a
plugging operation restores the missing subtree. Elliott's worked construction
shows how differentiation and plugging compose for datatype combinators. See
[Differentiation of higher-order types](https://conal.net/blog/posts/differentiation-of-higher-order-types/).
The McBride author-hosted PDF timed out, and its older Nottingham link was
unavailable, so this note does not claim a full rereading of that paper.

Our assessment is that such derivatives may help implement syntax traversal or
focused editing. The cited construction does not itself discharge typing,
binder scope, substitution or identity transport obligations after replacement.
A dependency-aware elaborator and a structural zipper address different parts
of the proposed implementation.

## A universal calculus or a lattice?

A common metalanguage for presenting calculi is a plausible source of reuse.
A single calculus obtained by collecting all their principles does not yield
arbitrary projections back to weaker calculi: a proof may use a principle the
chosen target does not validate. The failed extension in the local
[theory-network comparison](theory-network-comparison.md) already exhibits this
problem with an added cancellation principle.

There is a limited lattice construction. Fix a set of sentences and a
consequence closure operator Cn. Deductively closed theories are ordered by
inclusion; intersections are meets and Cn of unions gives joins. This follows
from the closure-operator laws. It does not establish a lattice of all dependent
calculi with different syntax, equality and binding disciplines. Restricting to
consistent or computationally well-behaved theories can also lose closure under
joins. For those broader comparisons, retain actual translations and their
composition: an ordering that records only existence loses the chosen map and
its effect on selected data. This paragraph is a mathematical assessment, not
a new claim about the repository's implemented theory type.

## Suggested experiment and MVP criterion

Continue the publication/interpretation work under the existing #290/#235
agenda. Use two explicit requirement packages and a shared argument. Supply
local operation and rule interpretations, derive transport for the argument,
and compose two routes. Include a setting that supports the shared fragment
but rejects an added principle. Preserve the selected witness and dependent
substitution, and state which equality each route preserves. Strong and weak
pair specifications are candidate packages, but their full dependency closure
must be stated before treating them as an inclusion of theories.

The user's MVP criterion is an agent-productivity advantage. Human-productivity
evidence is not a prerequisite for that milestone. A useful evaluation compares
agents completing the same frozen task through the existing and proposed
interfaces, with equal correctness requirements. Record setup/model-builder
work separately from repeated author work, together with completion, repair
iterations, tool calls and resource use. These are proposed measurements, not
results established by the present literature review.
