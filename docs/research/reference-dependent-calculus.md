# A typed reference calculus for the structural and Id/J fragment

[#326](https://github.com/VladimirMarko/conaled/issues/326) now has a bounded
forward correspondence: an independently defined typed inference relation
translates into an explicit extension of the guarded dependent theory.
The extension supplies finite-telescope computation equations that the original
rule table did not expose. Each added equation is valid in every existing
`PathTransport.Typed.Model`. This establishes neither reflection into the
reference calculus nor conservativity over the original guarded theory.

The implementation incorporates integration `986ed1f`. It follows the authorized
bounded investigation from #235 and the declaration/translation obligations in
[the #332 literature study](finitary-type-theories.md). It does not implement
Haselwarter and Bauer's whole framework or inherit their metatheorems. Multiple
independently specified calculi can later be compared at the same boundary.

## Reference judgments and assumptions

[ReferenceCalculus](../../SquareKit/Internal/DependentJudgments/ReferenceCalculus.lean)
defines `Boundary`, `Claim`, `Declaration` and the inductive relation `Derives`.
A boundary is a context, a family over a context, a term of a family, or a
substitution between two contexts. An equality judgment has one boundary for
both operands. The separate tail judgment checks a finite list of dependent
families. `Derives` is not defined by translating a guarded proof or by testing
semantic validity.

This is a contextual explicit-substitution presentation. Its raw constructor
trees and their mechanically verified schematic substitution are shared with
the engine. Object variables are represented by the generic term of an
extension; weakening and pairing implement their binding discipline. An object
substitution is an expression with a source and target context. It is distinct
from replacing primitive expression leaves in a rule schema. Sharing those
mechanics does not identify the two inference relations.

The conventional assumption policy is
[WellFormedSignature](../../SquareKit/Internal/DependentJudgments/ReferenceSignature.lean).
A finite ordered signature may introduce a fresh primitive family or term only
after its context or type has been derived using the preceding declarations.
A family or term equality axiom requires both operands to be formed in that
preceding signature. There are no primitive context or substitution declarations.
This condition does not imply consistency of arbitrary equality axioms.

`Derives` also accepts general lists of family, term and equality assertions.
Every use checks its typing presuppositions. These lists are useful for the
mechanical instantiation theorem, but they are not all conventional signatures:
a family assertion can name a composite expression, for example. The conventional
comparison is restricted to `WellFormedSignature`; its checked examples prove
that condition. Arbitrary replacement of primitive leaves need not preserve
freshness, so the schematic instantiation theorem is not advertised as a theorem
about well-formed signature morphisms.

The supported fragment has empty and extended contexts, family and term
substitution, identity and composition of substitutions, weakening, generic
variables, pairing, their beta/eta and substitution equations, intensional
identity types, reflexivity, path/root presentations, and J with computation
and substitution equations. Context and family conversion retain the typing
boundary. General congruence requires typed equalities of the inputs **and**
formations of both outputs at their common boundary. It cannot manufacture a
typed equality from arbitrary raw congruence.

[ReferencePresuppositions](../../SquareKit/Internal/DependentJudgments/ReferencePresuppositions.lean)
recovers both typed operands of every equality and both contexts of every
substitution. Type-context and term-family judgments are explicit admissible
presupposition rules in this presentation. Some computation constructors expose
endpoint formation premises; public helpers in
[ReferenceDerived](../../SquareKit/Internal/DependentJudgments/ReferenceDerived.lean)
discharge them for pairing eta/beta and J computation/naturality. `rootDef` still
requires its expanded right endpoint to be formed explicitly. This is a
formation obligation, not an equality or normalization premise.

## Actual finite tails and dependent J

[FiniteTail](../../SquareKit/Internal/DependentJudgments/FiniteTail.lean) uses
`nil` and `cons`, rather than a primitive telescope variable. Total context,
projection, reindexing and lifted substitution are recursive operations on this
datatype. A tail's next family is checked over the total preceding context.
The length is unbounded but finite.

Given `x : A` over `Γ`, the path context extends `Γ` by `y : A` and
`p : Id_A(x,y)`. A tail `T` may depend on those variables and every earlier tail
entry. J's motive is a family over the total path-and-tail context. Its branch
lives over the recursively reindexed tail at reflexivity. The branch map in
`jNaturality` has the actual reindexed source and target contexts; its commuting
square supplies the type conversion for the substituted branch. Consequently
J naturality changes the tail, motive and branch together. It is not just an
equation between two evaluations of a closed example.

`path`, `root`, `pathSub` and `branchMap` remain named operations in this
presentation. The path context has an explicit extension equation, and root has
a guarded pair expansion. A general syntactic normalization of all these named
operations to weakening and pairing is outside the proved correspondence.

## Translation and the target correction

[ReferenceTranslation.translate](../../SquareKit/Internal/DependentJudgments/ReferenceTranslation.lean)
is an induction over every reference inference constructor. Formation judgments
translate to guarded predicate derivations. Typed equality translates to a raw
guarded equation, accompanied by translations of the two operand derivations
recovered by `eqOperands`. A tail translates to `Presented`, which includes its
guarded typing and the equations relating recursive contexts/maps to telescope
codes. No guards are discarded in the semantic correctness statement.

The target is
[TelescopePresentation.theory](../../SquareKit/Internal/DependentJudgments/TelescopePresentation.lean),
which has the original signature and all original axioms plus these schema
families:

| Added family | Equation supplied |
|---|---|
| `projectionNil`, `tailMapNil` | Empty-tail projection/map computation |
| `totalCons`, `projectionCons` | Extension and projection of a cons tail |
| `pullbackCons`, `tailMapCons` | Recursive reindexing and lifted map of a cons tail |
| `rootTailDef` | Root-tail map as the corresponding tail map |
| `pathTailDef`, `pathTailMapDef` | Path reindexing as pullback and its tail map |
| `branchSquare` | The root/reindexing substitution square |
| `reindexBranchDef` | Reindexed branch as explicit term substitution along the branch map |

Each family has a validity proof against the existing model operations and laws.
`model` expands every existing `PathTransport.Typed.Model`; `reduct` forgets the
extra rules from any model of the extension and preserves its algebra exactly.
`embed` sends each old guarded derivation to the extension unchanged. There is
no expansion theorem for all arbitrary models of the original guarded theory,
and no proof that the added equations are independent of its old axioms.

The failed direct approach was to treat a typed opaque telescope code as though
its total context and lifted map already computed by the cons recursion. The
original inference table did not provide those equations to that translation.
The correction is the named extension and its validity proofs, not an implicit
change to `Contextual.theory`. `FiniteTailTranslation`, `FinitePathTranslation`,
`FiniteJTranslation` and `FiniteJNaturality` contain the resulting conversion
proofs. J naturality uses the existing target J-substitution rule together with
the displayed expansion equations; it adds no new J principle.

[ReferenceSubstitution](../../SquareKit/Internal/DependentJudgments/ReferenceSubstitution.lean)
proves replacement of schematic leaves preserves every reference derivation,
including conversion, congruence and J naturality. Object substitution remains
the independently typed `subTy`/`subTm` operation with identity and composition
laws. [ReferenceSoundness](../../SquareKit/Internal/DependentJudgments/ReferenceSoundness.lean)
then interprets reference derivations through `translate` and the validated
target extension. An equality's `Claim.Valid` contains both operand guards and
their evaluated equality. Soundness assumes the selected model validates the
declarations; it does not infer that from syntactic well-formedness alone.

## The generated category and empty context

[ReferenceGenerated](../../SquareKit/Internal/DependentJudgments/ReferenceGenerated.lean)
defines finite extension contexts and structurally generated arrows. Arrow
constructors are identity, composition, weakening, pairing, and conversion by a
typed reference equality. Pairing accepts any reference term derivation, so
terms obtained by dependent J are allowed. Quotienting representatives by typed
**reference** substitution equality gives a Mathlib category. `emptyUnique`
proves that every arrow into its empty object equals the recursively generated
empty substitution; the hom type has a `Unique` instance.

The hom-set map `forward` uses the same representatives and quotients them by
the extended guarded theory's equations. It is well-defined by `translate`.
There is no injectivity claim: arbitrary target equations have not been
reflected back into typed source equality.

This category has an explicit grammar boundary. We do not prove every
`Derives Ξ (.has (.sub Δ Γ) σ)` can be represented by its `Arrow` datatype.
In particular, a named path/root/branch-map operation requires expansion and
boundary conversion before a structural representative can be supplied. The
category's empty uniqueness theorem is not a terminality theorem for every
syntactically typed substitution or for arbitrary raw assumptions.

The original-engine result from
[#330](https://github.com/VladimirMarko/conaled/issues/330) is consumed separately
by `original_generated_empty_unique` on exactly its `closedArrows` grammar.
The new J terms are not claimed to land in that older generated grammar.
The old result and its explicit primitive-arrow policy remain intact; allowing
arbitrary primitive substitutions into empty cannot silently acquire terminality.

## Checked uses and statement review

[ReferenceDependentCalculus](../../Examples/ReferenceDependentCalculus.lean)
provides a well-formed four-leaf signature. Its two-entry tail has a family `B`
over the path context and a family `C` over the extension by `B`. Its motive
mentions the last generic term. The branch is constructed by reflexivity and
conversion. `dependentJ`, `beta` and `guardedBeta` exercise the independent
inference relation and the actual forward translation. `naturality` substitutes
a nonidentity parameter weakening through that tail and branch.

The native model satisfies these declarations with `B = Nat` and
`C(z,b) = Fin(b+1)`: the second family's fibers really depend on the first entry.
`interpreted_beta` and `interpreted_naturality` consume `Reference.sound` with
the proved declaration interpretation. `substitutedTwice` checks object
substitution composition through two extensions. A generated point followed by
weakening exercises typed empty uniqueness through a nonempty context.

The malformed example has a raw variable with a guarded reflexive equation but
no typed reference reflexive equation at the proposed term boundary. The proof
uses an interpretation mapping that variable to the invalid value and the
operand-presupposition theorem. Thus the discriminator tests the difference
between raw reflexivity and typed reflexivity; it does not reject ordinary
reflexivity of a well-formed term.

[ReferenceClient](../../Examples/ReferenceClient.lean) constructs the retained
#328 client's right dependent-pair endpoint in the reference calculus, over an
ordered fresh signature with a finite extension context. `Interpretation.typed`
uses the new soundness theorem. `recovers` and `recovered_eq` recover its exact
chosen substitution, including its dependent second component. `recovered_twice`
retains it under two substitutions. `agrees_with_original` uses the retained
client's own equality theorem to identify the left endpoint; it is explicitly
not a translation of that whole original proof into `Derives`.

Statement review distinguishes schematic substitution, object substitution,
typed judgmental equality, identity-type terms and semantic Lean equality.
The universal forward theorem quantifies over derivations, not just the worked
examples. The concrete declaration interpretations rule out vacuous J/client
uses. The equality results retain common boundaries; conversion premises are
checked rather than inferred from raw equality. Category uniqueness quantifies
over its published arrow grammar, not all typed or raw substitutions.

## Mismatches, ownership and migration limits

| Mismatch | Classification and correction | Owner |
|---|---|---|
| Opaque telescope computations needed by the translation | Missing exposed target rules; use the separately named, semantically validated extension. Decide separately whether to add them to the old table. | #326, coordinated by #235 |
| Raw equations or arbitrary context/substitution assumptions | Different assumption/equality policy; remain outside the conventional comparison. Preserve raw use cases instead of pretending their guards follow. | #326; empty-policy results in #330 |
| Named substitutions versus the generated category | Representation limitation; before claiming coverage of all typed substitutions, prove expansions and a landing theorem into `Arrow`, or give an exact obstruction. Current category theorem is restricted to its explicit grammar. | #235 follow-up to #326 |
| Target equation quotient potentially identifies more arrows | Unproved reflection, not an established strict separation. A reverse translation needs its own hypotheses and proof. | #235 follow-up to #326 |
| Retained client left proof not translated | Bounded client connection; the selected right endpoint and the original equality guarantee are checked separately. Translate the whole proof before replacing that retained argument. | #235 follow-up to #326/#328 |

This work changes no Sigma contract and imports no Sigma-specific eta principle.
It preserves the existing stronger interfaces. It is not a parser, a normalizer,
a semantic completeness proof, an initiality result or a universal migration.
The new reference modules and examples are included in the public build and
exhaustive proof audit. Subsequent migration must name the source signature
policy, the target rule table and the equality used by its claimed comparison.
#107 remains paused, #108's theorem remains unselected and unprepared, and #260
remains inactive.
