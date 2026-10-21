# Contextual J: design experiments and alternatives

This records the design work for [#104], part of the Agda transfer experiment
in [#102]. The starting implementation is `91995694a9b9bfb377da0e53cce7a27548f20cbf`.
The toolchain is Lean 4.35.0 with the repository's pinned Mathlib. The
[transfer contract] states the required mathematics; the [language direction]
states the broader author experience we are trying to achieve.

This records the implemented #104 design, not a decision that this encoding
should become the project's general frontend. The typed core, constructed
groupoid model, arbitrary-tail elimination, rebuilt-J substitution, and named
source callers compile together. Whole-repository validation and independent
review are recorded in the implementation handoff.

The observations below come from implementation and checked probes by the
framework implementer, the contextual-elimination and typed-syntax helpers,
and the originating session. They are framework-construction evidence.
They do not measure independent proof-author effort; [#106] owns that test.

## What the representation has to preserve

The selected upstream argument eliminates the first path while retaining a
dependent tail containing a second endpoint, a second path, and a fiber
element. Source paths must retain arrow data in the groupoid model. Lean
equality of base objects would erase the distinction the experiment tests.
The implementation must also distinguish judgmental conversion from identity
types, and construct the interpretation of every supported rule.

These constraints explain several choices below. They do not require a
particular syntax encoding, a general universe, internal function types, or
host functions inserted as source terms. A convenient target proof of
transport functoriality cannot replace the source derivation.

## Syntax and interpretation experiments

| Approach | What was tried or established | Limitation and disposition |
| --- | --- | --- |
| Raw expressions with extrinsic judgments in `Prop` | Contexts, simultaneous substitutions, J premises, and separate type/term conversions were developed around the existing raw syntax. | A recursive interpreter returning semantic data cannot generally eliminate these proof objects into `Type`. This representation was revised; the failure does not rule out extrinsic syntax with a different semantic construction. |
| Move the derivations into `Type` | Typed substitutions, generalized-tail beta typing, and a named typing-only caller compiled. | This permits data-producing recursion but does not choose one interpretation of a raw context independently of its formation derivation. Types and substitutions still have to agree on the interpretations selected by their premises. The change alone did not solve soundness. |
| Canonical evaluator for raw syntax | Considered as a way to choose semantics independently of typing evidence. | The raw J node retained a tail length, not its declarations. A canonical evaluator would need additional annotations or reconstruction, together with coherence proofs. No complete evaluator was implemented, and this route was deferred rather than disproved. |
| Direct mutually indexed context/type definitions | A minimal Lean declaration was tested; the reproducer below fails. | The proposed declaration needs the context type in the header of the other mutual inductive. This particular declaration is rejected. That is a restriction of this encoding, not a proof that intrinsic syntax is impossible in Lean. |
| Syntax indexed by model-parametric interpretation codes | Inductive judgments retain raw context/type/term indices and also carry codes evaluated uniformly in an abstract model. Constructor-recursive interpretation and agreement theorems compile. | This avoids the immediate recursive-definition problem but makes the implementation more elaborate. Codes and their coherence must remain hidden from ordinary authors. Its suitability for a larger language remains untested. |

The minimal mutually indexed declaration fails with
`error(lean.unknownIdentifier): Unknown identifier Context` at the second
inductive header:

```lean
mutual
  inductive Context : Type where
    | empty
    | extend (Γ : Context) (A : TypeExpr Γ)
  inductive TypeExpr : Context → Type where
    | base (Γ : Context) : TypeExpr Γ
end
```

This was reproduced with `direnv exec . lake env lean <file>` on the pinned
toolchain. Keep failed declarations in documentation or external probes;
they do not belong in the production import closure. Alternative encodings
using a shared code universe or a separately defined raw grammar were not
excluded by this test.

### Why interpretation codes are constrained

Schematically, a context code is `∀ M, M.Context`, a type code maps each model
to a family over that context, and a term code maps it to a section. Such
functions alone would be an unrestricted semantic interface. The supported
syntax therefore requires inductive derivations whose constructors produce
the codes from source operations. There is no constructor accepting an
arbitrary section as a source term.

Retaining raw indices matters. Equality of semantic codes must not authorize
changing the raw type or deriving source conversion. `TyEqDeriv` and `TmEqDeriv` must
come from the declared source rules. The same inductive derivation is
interpreted in each model, and a concrete groupoid instance must prove the
model laws. An abstract record of those laws is only an interface.

A recursive interpreter returning only a section encountered a further
dependent typing problem at reflexivity: the result family mentions the
recursively interpreted endpoint, whereas the indexed result type mentions
its code. Returning a section together with its equality to the code supplied
the needed connection at each recursive step. This checked construction
explains the simultaneous interpretation/agreement interface. It is another
cost a replacement encoding should account for, rather than assuming that
changing the inductive declaration alone completes interpretation.

### Conversion and the declaration-order problem

A conversion constructor needs to transport a term code from one type code
to another. The intended equality follows from the source type-conversion
derivation, but its soundness theorem is defined after the mutually inductive
judgments. It cannot be called in their declaration.

The working encoding stores a redundant equality certificate alongside the
genuine syntactic conversion premise. The public constructor derives that
certificate using the later soundness theorem. Proof irrelevance establishes
that choosing a different certificate does not change the cast result.

The safety conditions are part of the design: the syntactic conversion
premise must concern the exact raw context and types; the certificate cannot
create a conversion; and generic conversion soundness must be proved for all
rules. Requiring authors to provide the certificate would expose the
representation problem instead of solving it. A future encoding should try
to remove this bookkeeping while preserving those conditions.

### Conversion closure and its context boundary

The first review found that beta computation and conversion soundness did not
by themselves make conversion a congruence. The initial rules could compare
substituted terms only after receiving a substitution equality, but supplied
no rule lifting a term equality into a paired substitution. They also lacked
a rule replacing a J branch. Thus a converted subexpression could get stuck
inside a larger source construction even though its denotations were equal.

The corrected interface adds generated dependent pairing congruence and J
motive/branch congruence, with generic soundness. The dependent pairing rule
compares both the base substitutions and their new terms, transporting the
second term's type by the generated substitution equality. The J rule
compares motives in the same path-and-tail context and branches in its
reflexive specialization. Its instantiated form also compares simultaneous
endpoint/path/tail substitutions. Public operations derive the redundant
coherence certificates from source equality; a semantic equality alone still
cannot authorize any raw conversion.

The supported congruence operations are:

| Construction | Generated conversion |
| --- | --- |
| Primitive base | Reflexivity; substitution uses `baseSub`. |
| Primitive family | `TyEqDeriv.fiber` consumes equality of base terms. |
| Identity type | Endpoint congruence and `identityCongr` for its underlying type. |
| Reflexivity term | `reflexivityCongr`, with the dependent result type transported. |
| Type/term substitution | Conversion of the expression by `sub`; conversion of the substitution by `subCongr` / `substitutionCongr`. |
| Substitution composition and pairing | `SubEqDeriv.comp` and `pairingCongr`; the latter changes both components dependently. |
| J at fixed Γ/A/x/telescope | `pathInductionCongr` and `pathInductionMotiveCongr` compare motives and branches; `pathInductionAtCongr` also compares endpoint/path/tail substitutions. |
| Reindexing J's whole input | `jSub` rebuilds A, x, telescope, motive and branch under the supplied typed context substitution. |

These operations do not provide a judgment converting arbitrary raw context
presentations or transporting a derivation between arbitrarily converted
telescope declarations. In particular, fixed-context J congruence is not a
claim about independently changing its raw A, fixed point x, or telescope
while leaving its premises in their old contexts. Rebuilt-J substitution
changes these inputs together through a checked context map. A future
frontend needing arbitrary context conversion must supply that additional
metatheory; ambient equality of semantic context codes is not a substitute.

`Authoring.CongruenceCaller` retains an inner beta redex under an outer J,
including endpoint-instantiated J, and inside an identity proof supplied as
a later dependent substitution component. It also changes an identity motive
using that beta equality. The cases construct actual typed terms and
substitutions on both sides and consume `termSound` or `subSound` together
with interpretation agreement. `beta_sides_distinct` and
`nested_sides_distinct` check that the compared raw syntax differs. The
normalization of interpretation annotations in this caller keeps the raw
context, type and term fixed; it does not create source conversion.

This review exposed a frontend obligation beyond making direct beta calls
convenient: conversion must remain available when a proof is nested inside
another constructor. The checked cases are framework-author evidence and
do not replace the independent-author experiment.

## Groupoid representation and elimination

The committed groundwork provided constant-family arrow identities and
set-valued based elimination. It did not yet provide contextual J with
arbitrary supported groupoid-valued motives and dependent tails.

The semantic development first used a comma category of paths from a section.
This made the contraction to the reflexive branch explicit. For a dependent
family, a vertical subcategory of a total-category construction gave an
intermediate model of the same idea. The final source context, however, is
formed by two actual comprehensions. A categorical equivalence to a convenient
path category alone does not establish its required computation and
substitution laws. The contraction was subsequently constructed on that
actual context.

An early identity-family representation used vertical arrows represented by
subtypes in the total category. Replacing it with arrows directly in the
fiber made identity reindexing strict: endpoint conjugation acts on the
fiber arrow itself, and the identity-family substitution equation reduces
definitionally. In the subtype representation, substituting a different
context changes the ambient total category in which the arrows live.
Precomposition therefore does not directly give the same identity family.
This was a representation problem; no failure of groupoid identity
elimination was found.

The retained family has discrete fiber `x γ ⟶ y γ`. Along a context arrow
`f : γ ⟶ δ`, it sends `p` to
`inv (x.map f) ≫ (A.map f).map p ≫ y.map f`.
Its functoriality uses the section laws and the equality transports for
`A.map_comp`. Normalized sections store objects and arrows in these fibers;
their associated functors into comprehension lie over the identity strictly.
This makes substitution ordinary precomposition.

Dependent elimination extends a branch section along the path-context
equivalence. A general equivalence supplies isomorphisms where the split
model needs selected strict equalities. Normalizing the section and the
equivalence supplies the chosen representative with strict reflexive
computation. Repeated Grothendieck extension then handles arbitrary finite
dependent tails. The checked construction includes groupoid-valued motives;
it is not limited to the original set-valued elimination case.

Concretely, normalization transports each total-category object along its
projection isomorphism and conjugates its arrows by the induced transport
isomorphisms. The chosen equivalence has unit components equal to the
canonical equality arrows. Preservation of this condition by
`Grothendieck.preEquivalence` is the recursive step for dependent tails.
Replacing the forward functor with the source model's canonical `rootTail`
uses a proved equality and preserves the naturality square. An arbitrary
isomorphism of contexts would not justify that replacement.

### Substitution is a separate obligation

Substituting an already constructed section, proving beta after substitution,
and rebuilding J from substituted inputs are different checks. The last
requires comparing the path contraction, motive, reflexive branch, and all
dependent-tail substitutions.

The working proof uses a square between equivalences with forward, inverse,
and counit compatibility. The square lifts through a Grothendieck extension,
so it can be iterated through the tail. Normalized extension then commutes
with that square. [`JNaturality.lean`](../../SquareKit/Internal/PathTransport/JNaturality.lean)
proves the functor and section comparisons.
[`GroupoidSoundness.lean`](../../SquareKit/Internal/PathTransport/GroupoidSoundness.lean)
connects them to the structural model in four steps: `squareLift_eq`
identifies the pair/cast map with Mathlib's Grothendieck map/precomposition;
`telescopeModelSquare` recurses on the exact `Telescope.square` map;
`rootTailModelSquare` preserves the canonical forward-functor choices; and
`contextualJ_sub` proves equality with the rebuilt section and reindexed
branch. The source `TmEqDeriv.jSub` rule in
[`Typed.lean`](../../SquareKit/Internal/PathTransport/Typed.lean) consumes
that law through generic `termSound`. The named weakening example in
[`Authoring.lean`](../../SquareKit/Internal/PathTransport/Authoring.lean)
compares actual substituted and rebuilt source J terms.

The final recursive proof initially failed when `simpa` unfolded dependent
category arguments while comparing the two telescope recursions. Rewriting
`Telescope.square` explicitly before the recursive call preserved those
arguments. This was a Lean conversion difficulty; the single-extension
commuting-square theorem was already proved.

## Author-interface experiments

The early raw-typing caller retained `z`, `q`, and `b` and closed a `q = q`
motive by reflexivity. It exposed whether tail formation and beta typing
could be automated, but it did not demonstrate interpretation of that caller.
The retained `Authoring.NamedCaller.reflexiveApplication` now constructs the
source J term in the interpreted core. Its `interpreted_beta` theorem uses
`interpretTm_agrees` and the generic `termSound` theorem.

One early beta constructor asked the caller for a typing derivation of the
computed right-hand side. That obligation was derivable from the J premises
and typed substitution. A generic helper discharged it, removing a repeated
author obligation without adding a source rule.

The interpreted caller also exposed a restriction in the initial J
constructor: its conclusion context was fixed to the context containing the
base type and fixed endpoint. Applying the canonical reflexive branch in its
own extended context then required extra plumbing. The retained
`pathInductionReindex` contextual rule permits a conclusion context Ω and a generated
base substitution ρ into the original context. It substitutes A and x along
ρ, the motive under n + 2 binders, and the branch under n binders. The
canonical application uses the reflexive branch context for Ω and its
projection for ρ. `jBetaReindex` supplies the source computation proof.

Adding an earlier fiber element b₀ was considered as a workaround for this
particular example, but was not implemented. The generalized-context rule
handles the reusable structural operation. These contextual forms are
additional inductive constructors validated by interpretation. Their raw
erasures use the same Expr J node; the implementation does not prove that
every constructor is derivable solely from the smaller original rule set. It adds no internal Π type or
constructor accepting a host function as a source term.

This caller is a structural exercise, not the `tr-concat` port. A successful
framework-author example also does not establish that a fresh author can use
the interface easily. Preserve these distinctions in later usability claims.

## Questions for a more elegant interface

The current implementation gives concrete places to seek improvements:

- Can an intrinsic or separately annotated syntax avoid model-code casts
  while keeping ordinary inductive definitions and recursive interpretation?
  Compare an actual contextual caller and its soundness proof before choosing.
- Can a smaller typed substitution/comprehension interface absorb the raw
  context arithmetic now repeated across rules and named operations?
- Can a reusable interface for split-comprehension substitution squares hide
  repeated `eqToHom` conversions? Exercise it on a tail whose second
  declaration depends on its first. Empty or constant tails do not test the
  same comparison.
- Which equalities need to be strict, and where would explicit coherent
  isomorphisms simplify the implementation without burdening proof authors?
  Test computation and substitution together, not just object-level meaning.
- Can the generalized-tail caller be expressed with ordinary names and a
  small set of operations that also work for the next independent proof?
- Are interpretation codes an internal implementation device that remains
  hidden as the fragment grows, or do new rules repeatedly expose them?

These are proposals for further experiments. None has been established as a
superior replacement by this implementation.

## Relevance to compiling-to-categories frontends

The shared design problem is an argument or program whose required structure
is supplied by a target. The model-parametric syntax experiment makes that
separation explicit, while the conversion and substitution work shows the
cost of preserving it through dependent contexts.

Several tests carry over to a compiler frontend: retain a source artifact
distinct from its denotation; interpret every admitted constructor; expose
required target capabilities; and test public author operations while
building the backend. A compiler can use host functions to construct syntax
without allowing arbitrary host computation to bypass the source language.
Likewise, prettier notation is insufficient if users still manage all the
representation's substitutions and casts.

The groupoid contraction and contextual-J machinery are specific to this
proof fragment. This work does not show that a compiling-to-categories
frontend should adopt them, or that the two frontends need a shared AST.
Use checked programs and proofs to establish what can be shared. The
[language direction] supplies the common objective without fixing one
implementation for both workstreams.

[#104]: https://github.com/VladimirMarko/conaled/issues/104
[#102]: https://github.com/VladimirMarko/conaled/issues/102
[#106]: https://github.com/VladimirMarko/conaled/issues/106
[transfer contract]: agda-transfer-interface.md
[language direction]: ../language-direction.md
