# The frozen dependent higher-identity test

Investigation for [#316](https://github.com/VladimirMarko/conaled/issues/316),
under #289, with the current successor status recorded below. The frozen
[external memo](dependent-coherence-discovery/292-external-memo.md), Agda source
artifacts and historical author-trial submissions are unchanged.

## Current Lean result and remaining scope

The accepted #321/#334 candidate
`45e12129182e170202a3febbc512396e2e71f0d7` supplies the bounded Lean higher
interpretation that was missing from the original #316 investigation. The
[cubical construction record](cubical-model-construction.md#final-construction-and-acceptance-mapping)
links the constructed dependent presheaf model, selected lawful fillers,
constructor closure and marked-identity eliminator. Contextual J covers
arbitrary admitted motives and finite dependent source tails, with strict
beta and substitution.

The [frozen consumer](../../Examples/CubicalFrozenOrdinaryAction.lean) uses an
actual selected higher identity in that model. Its interpretation retains the
original eight-binder input, both frozen substitutions, the selected dependent
pair and certificate, and the certificate's dependent action. The
[source-action connection](../../Examples/CubicalFrozenActionSource.lean)
identifies the original ordinary `ap_T` after assignment. A typed identity
joins that selected action to pointwise cubical action; the resulting
conjugation cube has the source action, selected h and actual beta endpoint
faces. Its action face has observation one and cannot be erased. The
certificate action `apd_η(h)` remains a separate preserved output.

The nonconstant lower observation uses the existing
[groupoid source interpretation](../../Examples/FrozenMemoRealizationExamples.lean),
with value `q + (p + b)`. The contract permits that observation and the higher
observation to use different models. No new cubical monodromy or complete
classification of the cocycle model as `K(ℤ,2)` is inferred.

The Lean higher-consumer gate has therefore passed through the selected #321
fragment. Its types require selected lawful providers, and its universe levels
are metatheoretic. Unchanged external Agda reuse still requires a
judgment-preserving translation. Internal universes, Glue/univalence, HIT
eliminators and cohesive or smooth geometry remain outside the advertised
fragment.

The separate [strict two-groupoid construction](strict-two-groupoid-checkpoint.md)
for #322/#336 supplies higher families and sections with their cell data,
Grothendieck extension, open identity, coherent rooted contraction and stable
Sigma. Its contextual J is constructed for every admitted motive and finite
dependent tail, with whole-section beta and substitution; it does not assume
Pi closure to derive J. The #336 coherence helper uses the proved faithful
observation to reconstruct laws from constructed operations and a coherent image, retaining the dependent
boundaries.

[`sourceIdentityFiberAction`](../../SquareKit/Internal/PathTransport/TwoFamilySourceIdentityFiberAction.lean)
connects actual ordinary source J-action to identity-fiber action. Its
singleton-object hypothesis concerns objects of the path fiber, not its
arrows. The original B²ℤ frozen input discharges that hypothesis while keeping
its integer-labelled higher arrows. The
[selected-source conjugation](../../Examples/TwoFamilySelectedSourceConjugation.lean)
uses the original fixed transport, beta section and selected h; the
[frozen specialization](../../Examples/TwoFamilyFrozenSourceConjugation.lean)
retains the actual source action value through its proved endpoint-type
conversion. The normalized witness observation retains the original h and
computes its integer label. These constructions use the same source action and
original substitution evaluations as the cubical route; `apd_η(h)` remains a
separate output.

Candidate `574bfa2af3d5c31cc831749d056ff4b102ff1b31` passed all 1,786 modules,
the exhaustive proof audit, immediate candidate verification, and independent
Standards and Spec review for #322/#336. This supplies a second constructed
interpretation of the bounded frozen higher client. It does not
extend the admitted source language to universes or higher inductive types.
Final #235 integration acceptance is a separate gate. None of these results
retroactively adds a higher arm to the frozen #320 trial or establishes human
usability or comparative productivity.

## Original investigation and source test

The remainder records the #316 study at baseline
`9b0a0fe143c6f97f399632d4bb34a179db012181`. Its construction proposals and
statements about missing Lean infrastructure describe that baseline. The
successor status above supersedes those historical adoption conditions.

The generic argument has a source derivation using inductive identity with
judgmental J computation. Its two dependent substitutions include `w` and
`apd_η(h)`, with the transported source of the latter. A separate instance
connects the same derivation to a nontrivial second identity in `K(ℤ,2)`;
an integer observer distinguishes the selected identity from reflexivity.
The circle's integer cover supplies the nonconstant transport case. These
are source-theory results, checked by Agda. The original Lean construction
prerequisite is specified below, together with the direct higher-groupoid
alternative to the cubical programme.

## Feasibility assessment at the original baseline

The required fragment has a terminal context, dependent context extension,
simultaneous substitutions, Σ, intensional identity, reflexivity, and J with
its reflexive computation and substitution laws. `A` and `B` are schematic
parameters. No object-language universe, univalence, sphere eliminator or
modal operation occurs in the generic argument. Contextual J must cover
arbitrary admitted motives and finite dependent tails; restricting its motive
to the one used for transport would change the contract.

| Route | Semantic existence and scope | Mechanization and construction cost | Assessment for this test |
|---|---|---|---|
| Direct strict higher groupoids | Warren's Theorem 7.1 interprets intensional Π/Σ/Id; §§3, 5–6 construct extension, open identity and elimination. | Need higher families, sections and their Grothendieck construction, then all-motive J. A finite dimensional restriction needs a closure proof. | Leading smaller construction candidate. It does not require cubical primitives. |
| Kan fibrations, then local universes | Lumsdaine–Warren Theorem 4.2.2 and Examples 4.2.5 apply to the Kan model structure; Theorem 3.4.1 supplies strict stability. | Need the full comprehension category, LF representations and weakly stable constructors in Lean. The local Type-family example does not construct these for Kan fibrations. | Credible alternative with a real strictification benefit: arbitrary filler choices do not themselves commute strictly with reindexing. |
| Chosen simplicial universe | Kapulkin–Lumsdaine Theorem 2.3.4 supplies constructor closure for a small Kan-fibration classifier. | Need the classifier, chosen pullbacks, path-factorization/lifting and an interpretation of the selected judgments. | Credible coherence route, but a global classifier is additional work for schematic `A,B`. |
| Direct fibrant cubical families | CCHM §8 supplies presheaf semantics; §9.1 distinguishes strict identity from Path. | Need dimension substitutions, restrictions and stable composition/fibrancy; strict Id closure and rule soundness still require construction. | Coordinate with #321, which also owns source compatibility. A full Cubical Agda language is not necessary for #316. |

Sources: [Warren](https://mawarren.net/papers/crmp1295.pdf),
[Lumsdaine–Warren](https://arxiv.org/pdf/1411.1736v2),
[Kapulkin–Lumsdaine](https://arxiv.org/pdf/1211.2851v5),
[CCHM](https://arxiv.org/pdf/1611.02108v1).

These routes have different size assumptions. The cited simplicial classifier
theorem uses an inaccessible cardinal; its internal-universe corollary uses
two. That is not a lower-bound theorem about this universe-free fragment.
Local universes separate coherence from an object-language classifier.
For a direct construction, small cell carriers and a larger collection of
such structures can occupy separate Lean universes. Proving closure remains
necessary; simply writing universe-polymorphic records does not establish it.
CCHM's constructive metatheory is also not automatically a proof of
compatibility with Agda's variant of the rules.

One apparently small alternative fails the observation. Garner's
*two-dimensional models* concern a theory whose `Id-disc2` rule identifies
every second identity with reflexivity. “Two-dimensional” there counts the
semantic category's dimensions, not the required homotopy dimension of a
closed type. That theory cannot retain the memo's `h`. This excludes that
particular truncation, not strict 2-groupoids as closed semantic types.
[Garner, §2.3, Table 2](https://arxiv.org/pdf/0808.2122v2).

The decision is **investigate the direct higher-groupoid construction for the
bounded fragment**, retaining the Kan and cubical routes as alternatives.
This is based on the required operations and computation rules, not an attempt
to keep existing source annotations. It is not a claim that the direct route
has been constructed or that its host encoding cost has been measured.

## Artifacts inspected at the original baseline

The baseline is `9b0a0fe143c6f97f399632d4bb34a179db012181`.
`lake-manifest.json` pins Mathlib and its tooling; it does not declare an
integrated cubical model. The concrete
[split families](../../SquareKit/Internal/PathTransport/SplitFamily.lean)
have objects and coherent arrows, and the
[groupoid model](../../SquareKit/Internal/PathTransport/GroupoidSoundness.lean)
constructs contextual J. Its identity family is discrete. The
[algebraic two-loop language](../../SquareKit/Internal/TwoLoop.lean) retains
2-cell labels but has no dependent family or J. Neither becomes a dependent
higher model by combining their examples. The three independent
[architecture assessments](dependent-architecture-reassessment.md) and
[#292 report](dependent-coherence-comparison.md) are starting evidence,
not substitutes for this distinction.

The pinned HoTTLean tree at
`31133dd5b25226ea897f8aa5e2e43b61392459eb` was inspected through its recursive
Git tree and selected semantic files. `FunctorOperation.IdObj` explicitly
uses `Discrete` on a hom type. Its generic Hurewicz machinery is useful:
normality and uniformity separate reflexive computation from substitution
stability. The concrete groupoid inhabitant cannot realize the selected
second identity. Adapting that machinery to another cylinder and classifier
would require new inhabitants of those hypotheses; renaming the interface
would not supply them. No wholesale code import was made.
[Pinned Id](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Groupoids/Id.lean),
[pinned Hurewicz construction](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Model/Unstructured/Hurewicz.lean).

The supplied [checkpoint inventory](../history/orbifold/agda-checkpoints/README.md)
was read before extraction. The experiment uses Myers checkpoint 22's
Cubical v0.9 at `b150186d2544e7efeddd31e5d14a8b9ecbb100f7` and its compiler
kit pinned to Agda 2.8.0.2. This is a new, smaller source closure, not a fresh
check of the full Myers or Kock development. Kock remains a separate safe,
`--without-K` source with explicit geometric assumptions. Neither its
conditional proofs nor Myers's crisp/cohesive geometry are claimed absent.

## Source derivation and transported types

The sources are in
[experiments/dependent-higher-identity](../../experiments/dependent-higher-identity/README.md).
`FrozenMemo.agda` imports `Cubical.Data.Equality.Base`, whose equality is the
inductive type from `Agda.Builtin.Equality`. Its `J` admits every well-typed
motive in the declared universes and computes at reflexivity by pattern
matching. `j-beta` checks that computation. These are Agda identities in
`Type`, not Lean's proof-irrelevant `Eq` in `Prop`.

Contexts are dependent records with exactly the memo's components. Their
extension is ordinary Agda dependent record/Σ extension; substitutions are
functions on those records. Family reindexing is composition, term reindexing
is application, and composition is function composition. Record projections
and function reduction establish both projection laws and repeated
substitution for these contexts. This shallow source realization does not
claim a new general syntactic soundness theorem.

With `tr = Eq.transport`, `v p q u = tr B q (tr B p u)` and
`η refl refl u = refl`. The pair is a genuine Σ term:

```text
w(p,q,u) : Σ(v:B(z)). Id(v,tr_B(p·q,u)).
K(q,u,p) = Id(v(p,q,u),tr_B(p·q,u)).
apd-η(h,q,u) : Id(tr_K(h,η(p,q,u)),η(p′,q,u)).
```

`first-w` and `first-apd` apply `σ` to these expressions. The latter has type

```text
Id(tr_(λ p.K(r,u,p))(h,η(ℓ,r,u)), η(ℓ′,r,u)).
```

`second-w` and `second-apd` apply `τ`, producing

```text
Σ(v:B(x)). Id(v,tr_B(ℓ·k,u)),
Id(tr_(λ p.K(k,u,p))(h,η(ℓ,k,u)), η(ℓ′,k,u)).
```

`w-twice` and `apd-twice` compare those terms to the independently defined
direct assignment `σ∘τ`. Both comparisons type-check by reflexivity after
substitution, including the transported type. They say nothing about equality
of arbitrary inhabitants of that type.

For `B(y)=Id_A(x,y)`, `T(p)=tr_B(p,refl)` and `β(p):T(p)=p` are defined by
identity elimination. `conjugation` proves, for any endomap with such a
pointwise comparison,

```text
β(p)⁻¹ · ap_T(h) · β(p′) = h.
```

Its reflexive branch is inverse cancellation, so endpoint comparisons are
not suppressed. `PathFamily.observation` specializes to `p=p′=refl`.
`PathFamily.input` supplies `ℓ=ℓ′=k=refl`, `u=refl`, and an arbitrary `h`;
the retained `w` and `apd` are obtained through the two substitutions.
There is no requirement that `apd-η(h)` itself be nontrivial.

## A nontrivial higher instance of that derivation

`HigherWitness.agda` chooses `A=coHomK 2`, the library's `K(ℤ,2)`, with its
specified basepoint. Two pointed equivalences `K_n ≃ ΩK_(n+1)` give a pointed
path from `(ℤ,0)` to the double Path loop space. The library's `PathIsoEq`
and its reflexivity comparison convert each loop layer to inductive identity.
The resulting `double-identities` retains the basepoint comparison, not just
a bijection of unpointed carriers.

Consequently `decode : ℤ → Id_Id(refl,refl)` and `encode` in the opposite
direction satisfy `encode(decode n)=n`, and `encode(refl)=0`. Set
`h=decode 1`. Then `encode(h)=1`, and `h-not-refl` reduces any proposed
identity `h=refl` to `0=1` in the integers. This proves nontriviality in the
same dependent source theory used by the generic argument.

The instance then applies `w-twice`, `apd-twice`, and `PathFamily.observation`
to this `h`. `observation-detects-one` proves that the observed conjugate has
integer observation 1. `erasure-rejected` rejects replacing that conjugate
by reflexivity. Thus the detector is attached to `ap_T(h)` with its endpoint
comparisons; it is not an unrelated algebraic two-loop expression.

The parameter construction uses the Cubical library's homotopy theory,
univalence and truncation infrastructure. Those are requirements of this
particular external witness construction, not additional premises of
`FrozenMemo`. A Lean model could supply a different pointed parameter, such
as `B²ℤ`, without adding those constructors to the admitted source language.

`Monodromy.agda` uses the circle's integer cover. Under the same two
substitutions, `ℓ=1`, `k=2`, `u=0` gives value 3, while replacing `ℓ` by
reflexivity gives 2. The checked expressions include the dependent witnesses
and their repeated-substitution comparisons. This realizes the memo's
integer action in an external dependent theory. The existing Lean groupoid
results remain valid evidence at their weaker truncation level.

## Original direct-construction prerequisite

The following is a proposed Lean construction, with a calculable first test.
It is not a record of assumed model laws. Call its required theorem
**strict two-groupoid dependent identity soundness**. Its input is actual
small strict 2-groupoids and strict higher functors with the transformation
data needed for families. Its output is a constructed interpretation of the
above fragment. The admissible families must include the representable path
family and must be closed under reindexing, context extension, Σ, and Id.
If contextual J is derived using Π, that closure must be constructed too.

A family over a base with a 2-cell `α:f⇒g` has more data than the current
`Γ ⥤ Grpd`: `F₂(α)` is a transformation between the fiber functors.
For extension objects `(x,a),(y,b)`, an arrow is `(f,u)` with
`u:F(f)(a)→b`. With the orientation used here, a 2-cell from `(f,u)` to
`(g,v)` is `(α,ρ)` where

```text
ρ : u ⇒ v ∘ F₂(α)_a.
```

Composition must preserve that boundary, including the whiskering and
interchange equations. A section likewise needs its 2-cell component with
this boundary. Substituting host equality for `ρ` before proving that the
fiber is locally discrete would discard the required interpretation.

The first concrete test is `A=B²ℤ`: one object, one 1-cell, and integer
2-cells, with both compositions addition. For `B(y)=Id_A(x,y)`, its fiber is
the one-object groupoid with arrows ℤ. The base 2-cell `m` acts on this fiber
by the natural transformation whose component is `m`; commutativity supplies
naturality. The total path family has one object, arrows `a:ℤ`, and a 2-cell
from `a` to `b` with base component `m` precisely when `a=b+m`.
The unique required component is `m=a-b`. This calculation identifies where
the second identity enters dependent extension.

It also rejects a tempting implementation. If the transformation component
is erased, only equal arrows can be related. And a *strict natural*
contraction from the constant functor on this total path family to its
identity functor cannot exist: its single component `c` would require
`c=a+c` for every `a`; take `a=1` and cancel `c`. A contraction with coherent
2-cell witnesses can exist, using the displayed difference. Therefore the
ordinary groupoid proof cannot be lifted by changing carrier names and
retaining equalities for all naturality squares. This is a specific missing
higher coherence construction, not an impossibility of the model.

After that test, construct J for an **arbitrary** admitted family `D` over
the identity context and branch `d` over reflexivity. At objects, the
candidate is transport of `d` along the canonical contraction. On arrows
and 2-cells it needs the square and triangle pastings from the contraction
and the section `d`. The outstanding theorem is that those pastings give a
section, compute to `d` on the reflexive context, and commute with all base
substitutions, including lifted substitutions through finite dependent tails.
Merely establishing the object formula or its value at `B²ℤ` does not prove
this theorem. Nor does a field named `J` with these equations.

Warren supplies an existence route, not a checked finite-dimensional package
here. Restricting the higher construction to 2-truncated carriers must be
proved to preserve extension, open identity, and all these motives and
pastings. Identity 3-cells may be represented by metatheoretic equations
only after that restriction is justified. The selected integer 2-cells must
remain data. The source's higher identity comparison is compatible with
this truncation: it needs a third identity witnessing the correct equality,
not two distinct third identities.

This isolates why the remaining work is substantive. Existing ordinary
family records cannot even express `F₂(m)`, and the strict-contraction
shortcut fails on the chosen parameter. The new source test supplies the
consumer independently of that representation, so implementing only the
numerical calculation cannot pass it. A full Lean reconstruction is not
claimed justified by the inspected code or by external checking.

## Original continuation and adoption conditions

[#322](https://github.com/VladimirMarko/conaled/issues/322), under #289, owns the following
strict higher-groupoid milestones. #321 owns the separate cubical-calculus
and source-compatibility route; these alternatives share the frozen consumer
without assigning the direct construction to the cubical programme:

1. Construct the finite-dimensional family and section representation,
   Grothendieck extension and reindexing. Prove the `B²ℤ` path-family
   calculation above and its canonical coherent contraction. Establish
   closure under the intended dimension restriction; do not infer it from
   Warren's full theorem.
2. Construct open Id and arbitrary-motive contextual J, with β and
   substitution. Include Σ or a justified equivalent interpretation of `w`
   as an object-language dependent pair. Prove the composition equations
   on section components, not just their object projections.
3. Interpret the declared judgments, then the retained generic derivation
   and both substituted terms. Supply the integer detector in that model,
   retain nonconstant transport, and reject higher erasure. A hand-reproved
   target equation or an Agda success receipt does not replace interpretation.

If #321 selects the cubical route instead, the corresponding first prerequisite
is constructed fibrant families with reindexing/comprehension and **strict
inductive identity**, or an explicit sound translation of that Id fragment.
The admitted rules must match the actual consumer. CCHM Path alone has only
propositional J computation; the supplied library's inductive equality and
`PathIsoEq` show a source solution, not a Lean implementation of it.
[Agda's versioned rule reference](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html).
No crisp-context or smooth geometry rule is needed by this consumer.

For #318, the direct route has no demonstrated need for local universes or
right splitting. The Kan alternative has a strictification use, but its
higher full-comprehension/LF/weak-stability hypotheses must first be
constructed. Chosen-universe closure is a different obligation. For #315,
the source pair and transported `apd` types are the interpretation contract;
annotation equality across unrelated presentations is not required. For
#319, nothing here constructs a context-varying internal setting. For the
original #320 freeze, only the declared lower-truncation observations were
available in Lean. The accepted #321 result supplies later higher evidence
without changing that frozen trial or its declared comparison.

The original recommendation was to retain the external source test as partial
evidence and investigate both successor constructions. Its rejection of the
discrete-identity, strict-contraction and Path-computation shortcuts remains.
The accepted #321 and #322 constructions above discharge the selected
higher-consumer gate in their respective fragments. Ordinary-author cost claims
remain separate. This work
does not resume #107, select #108's theorem, or activate #260.

## Statement review and validation

The statement review checked the quantifier order and universes in the generic
argument, both substituted transported sources, the orientation of `β⁻¹`,
and that `h` is an inhabitant of second **inductive identity**. The higher
observer has a basepoint comparison proving `encode(refl)=0`; an unpointed
carrier equivalence alone would not justify the negative control. The
specialized observations consume the generic `observation`, `w-twice`, and
`apd-twice` declarations. Neither a supplied `h≠refl` assumption nor a
postulate replaces their instance proofs.

The experiment README and machine-readable validation record contain the
reproduction command, source hashes, checked import closure, compiler identity
and trust boundary. No integrated Lean theorem, host axiom, proof-audit
exception, toolchain change, or claimed Lean build result is introduced by
these Agda files. Independent Standards/Spec review and final candidate
validation are recorded in the implementation handoff.

The [component acceptance record](dependent-foundations-validation/reviews/316-review.md)
retains the exact reviewed candidate, both independent reports and matching
validation evidence. Final orchestration acceptance is a separate gate.
