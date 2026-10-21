# Agda proof transfer: implemented interface and frozen handoff

The #104 identity fragment and #105 first transfer implement the bounded
experiment selected by [#101] and [#102]. The retained source proof is
`trConcat`, following agda-unimath's first-path induction proof of `tr-concat`.
Its interpretation gives transport composition for arbitrary ordinary
groupoids and set-valued families. The independent second-author experiment
[#106] remains separate. Completing this port does not complete #102's
independent-author or cost evaluation.

Import `SquareKit.GroupoidTransport`. The public source names live in
`SquareKit.GroupoidTransport.Authoring`; the ordinary consumer is
`SquareKit.GroupoidTransport.transport_concat`. The compiling callers are
`Examples.AgdaTransferCaller` and `Examples.AgdaTransferModels`. The full source
implementation is opt-in: ordinary Mathlib callers need not construct source
syntax. No Lake dependency, Agda checker, or external proof verdict was added.

## Proof source and correspondence

The pinned source is agda-unimath
`75518656f287c203b41cb7f71df46e02b987a084`,
[`foundation-core.transport-along-identifications.lagda.md`][transport].
The [source notice](agda-transfer-source-notice.md) retains the MIT license,
source links and dependency inspection. No upstream Agda build is claimed.

| Upstream dependency | Implemented source construction |
| --- | --- |
| `Level`, `UU` | External base/family signature; no internal universes. |
| `Id`, `refl`, `ind-Id` in [identity types][identity] | Generated identity/reflexivity and finite dependent-tail contextual J in `Typed`. |
| `tr refl b = b` | `Authoring.transport` is J with empty tail; `transport_beta` is generated judgmental conversion. |
| `concat refl q = q` | `Authoring.concat` eliminates the first path with `z,q` generalized; `concat_beta` is generated conversion. |
| `tr-concat refl q b = refl` | `Authoring.trConcat` eliminates the first path with `z,q,b` generalized. Source beta and congruence convert reflexivity to the required branch type. |

This is the selected declarations' proof closure, not the upstream modules'
complete import closure. Other declarations in those modules use more
features. The base type and family are external parameters; the first
interpretation specializes arbitrary upstream fibers to sets. No internal
Π, universe hierarchy, univalence, function extensionality, truncation,
resizing, HIT, modality or crisp rule is supplied.

`TransferFrame` constructs the actual motive
`Id (fiber z) (transport (concat p q) b) (transport q (transport p b))`.
`TransferRootBranch`, `ConcatReindexBeta` and `TransferAssembly` construct the
reflexive branch using generated conversion. `Transfer.trConcat` applies the
resulting `PathCommand` to named arguments. No semantic arrow induction or
functor-composition theorem closes the source proof.

## Available author API

```lean
import SquareKit.GroupoidTransport
open CategoryTheory

example (C : Type u) [Groupoid.{v} C] (B : C ⥤ Type w)
    {x y z : C} (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
    B.map (p ≫ q) b = B.map q (B.map p b) :=
  SquareKit.GroupoidTransport.transport_concat C B p q b
```

The ordinary theorem accepts independent object, arrow and fiber universes.
`UniversalTransfer` uses the same source proof in the universe-lift model to
establish this wrapper. The smaller concrete model `Instance.fullModel` uses
a common universe, with explicit lifts behind `Instance.universeModel`.

For source authors, `BasePoint`, `Path x y` and `FiberElement x` contain actual
raw syntax and generated typing evidence. Given a generated context `hΓ`, the
named operations are `transport hΓ p b`, `concat hΓ p q`, and
`trConcat hΓ p q b`. They infer the named endpoints; callers supply no de
Bruijn shifts or model-specific coherence proofs. `Examples.AgdaTransferCaller`
retains a complete call, a weakening with an earlier parameter, an arbitrary
typed simultaneous substitution, a reflexive substitution preserving the
three-entry tail, and contextual beta. These are checked uses of the actual
source derivation.

For a new supported proof, `Authoring.Motive`, `PathCommand`, context extension,
variables and typed substitutions are available through the imported
`Internal.PathTransport` modules. The existing first port provides reusable
named operations, not a tactic parser or an Agda frontend. New motives can
still require explicit typed-context and annotation plumbing. The first
port's framework authors built that plumbing; independent usability is the
question reserved for #106.

## Supported source rules and limits

`Internal.PathTransport.Typed` is the supported calculus. `Syntax` and
`RawContext` provide erasure and capture-avoiding substitution; raw expressions
alone are not proofs. `CtxDeriv`, `TyDeriv`, `TmDeriv`, `SubDeriv`, `TelDeriv`
and separate `TyEqDeriv`, `TmEqDeriv`, `SubEqDeriv` are generated data indexed
by exact raw contexts/types/terms and model-parametric annotations.

Supported types are the primitive base, its primitive fiber at a base term,
and iterated identities. Rules include empty/extended contexts, variables,
weakening, simultaneous substitution and comprehension pairing; identity and
reflexivity; conversion; and J with arbitrary earlier context and finite
dependent tail. Type and term conversion have equivalence, congruence,
structural computation and substitution laws. Pairing congruence and J
motive/branch/argument congruence cover operations in a fixed context
presentation. Rebuilt-J substitution reindexes the type, fixed endpoint,
tail, motive and branch. Arbitrary changes of raw context presentation are
not a context-conversion API. The [#104 design record](contextual-j-design.md)
documents that boundary and the generated structural J forms.

The all-rule interpreter recursively interprets these derivations.
`typeSound`, `termSound` and `subSound` validate conversion; interpreter
agreement proves that the recursive result agrees with the indexed code.
A guarded conversion constructor carries a semantic coherence certificate
only alongside a genuine source type-conversion derivation. The public
constructor derives that certificate. A semantic equality alone cannot
produce source conversion or an identity term. Native annotation changes
must preserve the exact raw judgment.

Unsupported operations are rejected by Lean's elaborator, as retained in
`Examples.AgdaTransferDiagnostics`: `Expr.pi`, `TmDeriv.hostFunction` and
`TyEqDeriv.reflect` do not exist. This is an explicit supported-fragment
boundary, not a custom error-reporting parser. A proof requiring unsupported
formation or elimination must report a new interface requirement. It may not
insert an ambient host function or equality into the source language.

## Interpretation and consumers

`GroupoidModel.Instance.fullModel` constructs the model's operations and laws.
Contexts are groupoids, types are split groupoid families, and terms are
normalized sections. Base identity is a discrete family of actual arrows,
with endpoint-conjugation reindexing. Primitive fibers are discrete sets.
Contextual J is constructed for every admitted motive and tail, with strict
reflexive computation and rebuilt-J substitution. There is no `trConcat`
assumption in the model.

`SourceSemantics.interpret_transport_obj` identifies interpreted source
transport with `B.map p b`. `ConcatSemantics.interpret_concat_obj` identifies
source concatenation with `p ≫ q`. `TransferConsumer.consume` interprets a
generated source identity proof and extracts equality in the discrete fiber;
`UniversalTransfer.transport_concat` applies it to the retained `trConcat`
proof and named semantic inputs. The ordinary wrapper uses this route and
does not independently close its conclusion with `Functor.map_comp`.

The public `basePathEquiv` identifies an interpreted base identity element
with its arrow; `basePathEquiv_refl` and `basePathEquiv_concat` prove its
computation on the derived operations. `Examples.AgdaTransferModels` applies
the same source derivation to C₄ translation and to the trivial `Fin 2`
family. Labels remain distinct in both. Mathlib's one-object convention is
`p ≫ q = q * p`, hence additive label `q + p`. For translation, `p=q=1,b=0`
gives 2 along both routes; transport by 1 sends 0 to 1. Trivial action does
not identify base arrows.

Strict uniqueness of J extension is used only for pointwise discrete motives
in the operation comparisons. It is false for arbitrary groupoid-valued
motives; `Examples.PathTransportUniqueness` retains a checked counterexample.
The model's general J construction and source soundness do not assume that
false uniqueness claim. General source concat-code naturality is not a new
named wrapper theorem: the transfer uses an exact reindexed-beta factorization
through the original tail. Generic source J substitution remains proved.

## Relationship to #98, #99 and the full bridge

#98 can independently construct finite locally constant group sheaves,
torsor groupoids, restriction/descent, and the dual-extension equivalence.
Its public maps should retain labeled isomorphisms and explicit base-change
coherence. The ordinary one-object groupoid example is not a replacement for
nontrivial sheaf torsors, disconnected stages or effective descent.

Before #99 can claim to consume the higher proof, reconcile these exact
obligations:

1. Interpret the same source grammar and J in the smooth groupoid semantics,
   including restriction/base-change coherence. A groupoid at each stage
   alone is insufficient for descent of contexts, families and sections.
2. Identify source Id with the torsor quotient's actual isomorphisms, including
   locally varying and ineffective labels. Transport must agree with their
   action on the chosen fiber, not merely with isomorphism classes.
3. Construct the discrete inclusion preserving `R`, `D`, exponentials relevant
   to `R^D`, evaluation at zero, products and the existing KL map.
4. Use #98 to construct the pointed homotopy-pullback comparison with its
   boundary isomorphism, hence identify the chosen-lift tangent fiber.
5. Compare its transport with the classical quarter-turn derivative and the
   ineffective action. Instantiate the source theorem through the smooth
   interpretation to obtain composition compatibility of this action.

The selected transfer supplies the last step's reusable transport argument;
it does not prove the comparison maps. #99 may still deliver a useful direct
semantic comparison before smooth source soundness exists, but must label
that gap. Cohesive/crisp and broader Myers requirements remain open under
#36. #97's transverse pullback work is not a prerequisite of this experiment.

## Validation and independent-author handoff

See [the frozen author handoff](agda-transfer-handoff.md) for imports, commands,
permitted work and reporting requirements. Use the repository's pinned flake,
Lean toolchain and Lake manifest. `direnv exec . ./check.sh` runs the complete
fresh-source build and exhaustive proof audit. Allowed kernel axioms remain
`propext`, `Classical.choice`, `Quot.sound`; no audit exception is added.

The approved [#104]/[#105]/[#106] sequence supersedes the original single-slice
scheduling proposal. The framework and first proof may share an author. Their
implementers and reviewers are ineligible for the independent second-proof
baseline. That author must start in a fresh session using only the frozen
public repository and handoff, without inherited context, coaching or API
repairs during the baseline. Archive the baseline before assisted correction.
Contaminated attempts must be replaced by an unexposed author, and by a new
scoped theorem if its solution leaked. Assisted retries cannot count as the
independent baseline. No second theorem or theorem-specific helper was selected
or prepared during this port.

The [#104 design record](contextual-j-design.md) and
[first-port design and effort record](first-transfer-design.md) separate the
accepted framework baseline, additional first-port framework work, proof
translation, dependency inspection and debugging. They preserve checked and
rejected alternatives. The observed framework intervention is not an estimate
of independent translation cost; that requires the uncontaminated #106 run.

[#101]: https://github.com/VladimirMarko/conaled/issues/101
[#100]: https://github.com/VladimirMarko/conaled/issues/100
[#36]: https://github.com/VladimirMarko/conaled/issues/36
[reuse assessment]: higher-theory-reuse-and-outsourcing.md
[language direction]: ../language-direction.md
[#96 assessment]: myers-tangent-integration.md
[transport]: https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/foundation-core/transport-along-identifications.lagda.md
[identity]: https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/foundation-core/identity-types.lagda.md
[hottlean]: https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Groupoids/Id.lean

[#102]: https://github.com/VladimirMarko/conaled/issues/102
[#104]: https://github.com/VladimirMarko/conaled/issues/104
[#105]: https://github.com/VladimirMarko/conaled/issues/105
[#106]: https://github.com/VladimirMarko/conaled/issues/106
