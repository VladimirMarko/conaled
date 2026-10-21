# First Agda proof-transfer contract

The [contextual-J design record](contextual-j-design.md) preserves the
implementation experiments for #104, including rejected encodings, checked
constructions, author-interface friction, and alternatives still worth testing.

This is the interface decision for [#101], under [#100] and [#36]. It selects
one experiment: port transport over concatenation from agda-unimath into an
opt-in Lean-hosted identity fragment, interpret it in ordinary groupoids, and
retain finite-group labels in two action-family consumers. The selected `tr-concat`
handoff below is **not implemented**. Existing scalar interfaces supply
compiled authoring evidence; they do not supply higher semantics.

The baseline is conaled `5dbd73f` (the committed [reuse assessment]); Lean
4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. This decision
uses the [language direction] and the accepted [#96 assessment]. The approved
[#102] experiment requires an independent second-proof author for [#106].
The framework and first port may share an author; their implementers and
reviewers are ineligible for that independent baseline. The second author
must start in a fresh session, receive only the frozen public repository and
handoff, and work without inherited implementation context, coaching or API
repairs during the baseline. Archive the baseline before any assisted
correction, and label assisted results separately. A contaminated attempt
must be replaced by an unexposed author and, if its solution leaked, a new
scoped theorem; assisted retries cannot count as the independent baseline.
A broad library port is conditional on the technical and independent-author results.

## Implementation progress on #102

The typed contextual identity fragment is implemented for #104. The selected
Agda proof and its action consumers remain the #105 handoff; the independent
second proof remains #106.

- `SquareKit.Internal.PathTransport.Typed` supplies generated context, type,
  term, telescope and simultaneous-substitution derivations. Judgmental type
  and term conversion are separate from source identity. The same derivation
  is interpreted across supported models; constructor-recursive interpretation
  agrees with its model-parametric code.
- `SplitFamily` constructs split groupoid families, normalized sections and
  identities whose objects are actual fiber arrows. Identity reindexing is
  endpoint conjugation. `identityFiberEquiv` retains the arrow data.
- `GroupoidModel.Instance.fullModel` in `GroupoidSoundness` constructs every
  supported operation and law, including arbitrary finite dependent-tail J, strict reflexive
  computation and rebuilt-J substitution. `universeModel` uses explicit
  universe lifts for independently sized base objects, arrows and fibers.
- `Authoring.NamedCaller.pathInductionGeneralizingZQB` retains `z`,
  `q : y = z`, and `b : fiber x`. Its motive is `q = q`, with reflexive branch.
  `reflexiveApplication` is an actual source J derivation;
  `interpreted_beta` consumes generic source soundness. The additional
  `rebuilt_interpretation` case compares substituted and rebuilt source J
  terms after adding an earlier parameter.
- `Examples.TypedPathTransport` specializes source conversion and the named
  caller to the constructed groupoid model. `Examples.GroupoidTransport`
  retains the preliminary C₄ label/action checks; those action equations do
  not yet consume the selected Agda proof.

The author API includes named base points, `Motive.reflexivity`, and
`PathCommand` operations for application, reflexive computation and rebuilding.
Library definitions still manage raw context arithmetic and semantic code
casts internally. These helpers were developed by the framework authors;
their use does not establish independent-author usability. The
[design record](contextual-j-design.md) preserves the tested alternatives,
representation costs, and remaining frontend questions.

Run `direnv exec . lake build Examples.TypedPathTransport` for the new cases,
and `direnv exec . ./check.sh` for the full fresh-source check and audit.
There is no working `transportConcat` or `transport_concat_action` handoff yet.
No Agda proof or upstream Agda build is claimed by #104. The smooth-model
obligations below are unchanged. No SynthLean declarations have been adapted.

## Selected theorem and actual dependency boundary

Select `tr-concat` in
[`foundation-core.transport-along-identifications.lagda.md`][transport] at
agda-unimath `75518656f287c203b41cb7f71df46e02b987a084`, MIT. It states that
transport along a concatenated path agrees with successive transport. Its
proof eliminates the first path; the reflexive case computes. Port this
argument, rather than merely proving functoriality in the target category.
The translated theorem must be a derivation whose interpretation supplies the
consumer's equation.

Its declaration-level proof closure is small:

| Dependency | Required rule or computation |
| --- | --- |
| `Level`, `UU` in `foundation.universe-levels` | Two external universe parameters for base and fibers. |
| `Id`, `refl`, `ind-Id` in [`foundation-core.identity-types`][identity] | Intensional identity and based dependent elimination, with its reflexive computation. |
| `_∙_` / `concat` in that identity module | Defined by elimination on the first path, so `refl ∙ q` computes to `q`. |
| `tr` in the selected transport module | Defined by elimination, so transport at reflexivity computes to the argument. |
| `tr-concat` | Eliminate the first path with the second endpoint, second path and fiber element still generalized; reflexivity closes the motive after computation. |

This is the proof dependency closure, not the import closure of the whole Agda
file. That file also imports action-on-identifications and function types for
other declarations. A manual port need not import those other proofs. Native
Agda pattern matching supplies the eliminator; it is not an additional Lean
axiom. No inverse, function extensionality, univalence, truncation, HIT,
resizing, modality or crisp rule is used by this selected argument. There are
no internal universe operations in the proposed fragment: the Agda parameters
`A : UU l1` and `B : A → UU l2` become an external signature with one base type
and a family. This is an explicit specialization of the upstream schema,
not a model of Agda's whole universe hierarchy.

The original theorem permits arbitrary fibers. The first interpretation uses
set-valued families over groupoids. It therefore tests a restricted instance
of the theorem; a later groupoid-valued family extension requires more
coherence and is not implicit in this contract. The base can retain nontrivial
loops even though its fibers are sets. Internal identity between base points
must consequently carry data, not be Lean's proof-irrelevant `Eq`.

This theorem checks that a stabilizer's successive actions on a tangent fiber
compose correctly. It does not identify the tangent fiber or construct a
quotient. Those are the separate obligations of #99. We do not select all of
`Torsor-Group` or `PGloops`: their identity/equivalence and universe requirements
would make the first experiment depend on an unjustified general univalent
universe. The [reuse assessment] retains them as possible later blocks.

Source inspection establishes the dependency claim above. No Agda build is
claimed. Source versions, license and computation choices must remain in the
port's module documentation. Copying code requires retaining the upstream MIT
notice; a new Lean derivation following the mathematical proof must still
attribute the proof source.

## What an author can use today

The current APIs provide separate source derivations and reusable semantic
soundness:

| Existing module / declarations | Scope and relevance |
| --- | --- |
| `Internal.SyntheticScalar`: `MapExpr`, `Derives`, `Slope`, `product_rule` | First-order scalar syntax and explicit ring, nilsquare, Taylor and slope-uniqueness rules. No general type formation or internal identity. |
| `Internal.SyntheticScalar.GeometricSem`: `Assignment`, `map`, `sound`, `slope_sound`, `sound_parameters` | Interprets every scalar rule in the constructed geometric KL model. Function parameters denote sheaf morphisms, not arbitrary pointwise functions. |
| `GeometricProductRule`: `product`, `component`, `parameters` | Ordinary callers consume the interpreted theorem, including arbitrary sheaf-valued parameters. |
| `Internal.DependentFunctions`: `Ctx`, `Dep`, `Func`, `Ren` | Primitive base/family indices; function domains are the primitive base. It does not provide arbitrary dependent motives or general higher identity. |
| `Internal.DependentFunctions.SheafSem` soundness files | Existing dependent-function β/η and equality interpretation into sheaf maps; these are not proof-relevant path objects. Consult `DependentFunctionSheafSoundness.lean` for the actual namespaces and arguments. |

Here is a caller that compiles against the baseline interfaces. It uses an
existing derivation and its public interpretation, so no new library theorem
is needed for this issue. Save it as `/tmp/AvailableCaller.lean` and run the
commands in the handoff section.

```lean
import SquareKit.GeometricProductRule

open CategoryTheory
open SquareKit SmoothPresentationSite SmoothGeometricKL SmoothGeometricDerivative
open SquareKit.Internal.SyntheticScalar

example {n : ℕ} (f g : MapExpr n) : Slope (.mul f g) (productSlope f g) :=
  product_rule f g

example {J : GrothendieckTopology SmoothPresentationSite.Site}
    [Fact (Presieve.IsSheaf J SmoothPresentationSite.scalarData)]
    (ρ : GeometricSem.Assignment (J := J) 2) :
    derivative (GeometricSem.map ρ (.mul (.param 0) (.param 1))) =
      GeometricSem.map ρ (productSlope (.param 0) (.param 1)) :=
  GeometricSem.slope_sound ρ (product_rule (.param 0) (.param 1))

#check SquareKit.GeometricProductRule.parameters
```

The topology's scalar sheaf condition is exposed, not hidden as an arbitrary
KL or product-rule assumption. `slope_sound` consumes the checked construction
of the geometric derivative and all-rule soundness. The example still needs
explicit `MapExpr` constructors. It validates the separation of proof,
interpretation and consumer, not the desired final author ergonomics.

## Source proof interface: proposed declarations and rules

Use an explicitly typed derivation core with a small named-binder author
layer. Reuse the local separation of syntax, judgments and soundness; do not
extend `Derives : Expr → Expr → Prop` to hold path terms. Derivation evidence
may be a proposition, but object-language paths are terms of a syntactic type
whose interpretation can be a nontrivial arrow.

The following is a **declaration design**, not compiling Lean. Every name in
this section is new. `Ctx`, `Ty`, `Tm` stand for well-formed syntax with
explicit typing; `Sub Δ Γ` substitutes Γ's variables by terms in Δ. `Tm Γ A`
must be syntax, not a synonym for a semantic function or a Lean equality.
An implementation may use raw syntax with typing derivations internally,
provided the public typed interface and substitution equations are proved.

```lean
-- Proposed public sorts, indexed by an explicit signature S.
Ctx (S : Signature) : Type
Ty  (Γ : Ctx S) : Type
Tm  (Γ : Ctx S) (A : Ty Γ) : Type
Sub (Δ Γ : Ctx S) : Type
empty : Ctx S
ext (Γ : Ctx S) (A : Ty Γ) : Ctx S
idSub (Γ : Ctx S) : Sub Γ Γ
compSub (σ : Sub Δ Γ) (τ : Sub Θ Δ) : Sub Θ Γ
subTy (A : Ty Γ) (σ : Sub Δ Γ) : Ty Δ
subTm (t : Tm Γ A) (σ : Sub Δ Γ) : Tm Δ (subTy A σ)
weaken (A : Ty Γ) : Sub (ext Γ A) Γ
variable (A : Ty Γ) : Tm (ext Γ A) (subTy A (weaken A))
pairSub (σ : Sub Δ Γ) (t : Tm Δ (subTy A σ)) : Sub Δ (ext Γ A)
Id (A : Ty Γ) (x y : Tm Γ A) : Ty Γ
refl (x : Tm Γ A) : Tm Γ (Id A x x)
```

A signature initially names one closed base type `base : Ty empty` and one
family `fiber : Ty (ext empty base)`. In any Γ, reindexing `base` along the
unique empty substitution gives `A`; reindexing `fiber` along a term `x : A`
gives `B[x]`. These are syntactic families, not unrestricted host functions.
No source Π, internal function type, universe or function extensionality is
needed for the open theorem. Its binders are a telescope in the source
context, not a source function object. Host functions may construct syntax
uniformly, but cannot be inserted as internal functions by an escape rule.

Required type equality and term conversion use separate inductive judgments
`TyEq Γ A A'` and `TmEq Γ A t u`. They include equivalence, congruence,
substitution laws and J computation. Conversion transports typing along
`TyEq`. These are **judgmental** equality, distinct from `Id`. In particular
there is no equality-reflection rule or K/UIP rule for source paths.

Based `J` has the following exact mathematical signature. For Γ⊢A, Γ⊢x:A,
form the telescope Γ,y:A,p:Id A x y. Given a type C in that telescope and
`d : C[x/y,refl x/p]` in Γ, produce `J C d y p : C[y,p]`. Require
`TmEq Γ C[x,refl] (J C d x (refl x)) d`. C may itself be an identity type,
and Γ may contain arbitrary earlier parameters. Weakening, simultaneous
substitution and their composition must preserve this rule and computation.

For `tr-concat`, eliminating p must allow the later declarations z, q and b
to remain generalized. Supply a **derived telescope J** operation: a motive
can return a derivation in a finite dependent extension of the elimination
telescope, with that extension substituted in the reflexive branch. Prove it
from based J and contextual substitution, or implement its contextual rule
and validate it for all such telescopes in the model. Do not silently use
native Lean induction on a semantic arrow. If this derivation needs Π in the
chosen core encoding, that is an explicit design revision with Π formation,
λ/application and β soundness; it is not a license to use host functions as
internal Π. The preferred core keeps theorem parameters contextual.

Derived public operations and their required laws are:

```lean
-- Schematic types, with B[x] denoting the reindexed signature family.
transport (B : Ty (ext Γ A)) (p : Tm Γ (Id A x y))
  (b : Tm Γ B[x]) : Tm Γ B[y]
concat (p : Tm Γ (Id A x y)) (q : Tm Γ (Id A y z)) : Tm Γ (Id A x z)
transportConcat (B) (p) (q) (b) :
  Tm Γ (Id B[z] (transport B (concat p q) b)
                    (transport B q (transport B p b)))
```

`transport` and `concat` must be derived from J; their reflexive computations
must be derivable `TmEq`, not assumptions furnished by the interpretation's
caller. `transportConcat` must be derived by the upstream first-path
elimination, not added to the primitive rules. The named author layer must
elaborate the following proposed caller to that derivation:

```text
internal theorem transportConcat
    (x y z : A) (p : Id A x y) (q : Id A y z) (b : B[x]) :
    Id B[z] (transport B (concat p q) b)
            (transport B q (transport B p b)) := by
  path_induction p generalizing z q b
  reflexivity
```

This is a sketch, not an available tactic. The implementation may use named
Lean combinators instead of a parser, but its retained caller must bind names
and generalize the dependent tail without exposing indices, repeated shifts,
or model-specific proofs. A second proof author should only import the
fragment, declare a supported signature, and use those combinators.

## Model implementer and external consumer interfaces

The first model is **ordinary groupoids**, not the smooth site. Use Mathlib's
`CategoryTheory.Groupoid`, functors and natural transformations. Source
contexts interpret as groupoids, types as split families, and terms as
sections of the corresponding Grothendieck construction. The implementation
must choose and document its universe levels; a small context groupoid and
Type-valued fibers may yield constructions in the maximum or successor
universe. No resizing or univalence is required or promised.

The required concrete model contract, in schematic Lean declarations, is:

```lean
-- New declarations; proof fields specify primitive laws, not tr-concat.
structure SignatureMeaning (S : Signature) where
  base : Type u
  groupoid : CategoryTheory.Groupoid.{v} base
  fiber : base ⥤ Type w  -- a functor, hence coherent set-valued transport

structure Interpretation (S : Signature) (M : SignatureMeaning S) where
  context (Γ : Ctx S) : Type _
  contextGroupoid (Γ) : CategoryTheory.Groupoid (context Γ)
  substitution (σ : Sub Δ Γ) : context Δ ⥤ context Γ
  family (A : Ty Γ) : context Γ ⥤ Grpd
  term (t : Tm Γ A) : Section (family A)
```

Here `Grpd` is the bundled groupoid category and `Section F` means a functor
section of the total-groupoid projection, with its coherence. Their precise
universe parameters and split reindexing representation are implementation
work. The primitive base is a constant groupoid family; the primitive fiber
is discrete, induced by the functor `M.fiber`. Identity types are discrete
families of **arrows** in the interpreted type, reindexed by conjugation at
the endpoints. They are not Lean `Eq` of objects. For the set fibers, identity
is a discrete groupoid on equality witnesses; that is legitimate because
those fibers are sets, not because the base's identities are irrelevant.

The table defines the laws which must accompany those declarations. A record
listing them is only an interface; acceptance requires their constructed
instance and the derivation-recursive interpretation.

| Public proof obligation | Required content |
| --- | --- |
| `interpret_substitution` | Identity/composition for substitutions, type reindexing, section reindexing; chosen coherence with comprehension, variable and pairing. |
| `interpret_conversion` | Every `TyEq` / `TmEq` rule preserves interpretation. State whether chosen equalities are strict or specified coherent isomorphisms, then prove coherence; never use an arbitrary iso as definitional equality. |
| `interpret_Id`, `interpret_refl` | Arrow-valued base identity, identity arrow for reflexivity, natural under substitutions and endpoint arrows. |
| `interpret_J` | Construct dependent elimination and reflexive computation for every admitted motive and contextual tail, with substitution stability. |
| `sound` | Recursion on all well-typed derivations yields sections of the stated interpreted types. It must cover the complete supported grammar, not only the selected theorem. |
| `interpret_transport`, `interpret_concat` | Derived operations agree with functor action and groupoid composition, including parameter reindexing. |
| `transportConcat_sound` | Corollary of `sound` applied to the ported derivation, exposing its conclusion to ordinary Lean callers. |

SynthLean/HoTTLean [`Groupoids/Id.lean`][hottlean] at
`31133dd5b25226ea897f8aa5e2e43b61392459eb` is a source for arrow-valued Id and
endpoint conjugation. Its declaration-level trust audit remains required
before adaptation. Its checker, universe and older dependency stack are not
adopted. The existing local sheaf substitution code provides law patterns,
not this groupoid instance. No semantic claim above is discharged merely by
having an interface record.

The ordinary consumer should have this public conclusion (proposed name):

```lean
-- Uses a proved interpretation of transportConcat, not a new assumption.
transport_concat_action
  (C : Type u) [CategoryTheory.Groupoid.{v} C]
  (B : C ⥤ Type w) {x y z : C} (p : x ⟶ y) (q : y ⟶ z) (b : B.obj x) :
  B.map (p ≫ q) b = B.map q (B.map p b)
```

Native equality here compares elements of a set fiber **after** interpretation.
It cannot substitute for the source derivation. The consumer must also expose
`basePathEquiv : InterpretedId x y ≃ (x ⟶ y)` and prove it respects reflexivity
and concatenation. This equivalence is what permits the label-retention
checks below. An equation alone would not demonstrate a higher bridge.

## Missing operations and first transfer acceptance

The original interface decision identified the following prerequisite list.
The #104 core and model are now implemented as described above; the selected
proof, consumers and independent-author experiment remain the later handoffs:

1. Signature, typed contexts/terms/substitutions, Id and conversion judgments;
   simultaneous substitution, comprehension and their laws.
2. Based J with computation and substitution stability, plus the generalized
   dependent-tail operation used by the selected caller.
3. Derived transport and first-path concatenation; the ported derivation;
   named author combinators with a diagnostic for unsupported operations.
4. Split groupoid interpretation with arrow identities and all-rule soundness;
   comparison of derived transport with the declared set-family functor.
5. Ordinary consumer and the two finite-action cases below, in the normal
   build and exhaustive audit.

The original single-slice scheduling instruction is superseded by the approved
[#104] framework, [#105] first-proof/consumer port and [#106] independent-author
sequence. These remain prerequisites of the same bounded experiment; completing
the framework or first port alone does not complete it. Do not add a full HoTT
library first. If the selected core forces an unanticipated universe/Π requirement,
record the exact failed caller and revise the contract before expanding it.

For a concrete acceptance test, use the one-object groupoid of C₄ with labels
0,1,2,3 and composition corresponding to successive action. With left actions,
`p ≫ q` has label `q * p`; in additive C₄ this is `q + p`. Retain that convention
explicitly so a later noncommutative group is not accidentally reversed.

- The faithful family has fiber C₄ with translation action. For p=q=1 and
  b=0, the **interpreted source theorem** computes both routes to 2. Transport
  by 1 takes 0 to 1. The interpreted path for 1 differs from reflexivity,
  and all four labels remain pairwise distinct via `basePathEquiv`.
- The ineffective family has fiber `Fin 2` with trivial C₄ action. All
  transports act identically, while all four base loops remain distinct.
  Run the same derivation and same soundness theorem for this interpretation.
  Do not identify labels by equality of their fiber maps.
- Check general composable p,q and arbitrary b via the consumer theorem,
  reflexive computation, a renamed/substituted caller, and the agreement
  between composition and interpreted concatenation. These exercise the
  public rules rather than private syntax representation.

A pointwise proof obtained directly from `Functor.map_comp` may be used as
an independent expected result for statement review, but cannot replace the
source-to-consumer route. Reject a source model using Lean `Eq` for the base,
a `transportConcat` assumption in a model record, or examples which only
check identity loops. Ordinary groupoids demonstrate 1-dimensional isotropy;
they neither validate a univalent universe nor prove smooth semantics.

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

## Handoff and validation

**Runnable now:** use the baseline above, `.envrc` and pinned Lake files. Run
`direnv allow` once if necessary, then `direnv exec . lake build` to prepare
incremental imports and `direnv exec . lake env lean /tmp/AvailableCaller.lean`
on the displayed caller. `direnv exec . ./check.sh` performs the authoritative
fresh-source check and exhaustive audit. The reused definitions and theorems
are already public through `SquareApplications.lean`; no new Lean source is
added by this design issue. Keep caller output and review evidence outside the
source diff. Compiling the caller checks its present API use, not the proposed
higher declarations.

**Proposed next implementation:** create opt-in modules under
`SquareKit/Internal/PathTransport/` for `Syntax`, `Rules`, `Authoring`, `Proof`
and `GroupoidSoundness`, plus an ordinary consumer
`SquareKit/GroupoidTransport.lean` and a retained example
`Examples/GroupoidTransport.lean`. These are proposed paths, not current
imports. Reuse Mathlib groupoid/functor infrastructure. Export the completed
modules through the public entrypoint and preserve ordinary direct Mathlib
use without requiring the author layer. No new Lake dependency is selected.

The public names are the proposed source operations, `transportConcat`,
`sound`, `basePathEquiv` and `transport_concat_action` specified above. Permitted
model inputs are a groupoid and a lawful set-family functor. Permitted kernel
axioms remain exactly `propext`, `Classical.choice`, `Quot.sound` under the
existing audit. Additional principles must appear as supported source rules
with proved interpretations; none is required for this slice. No `sorry`,
external checker verdict, trusted export or audit exception is acceptable.

Statement review must inspect the source conclusion, its actual motive and
computation direction, the generalized binders, the interpretation of base
identity, universes, and both finite-action cases. Check that the conclusion
is uniform in parameters and that the consumer actually calls soundness.
Run the full fresh check after any Lean change and save ordinary Standards
and Spec reviews against the same immutable candidate.

One-time framework work is the supported fragment, interpreter, binder
handling and reusable soundness. Incremental proof-author work is to select
an upstream theorem whose dependencies fit that fragment, state its source
signature, translate the argument using named operations, and instantiate an
existing interpretation. A second author must receive a compiling first-port
module, source-rule inventory, unsupported-feature diagnostics and exact
validation commands. They should not reconstruct context plumbing or invent
a new semantics. A theorem needing Π, univalence or a modality creates an
explicit new interface requirement; it cannot silently borrow those from
ambient Lean or an external Agda library.

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
