# Shared meaning for a selected higher identity

The #359 client connects the existing reference-calculus proof translation to
selected semantic realization of its actual contextual target. The selected
result includes its context, family and section. Typing is checked separately
by reference soundness. Consequently the shared comparison does not mistake a
semantic value for a proof that an arbitrary judgment is valid.

## Client and observation

The source remains the independently specified client in
[`ReferenceHigherTheoryMaps`](../../Examples/ReferenceHigherTheoryMaps.lean).
Its `action` is dependent action of a section along the chosen higher binder
`h : Id(p,p')`. The section is declared initially and compiled to the existing
J-built certificate section. Its action is derived, not declared as an input.
The original object substitutions `sigma` and `tau` retain the later `q` and
`u` entries. Compiler templates separately expand the section declarations
and change the variable namespace; these two notions of substitution must not
be conflated.

The independent cubical observation is fixed by
[`CubicalFrozenHigherObservation`](../../Examples/CubicalFrozenHigherObservation.lean):
the selected second identity has integer observation one, while reflexivity
has observation zero despite the same endpoints. The underlying cocycle and
presheaf model is not a finite carrier or a universal higher model. This is a
bounded client in that existing model. The ordinary C4 control from #366
cannot supply this higher witness.

[`CubicalSharedAssignment`](../../Examples/CubicalSharedAssignment.lean)
builds an assignment into the actual twice-reindexed display, including the
selected higher identity and dependent q/u entries. Its two explicit chains of
lifted substitutions keep the original sigma/tau families. Only proved family
equalities are normalized; `retainedU` also retains the rooted-family section.
[`HigherSharedObservation`](../../Examples/HigherSharedObservation.lean)
reads the witness from the shared compiler's actual target, assigns that final
context and obtains `some 1`. It rejects `some 0` and reflexive replacement.
This closes the observation after both substitutions, rather than reusing the
old observation at the original input context.

## Local realization and actual target

[`SelectedIdJRealization`](../../SquareKit/Internal/DependentJudgments/SelectedIdJRealization.lean)
packages a quoted contextual expression together with its selected semantic
value. The semantic value and operations come from an independently supplied
`PathTransport.Typed.Model`. The local identity, reflexivity, substitution,
J, transport and dependent-action constructors derive their quotation laws
from those operations. J takes a typed motive, branch and arbitrary finite
dependent telescope. No constructor accepts the desired final client action
as a correctness hypothesis.

[`ReferenceHigherSharedMeaning`](../../Examples/ReferenceHigherSharedMeaning.lean)
builds `semanticTransport` and `semanticAction` from the retained inputs and
J-built section. Their quotations are the existing contextual transport and
apd expressions. `compiledActionCode` connects the original twice-substituted
compiler output to that local construction using the native naturality law.
That last connection is a retained obligation: generic template substitution
does not discover the client's object-level naturality theorem.

[`ReferenceSelectedMeaning`](../../SquareKit/Internal/DependentJudgments/ReferenceSelectedMeaning.lean)
uses a selected-data `Institutions.Setting`. Sentences contain the actual
context, type and term; models are environments for a fixed Id/J model; evidence
is a selected semantic value. This is not a new logical satisfaction relation.
Reference derivations certify typing separately. `sharedAction_typed` decodes
the actual shared proof and applies soundness with discharged declarations.

The proof map is the existing local-certificate transport, with its exact
encoded derivations retained. The realization map substitutes into the actual
`Contextual.Expression`, not a replacement phase AST. Both commuting laws
follow from local operation evaluation and the term substitution fold law.
`Compatible.comp` composes these same maps. `sharedAction_exact` identifies the
shared proof with the original compiler result; `selected_joint`,
`selected_proof` and `source_selected` compare its selected meaning with the
separately constructed semantic action. `selected_witness` also retains the
chosen higher binder after both original object substitutions.

Lean equality here compares the complete semantic values and commuting maps.
It does not turn object-language identity witnesses into Lean equality proofs.
The witness remains a term of the modeled identity family, and the observation
can distinguish terms with the same endpoints.

## Second use and dependent tails

[`SelectedIdJTail`](../../Examples/SelectedIdJTail.lean) exercises local J on a
two-entry dependent tail: a natural number followed by an element of
`Fin(n+1)`. The selected branch returns that chosen element. Actual quoted J,
identity substitution and two template substitutions preserve the selected
value two. The generic local J constructor permits arbitrary finite tails;
this checked application supplies an inhabited varying-tail boundary rather
than relying on the empty telescope. It is a set-model application, separate
from the main higher witness. The higher client's own later q/u entries are
retained in its original dependent display.

The second use shares the operation quotation laws and the selected-value
substitution comparison. It still needs its own environment, motive, branch
and selected observation. Nothing in the shared interface synthesizes those
mathematical choices.

## Native, separate and shared costs

| Route | Reused construction | Remaining obligations |
|---|---|---|
| Native | Existing reference proof transport, soundness, native Id/J semantics and client naturality | Discharge declarations, identify target syntax, normalize dependent families and observe the chosen section |
| Separate | Local quoted semantic constructors alongside the native proof compiler | Build semantic inputs and prove the final target quotation and selected comparison explicitly |
| Shared | The same local semantics and actual compiler, with compatible proof/realization maps composed by existing interfaces | Supply those local maps once; retain client-specific naturality, model admission, assignment and observation proofs |

The shared route derives identity and composition for its maps, including exact
selected-data agreement. It does not reduce the cubical family-normalization
work, prove a new model, or automate the dependent display assignment. Native
helpers can reuse the same fold and substitution laws without institutions.
For this client, the institution capability is an assembly interface with a
common selected meaning, not an alternative identity theory. The separate
route remains useful when no downstream client needs that assembly.

A full model morphism would require preservation across contexts, families,
terms and all model operations. Here the underlying model is fixed and only
expressions/environments are translated. Adding those stronger morphism fields
would impose obligations unused by this comparison. Conversely a quotient by
endpoint equality would lose the frozen observation. These are reasons for
the bounded interface, not evidence that full model maps or another semantics
are unsuitable elsewhere.

## Execution and limits

Reference proof translation and contextual syntax substitution construct actual
syntax. Semantic decoding is explicitly noncomputable: contextual index tests
and presheaf sections are not presented as executable machines. The final
integer observation has a mathematical computation law; the work does not
claim an executable compiler for arbitrary cubical sections. No runtime
representation of every semantic object is required by this client.

The development adds a selected semantic comparison; it does not establish
arbitrary-fullG semantics, equality reflection, a reverse compiler, a joint
smooth/higher model, or the quantified Myers source interpretation left open
by #366. Wider source/model admission remains under #289/#290. Original #355
and #356 clients remain regressions. This is checked construction evidence,
not a fresh-author experiment or a measured productivity advantage; scaling
measurements belong to #358.
