# Guarded dependent-authoring repair

This implements the bounded migration approved for
[#107](https://github.com/VladimirMarko/conaled/issues/107). The initial
[comparison](dependent-congruence-resumption.md) remains evidence of why merely
retaining a fixed legacy operation template did not solve freshly reconstructed
operations. The implementation retains the left-path recipe and completes the
known associativity argument through guarded source judgments. It does not
repair every legacy `Typed` presentation or provide an Agda frontend.

## Mathematical result and caller boundary

`ThreePaths.associativity` accepts four typed endpoints and three arbitrary
composable paths. Its result is a source term of

```text
Id (Id A x w) (leftConcat (leftConcat p q) r)
                 (leftConcat p (leftConcat q r)).
```

The proof eliminates the first path. The remaining declarations are the
explicit dependent tail `z, q : y = z, w, r : z = w`. The branch is constructed
by source computation and congruence from reflexivity. The implementation does
not assume associativity, specialize the input paths to reflexivity, or insert
a groupoid proof into the source calculus. The full arbitrary-input caller is
[GuardedLeftAssociativity](../../Examples/GuardedLeftAssociativity.lean).

`Tm.leftConcatSub` compares an object-substituted operation with a freshly
constructed operation on the substituted arguments. Its inputs are the five
ordinary term judgments and a typed substitution. `Equal.leftConcat` propagates
generated source argument equalities through the recipe. Neither asks the caller
for equality of model-indexed annotations. The
[authoring examples](../../Examples/GuardedLeftAuthoring.lean) exercise fresh
substitution, repeated fresh substitution, and argument congruence.

This moves bookkeeping out of these callers. It does not eliminate the internal
proofs of dependent context conversion. The framework proves display-map
squares, lifted substitution laws, root-map expansion, and comparison of the
fresh motive and selected branch. Those are visible implementation obligations
rather than additional fields for ordinary theorem authors to fill in.

## Reusable mechanisms and admitted theory

The source judgments use the existing named
`Contextual.TelescopePresentation.theory`. This extends the guarded contextual
theory with explicit finite-telescope presentation equations already interpreted
by `TelescopePresentation.model`. In particular the proof uses the existing
`rootTailDef`, `pathTailDef`, `pathTailMapDef`, `branchSquare`, and
`reindexBranchDef` rules. No new object-language axiom, raw assumption, primitive
constructor, or semantic model law was added for associativity.

The reusable mechanisms are:

- `Presented.eliminate` and `Presented.beta`: build J from a mathematically
  stated motive and branch over an explicit finite dependent tail, generating
  primitive root-context conversions internally.
- `Presented.map`, `projection`, `termSquare`, and `typeSquare`: construct and
  compare substitutions through arbitrary presented tails.
- `SourcePath.substitute`, `ReflexiveRoot.under`, and `PathArguments.under`:
  transport a typed path, its established reflexive-root equations, and its
  argument comparison through dependent binders.
- `Tm.leftConcatSub` and the imported transport substitution laws: connect
  substituted operations to fresh constructions. These are theorem-specific
  instances of the source substitution/congruence mechanism, not a promise that
  every future named recipe normalizes automatically.
- `Tm.evaluates`: recover the value of the actual source expression from guarded
  soundness after identifying its context and family in a model.

The general engine still permits hypotheses which need not be conventional
well-formed declarations. A source derivation is interpreted conditionally on
all its source hypotheses holding. The repair adds no reverse translation,
equality reflection, or new adequacy theorem for unrestricted assumptions.

## Transport-composition reuse

`LeftTransportComposition.Inputs.composition` accepts arbitrary `p : x = y`,
`q : y = z`, a dependent family `B` over `Γ.A`, and `u : B(x)`. It constructs

```text
Id (B(z)) (transport (leftConcat p q) u)
            (transport q (transport p u)).
```

The proof again eliminates the first path, now retaining the dependent tail
`z,q,u`. It reuses `Presented.eliminate`, `ReflexiveRoot.under`,
`PathArguments.under`, and fresh left-concatenation substitution. Existing
transport typing, computation, and substitution derivations are imported from
the contextual theory. Lift composition and identity laws normalize the
reindexed dependent family; the author does not supply those conversions.

The [ordinary caller](../../Examples/GuardedLeftTransportComposition.lean)
spells out the transport endpoints for independently supplied `Γ,A,B,x,y,z,p,q,u`.
Its two substitution cases distinguish constructing a fresh certificate from
reindexing the original certificate to the fresh motive. Both are typed;
equality of their selected proof terms is not asserted. `Frame.beta` does retain
the computation equation for the constructed certificate and its selected root
branch. `certificate_evaluates` applies soundness to that exact source term.

The legacy first proof is retained. The new proof preserves its first-path
strategy and mathematical statement. This repair does not prove equality of
the new transport certificate with the legacy certificate in every model. That
is distinct from the checked selected-path comparison for concatenation below.

## Interpretation and retained clients

`LeftSemantics.Groupoid.eval_composite` identifies this left-path recipe with
path composition for arbitrary ordinary groupoids, contexts, sections, and
source expressions evaluating to those inputs. Its proof follows the selected
first-path J operation. `recipe_frozen` identifies the resulting path section
with the legacy `Authoring.concat` interpretation. This is equality of selected
meanings in that model, not equality of syntax or derivation objects and not a
general translation into `Typed`.

`associator_evaluates` interprets `ThreePaths.associativity` through guarded
soundness and identifies its two endpoints with the two composite sections.
The conclusion retains an exact equation for evaluation of the source
associator to its selected higher witness. It does not replace that witness
with a direct target associativity proof.

The C4 consumers instantiate arbitrary three labels in both faithful and
ineffective action models. The checked `1,2,3` examples retain label `2` at both
endpoints. The concatenation consumer also distinguishes labels `1` and `0`
under ineffective action. Observing only fiber action would lose that
information. Ordinary groupoid identity fibers are discrete; these examples do
not establish analogous uniqueness of higher witnesses in arbitrary higher
models.

The legacy API, original first source proof, direct and mixed clients, and
faithful/ineffective observations are unchanged. The #106 archive is unchanged.
No fresh theorem for #108 was selected, ported, or prepared during this repair.

## Statement review, diagnostics, and effort

The statement review checked the quantifiers and the routes through the code:

| Claim | Scope checked | Caller exercising it |
| --- | --- | --- |
| Left concatenation | J eliminates the first path, with dependent `z,q` tail and retained `q` branch. | Source typing, beta, and ordinary-groupoid selected-recipe evaluation. |
| Fresh substitution | Arbitrary source contexts, endpoints, paths, and typed object substitution; the result names the fresh recipe. | Repeated fresh-substitution caller and associativity branch normalization. |
| Associativity | Arbitrary `p,q,r`, all four dependent tail declarations, generated application to caller arguments. | Explicit source type in `Examples.GuardedLeftAssociativity.source`. |
| Interpretation | Same source derivation; assumptions validated before applying soundness; actual evaluated witness retained. | General groupoid theorem and faithful/ineffective labeled C4 examples. |
| Transport composition | Arbitrary dependent family, element at the initial endpoint, both paths, and retained `z,q,u` tail. | Ordinary caller, fresh/substituted motive callers, and exact certificate soundness. |
| Argument comparison | Source lookup/computation laws through each dependent binder. | `PathArguments.under` at every associativity argument. |

The retained
[wrong-endpoint diagnostic](../../experiments/dependent-congruence-resumption/GuardedWrongEndpoint.lean.txt)
attempts to supply `q : x = z` where `q : y = z` is required. Lean rejects that
caller at the middle-path field. It is not counted as a successful source proof
or included in the accepted import closure. Its
[output](../../experiments/dependent-congruence-resumption/GuardedWrongEndpoint.diagnostic.txt)
records the mathematical endpoint mismatch, rather than an unrelated syntax
failure.

The failed legacy fresh-annotation caller remains in the earlier comparison.
During this implementation, trying to discharge finite premise membership by
case analysis on `Or` failed because derivations live in `Type`; the import
helper uses decidable equality case splits instead. Raw schematic substitution
also needed explicit finite-arity congruence rather than relying on large
reduction. Routine namespace and implicit-argument failures were repaired
without changing the mathematical goals or increasing heartbeat limits. These
are implementation costs, not evidence against the statements.

The framework now contains the normalization work which ordinary callers of
these operations previously had to supply. Constructing it required explicit
binder, root-map, and interpretation proofs. This is framework-assisted recovery
of a known argument. It does not measure independent author productivity, total
repair savings, frontend usability, or scaling across many developments.

## Handoff and acceptance

Use the guarded source interface for the separate #108 trial. Authors still
supply the mathematical motive, admissible hypotheses, and branch argument.
Generic finite-tail elimination and path/environment substitution helpers are
available; automatic elaboration of arbitrary Agda syntax is not. New named
operations may need their own generated fresh-substitution theorem. Report such
work as setup or repair effort rather than omitting it from the trial.

The implementation incorporated integration commit
`a2265404d436986b8fc69dfb5ce252b6a9b6fde1` before this report. Focused checks cover
the new source modules and example modules. Full committed-candidate fresh
validation, exhaustive proof audit, and independent Standards/Spec review are
separate acceptance obligations owned by the orchestration. The candidate must
not be advertised as the frozen #108 interface until they pass.
