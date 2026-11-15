# Generated interpretation under signature-preserving maps

This is the generic preservation component of [#433](https://github.com/VladimirMarko/conaled/issues/433).
It connects the existing `PathTransport.Typed` derivations and recursive
interpreters to the existing `Typed.ModelMap`. It does not construct the smooth
comparison model or complete the source-to-classical checkpoint by itself.

## Contract

`SignatureMap` in
[`SignatureInterpretationMaps.lean`](../../SquareKit/Internal/PathTransport/SignatureInterpretationMaps.lean)
extends `ModelMap` with preservation of `base` and `fiber`. The fiber law casts
the mapped base section along the base-family equality before applying the
target fiber operation. The underlying map already preserves the structural
operations and primitive contextual J. Telescope, path, motive, branch and
reindexed-branch comparisons come from `InterpretationMaps`; they are not new
map-builder obligations.

For endpoints in the same `Model.{u}` universe, the same existing source
derivation has interpretations at both endpoints. The five mutually recursive
results cover every constructor of `CtxDeriv`, `TelDeriv`, `TyDeriv`, `TmDeriv`
and `SubDeriv`. Context preservation is equality. Family, section, telescope
and substitution preservation is heterogeneous equality, retaining the shared
context and family equalities in the result. The term cases include generic J,
endpoint-instantiated J, its reindexed form, reindexed branches and conversion.

The `interpretCtx`, `interpretTy`, `interpretTm` and `interpretSub` corollaries
use the existing `interpret*_agrees` theorems to connect these annotation results
to the actual recursive interpreters. No desired interpretation theorem is a
field of `SignatureMap`. The construction changes no source rule or model law.
Direct models, direct semantic clients and other comparison constructions remain
available independently of this optional map interface.

## Checked cases and statement review

[`Examples.SignatureInterpretationMaps`](../../Examples/SignatureInterpretationMaps.lean)
constructs a fresh source caller with a two-binder tail `z : base, b : fiber z`.
Its later family depends on the earlier binder. A reflexivity motive supplies a
generic J term and a reflexive endpoint application. The examples use the new
public preservation results for the full context, fiber family, telescope,
generic J, reflexive application, branch reindexed along weakening, and the
corresponding tail substitution. The point variables and motive branch also
exercise the existing generated conversion operation. An identity signature map
on the native type model gives a concrete satisfiable specialization.

The scope case constructs an identity-on-operations structural map between the
native models with base types `Unit` and `Empty`. The generated base family is
not preserved: evaluating a proposed family equality would give `Unit = Empty`
and hence an element of `Empty`. This checks a real obligation introduced by the
signature interface. It does not claim that every structural map extends to a
signature map.

The EDD obligation was the missing connection between these generated callers
and model-map preservation. The recursive proof establishes that connection;
the examples consume it rather than reproving the semantic result independently.
Statement review checked these boundaries:

- Both endpoints share one ambient model universe for the generated results;
  `SignatureMap` itself permits different universes. An outer universe adapter
  is a separate construction.
- The induction domain is generated derivations, including open contexts,
  arbitrary finite dependent tails, all substitutions and all term conversion
  constructors. No result asserts naturality of an arbitrary semantic-code
  function merely because it has a `CtxCode`, `TyCode` or `TmCode` type.
- The recursive invariants retain context and family comparisons. Every J case
  compares the complete telescope, motive and branch before using primitive
  `mapJ`. Conversion transports an already established result along its code
  equality; it adds no interpretation hypothesis.
- Heterogeneous equality here compares mapped semantic data. It does not identify
  distinct object-language identity witnesses or assert reflection of source
  equality.

## Validation and remaining integration

Focused builds of the generic module and examples completed successfully using
`direnv exec . taskset -c 0,1 lake build ...`. A focused run of the unchanged
`ProofAudit.lean` audit code with only its entrypoint import replaced by
`Examples.SignatureInterpretationMaps` passed for all 1,721 logical declarations
in its 11 imported project modules. The new library module contributes 73 logical
declarations and the example contributes 38. The transitive axiom union is
`propext`, `Classical.choice`, and `Quot.sound`.

The full public-entrypoint build, fresh acceptance audit and independent
Standards/Spec reviews belong to the enclosing integration workflow. This record
reports focused evidence only. The comparison-model author specializes the two
projection maps to `SignatureMap`; smooth restrictions, descent, classical
comparison and the unchanged retained transport-composition consumer remain
within the enclosing #433 work.
