# Encoding and resource evidence

The failed attempts below retain the same mathematical contract as the delivered
implementation. No recursion-depth or heartbeat increase was used.

## Whole-transformation target cast

[The original helper](helper-cast.lean.txt) transported an entire strong
transformation along equality of its target pseudofunctor. The
[span specialization](span-cast.lean.txt) retained the intended complete components,
but checking `successiveTransformation_app` required substantial kernel reduction.
The [original profile](cast-profile.log) records 45.149261 seconds for that
individual declaration; the [field-preserving profile](field-profile.log) records
0.014531 seconds after copying the data fields and transporting only the laws.
Both profiles were produced with Lean's `trace.profiler` enabled during local
`lake env lean` checks. They are single observations, not a repeated benchmark or
a claim about general author productivity.

Both profiled whole-module attempts still failed elsewhere at that point, on the
identity pullback-comparison proof. Their accepted component declarations provide
the measured evidence; the logs do not certify a successful whole-module build.
The identity proof subsequently reused `MixedBaseChange.identity`, and the final
module and concrete clients passed focused builds before integrated validation.
The retained `.lean.txt` files are experimental source, not proof roots.

## Elaboration failures

Early attempts at pseudofunctor extensionality allowed Lean to identify the two
functors before examining their complete data. Explicit endpoints fixed the
inference problem. Naturality proofs needed the underlying `mapFunctor` expanded
and explicit mapped identity equations at the slice boundary. Neither failure
supplied a counterexample to the proposed mathematics.

Native `Iso.refl` at a concrete strong-transformation type sometimes failed to
infer its hom-category. The helper's `ModificationIso` and `modificationRefl` fix
that native instance explicitly; clients also open Mathlib's strong-transformation
scope. No replacement category or weakened modification law was introduced.
