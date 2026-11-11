# Tasks for both routes

Work on H1 and then H2. Import `TaskSetup462` for the identical supplied setup.
The definitions and native preservation APIs are available to both routes.
Supply your proofs in your own output files; do not change supplied definitions
or production interfaces. Alternative valid sufficient proofs are accepted.

## H1: selected-row extension

Use `Tasks462.H1`. Source codes and values are Bool, with evaluator
`sourceEval c a = c`, step constantly false, and selected code false.
Target codes are Option Bool, with evaluator `targetEval c a = c.getD true`,
step constantly false, code map `some`, and identity value map. The target has
different rows for different codes; each row is constant in its input.
The supplied source object and map include their required local proofs.

Complete these obligations:

1. Prove `changeCodes.Extension source`. Obtain a full-target selected
   construction using the native extension route. Preserve its selected code
   `some false` and witness `false`, and prove representation for every target
   input, including `none` explicitly.
2. Prove `¬ Function.Surjective changeCodes.code`.
3. Obtain the native image-restricted construction and compare its selected
   code (projecting the subtype) and witness with the full-target construction.
   State representation on its image-subtype domain, and show that domain
   excludes `none`. Do not claim equal input domains.
4. Prove that proposed source code `true` fails its representation obligation:
   `¬ (∀ a, sourceEval true a =
      SquareKit.DiagonalConstruction.diagonal sourceEval sourceStep a)`.
   A failed proof attempt alone is not a checked refutation.

Retain the supplied evaluator, step and value map. A different value naming
convention cannot replace the incorrect source representation.

## H2: measured total compilation with product observations

Use `Tasks462.H2` and the existing `Examples.RecursiveCompilation.total` on
arbitrary lists of integers. The setup supplies its compiled seed and the
transition with the visit charge included. The supplied bare functions are
`productWeight n = (n, 2*n)` and `finalWeight (u,v) = u + 3*v`.

Complete these obligations:

1. Package both functions as additive homomorphisms with their zero/addition
   laws. Compose them through the actual Nat × Nat observation type.
2. Connect the real compiled seed and visit-charged transition execution to
   reweighted execution. Prove a universal seed/bind/run transport statement
   through both maps, using `Resources.reweight_bind`, `Resources.reweight_run`
   or their common generic consequence `InterpretationAssistance.seeded_reweight`.
   The product must be an intermediate executor observation, not just notation
   in a final arithmetic calculation.
3. Recover the ordinary result `xs.sum` and original counted result
   `(xs.sum, 1 + 2*xs.length)` before reweighting. Include the native source
   execution relation for total/addBody and its visited-list-cell count.
4. Derive the final universal observation `(xs.sum, 7*(1 + 2*xs.length))`,
   connected to that composition and execution transport. Check the empty list
   and `[1,2]` cases explicitly.
5. Prove the shifted function `shifted n = n+1` fails the zero law. State why
   this prevents an additive-homomorphism certificate for that function. Keep
   this separate from the ordinary function's definability or the existence
   of other resource interpretations.

The observation counts modeled primitive and visit charges, not runtime or CPU
cost. The result must cover every integer list, with the supplied code and
native observation unchanged before reweighting.
