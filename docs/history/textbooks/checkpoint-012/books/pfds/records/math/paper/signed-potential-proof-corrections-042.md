# Signed-potential compiler corrections during native recovery

Recorded 2026-11-03. This is development and statement-review evidence in the
existing ticket 10023 loop, not an acceptance record.

## Fixed scope and preserved failures

The full review base remains
`5e048f781aa04be9ce993f1e7455bdc82df22bff`; requirements remain version 1 of
`session/requirements/signed-potential.md`, SHA-256
`bb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81`.
The earlier reviewed candidate `d24c443ba22019613b1ce646d6eed7279c791ad6`
is retained. Its genuine QEMU focused run finished with exit 1 and unchanged
inputs in `validation/signed-d24-direct-r1.json`. Source review did not predict
or substitute for this compiler result.

Commit `956c4b06abe8d54f78a6166690c12453115f8304` qualifies the intended
`Resources.bind` and `Resources.pure` names in the signed examples and makes
the final natural-budget rewrite explicit. Its genuine native run is
`validation/signed-956-native-r1.json`: exit 1, unchanged inputs, and clean exact
candidate. `Examples.SignedPotential` compiled; the transport example still
failed. Both original records and their full diagnostic logs remain unchanged.

Commit `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` then fixes the type of the
inner budget before coercing the complete result to the reals. Its separate
eleven-target native run is `validation/signed-3cf-native-r2.json`. Consult that
record for its complete evidence. It subsequently finished with exit 0 at
17:14:27 UTC, with its terminal result observed, unchanged inputs and a clean
exact candidate. All eleven requested targets succeeded; Lake reported 935
jobs including dependencies. This establishes focused development success,
not the separate full build/audit or ticket acceptance.

## Intended mathematics and the inference correction

The counter program and its state trajectory are unchanged. Each step has
constant amortized charge 2. Consequently its natural-valued budget for a list
of n increments is 2n. Mapping that sum with `Nat.castAddMonoidHom ℝ` produces
the corresponding real-valued budget. This is the intended application of the
public `budget_map` law, followed by the existing natural `budget_constant` law.

After generalizing `budget`, its charge codomain is independent of the step's
observation codomain. An outer result ascription to ℝ can therefore select a
real-valued budget even when a lambda contains a numeral initially annotated
as Nat: the numeral is coerced at the charge. That is different from coercing
the complete natural sum. The first rewrite attempt exposed this mismatch.

The corrected intermediate expression is explicitly of the form
`((budget step naturalCharge inputs state : Nat) : ℝ)`. The inner Nat ascription
fixes the sum's codomain before the outer coercion is elaborated. The derivation
therefore connects the real charge to the natural budget through `budget_map`,
then rewrites that natural budget with `Resources.budget_constant` and the
ordinary cast/multiplication laws. It preserves the independently expected
conclusion, real budget = 2 × n.

## Statement review and acceptance boundary

The corrections change only proof expressions in `Examples/SignedPotential.lean`
and `Examples/PotentialTransport.lean`. No definition body, public theorem
statement, quantifier, hypothesis, numerical expectation, or source-provenance
claim is weakened. The real counter application still uses the unchanged
measured increment program, the public reweighting/run transport, and the
potential telescope. Its cost-only inequality still supplies nonnegativity of
the actual final potential. Signed debt and negative-final-potential examples
retain their original expectations.

The explicit inner type also makes the intended public-law connection visible;
it does not replace that connection with a detached numerical calculation.
The complete patch identities are preserved in
`validation/signed-potential-compiler-correction-042.patch` and
`validation/signed-potential-budget-cast-correction-042.patch`, with their
candidate records. Existing d24 review outcomes remain historical. Both axes
must review the entire current 10023 scope, and its own exact full build,
exhaustive audit, and immediate final candidate verification remain required.
No chapter or formal-ticket acceptance is advanced by this note.
