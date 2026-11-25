# Delimiter polynomial composition149

**UNCOMPILED implementation draft.** The six selected files in this directory
are a bounded mathematical handoff. No parent, repository source, native output
or checkpoint148 file was changed, and no compiler was invoked by this helper.

`EXPECTATIONS.json` was saved before `DelimiterPolynomial149.lean`. It fixes the
formula, quantifiers, small-input cases and preservation of actual witnesses.

## Contents and mathematical boundary

`timePolynomial A` mirrors the existing allowance exactly:

`p_A.eval N = 2 * (N + 3 + encodedPrimitiveTimeBound A N) + 1`.

Here A is `actionMaximum (R := R)` for the complete fixed program. The exponent
is `NormalFormDraft148.exponent p_A`, fixed before the raw word. Neither its
degree nor a large explicit numerical exponent is expanded.

The `Run` proposition exposes concrete native and conventional
`StateTransition.EvalsToInTime` witnesses, full initial/final configurations,
the exact `simulationTime + 1` equality, the `2 * native.steps + 1` bound and
the stopped fact. It contains no assumed polynomial-time field. `run_power`
constructs it from the existing `conventional_run`, preserving `target.toEvalsTo`
and changing only `steps_le_m`. `exists_fixed_power` exposes the order
`exists k, forall raw, exists native, exists target`.

The empty-input case retains the two steps of slack in the uniform polynomial.
Every singleton letter has exact equality of the existing conventional and
polynomial allowances. Both cases have actual-run corollaries; the singleton
case quantifies over all three `Option Bool` letters. The literal-pair theorem
retains the raw word, its size `input.length + cert.length + 1`, both complete
machine witnesses, and the existing `(verifyBitsRun input cert).1` answer.

This does not construct a new machine, transition table, NP equivalence,
effectivity theorem, sharper-space result, or source-acceptance claim.

## Precisely bound parents

The namespace `Resources.PolynomialTime.NormalFormDraft148` is supplied by the
corrected root-owned `work/normal-form149-checks/NaturalPolynomialNormalForm149.lean`.
Its body includes the explicit `change p.eval a <= p.eval b` repair. The
root-recorded normal-form149b and 149c results have actual exit 0 and unchanged
inputs; only their result metadata was inspected here, not their complete logs.
The original frozen148 core is retained historically and is not the chosen
implementation parent.

The consumer namespace remains
`Resources.RotationCertificate.DelimiterPreludeDraft.NativeConsumer148`.
For later root-bound assembly, the selected implementation body is
`work/delimiter149-checks/revision-d/DelimiterNativeConsumer149d.lean`, using
`work/delimiter149-checks/revision-b/SourceRunToOrdinary149b.lean`.
The revision-d diff against frozen148 changes only the local bundled finiteness
instance and the explicit natural-number allowance equality in the primitive
proof. The contracts consumed here are unchanged. The corrected delimiter-consumer149f result now records exit 0 with unchanged
inputs. Its selected concrete149d and generic149b bodies are exactly the parents
bound here. Only result metadata was inspected by this helper. This historical
combined result is neither compilation of the new composition nor installation,
ordinary-module completion or independent approval.

The new source's staging import `DelimiterNativeConsumer148` must resolve to
that explicitly selected body in root's preparation; it is a logical import
name, not a claim that a compiled module already exists. The upstream staging
import `SourceRunToOrdinary148` likewise maps to revision-b. The normal-form
staging import is `NaturalPolynomialNormalForm149`.

`MANIFEST.json` records exact existing paths, bytes, modes and hashes for these
parents, the five retained delimiter bodies, the unchanged four direct normal
project owners, and the observed result metadata. Parent proof bodies are not
copied into this draft. Root owns any later parent replacement or reassembly
and must bind its exact selected hashes before a compiler run.

## Query plan and remaining uncertainty

`QUERY_PLAN.json` specifies normal import of `DelimiterPolynomial149`, all
15 readable checks, four expanded checks, six selected axiom roots and one
definition print of `Run` so its witness fields are directly inspectable.
No combined carrier or compiler outputs are generated here. Parent queries
and the original 17 delimiter fixtures remain independently retained.

Remaining compilation risks are the polynomial evaluation rewrites, reduction
of the existential `Run` wrapper, dependent native initializer/default
conversions inherited from the parent, and the definitionally unchanged target
step fields after allowance widening. There has been no compiler feedback on
this composition, and no resource or transparency setting was changed.

## Frozen selection

Retain exactly `EXPECTATIONS.json`, `DelimiterPolynomial149.lean`,
`QUERY_PLAN.json`, `README.md`, `MANIFEST.json`, and `SNAPSHOT.json`.
The enclosing checkpoint inventory binds the snapshot itself. All parent
files remain at their existing canonical routes and are retained only once.
