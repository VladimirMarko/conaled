# Canonical decoder filling recovery

The fixed large-context classifier preserves the complete supplied lawful
filling operation in both native cube models. This resolves the operation
question in [#607](https://github.com/VladimirMarko/conaled/issues/607).
Adopt the recovery laws and their constructor/substitution corollaries. The
proof requires no change to the classifier, decoder, constructor selections or
existing clients.

## Exact statement and hypotheses

In either `Presheaf.SmallUniverse` or `Cartesian.SmallUniverse`, take
`Ξ : Context.{u+1}`, `C : Family Ξ`, `P : SmallPresentation.Data C`,
`F : Filling C` and `hF : F.Lawful`. The new theorem is

```lean
P.native_filling_recovery F hF :
  (NativeDecode.filling (P.code F hF)).transport (P.nativeIso F hF) = F
```

`P` supplies explicit `Type u` representatives and equivalences for the fibers
of `C`; the context itself need not be small. The equation uses the actual
`P.code` and `P.nativeIso` produced by the library. Lawfulness is required for
the local-to-global reconstruction. There is no uniqueness hypothesis on the
fibers, on fillers or on paths.

This equality of `Filling` records compares their `fill` fields on every test
context, base map, face and open box. In the original model the cap lies over
endpoint `false`. In the Cartesian model the equation also quantifies over
every interval section `r` and retains the entire cap on `graph r`. The outputs
are complete sections over the interval, including all generalized points and
naturality. Endpoint agreement alone would not establish this equation.

For `R = LargeConstructors.construct P F hF`, the equivalent exposed equation
is `NativeDecode.filling R.code = R.filling`, named
`construct_native_filling`. The named `sigma_native_filling`, `pi_native_filling`
and `path_native_filling` specializations apply to the existing fixed
constructors, including their selected small presentations. The general theorem
and these fixed-constructor corollaries are checked separately in
[the original module](../../SquareKit/Internal/Cubical/LargeFamilyFillingRecovery.lean)
and [the Cartesian module](../../SquareKit/Internal/Cubical/CartesianLargeFamilyFillingRecovery.lean).

## Derivation through the actual chart adapters

The source of the code is
[`SmallPresentation.Data.localFamily`](../../SquareKit/Internal/Cubical/LargeFamilyClassification.lean),
which lowers the supplied filler through the chart presentation. The proof
follows that data rather than replacing the canonical decoder with a new
operation:

1. `localFamily_code` identifies the restriction of the large code along any
   raised small chart with the code of the supplied chart record.
   `decoded_localFamily` then uses the small classifier's complete-record
   recovery law. This recovers the family, selected filler and lawfulness
   record together.
2. `localDecodeIso_filling` identifies the transported small decoded operation
   with the lowered supplied operation. `localDecodeIso_native` proves that
   this equality-induced local family comparison, after raising and composing
   with `chartIso`, is exactly the restriction of the global `nativeIso`.
3. `chartBox_recovery` identifies the entire lowered/raised box with the
   original box mapped through the decoder and restricted to the chart.
   The Cartesian proof retains `chartSource`, `LowerFilling.source` and the
   variable graph cap. `chartFilled_recovery` and `chartFilled_native` recover
   the whole selected chart section using these box maps and `hF.uniform`.
4. `fillRepresented_recovery` evaluates the raised chart equality through
   `representedRaise` and `lowerIntervalElements`. The final theorem uses
   `LocalFilling.toFilling_toLocal`, the inverse box-map roundtrip and
   `Filling.toLocal_value` to recover the operation on arbitrary contexts.

The original proof uses the original model's small-record and local-filling
bridges. The Cartesian proof independently uses its corresponding bridges;
the Cartesian complete-record theorem is not evidence for the original claim.
The implementation is a checked derivation of the displayed full equation,
with no outstanding paper-only step.

## Constructor substitution and the remaining body question

For any substitution `σ`, the new `sigmaSubstitution_native_filling` theorem
states

```lean
(NativeDecode.filling (σ ≫ (sigma a b).code)).transport
    (sigmaSubstitution a b σ) =
  NativeDecode.filling (sigma (σ ≫ a)
    (liftSub (liftedDecode a) σ ≫ b)).code
```

`piSubstitution_native_filling` uses the actual Pi substitution adapter, and
`pathSubstitution_native_filling` also substitutes both endpoint sections.
All three laws hold in both models. They follow from recovery and the existing
complete returned-operation substitution laws in
[`LargeFamilySubstitution`](../../SquareKit/Internal/Cubical/LargeFamilySubstitution.lean)
and [its Cartesian counterpart](../../SquareKit/Internal/Cubical/CartesianLargeFamilySubstitution.lean).
Thus a caller can rewrite canonical filling across the fixed rebuilt decoder
without unfolding the chart proof or changing its selected operation.

This supplies the full-operation input identified by
[#671](https://github.com/VladimirMarko/conaled/issues/671). That issue still
owns naturality of the selected `sectionComparison` construction and exact
whole-body equality for independently rebuilt fixed constructor comparisons.
The present equations do not identify arbitrary paths with equal endpoints,
or prove equality of code maps. The bounded original Sigma/Pi consumer has
priority; a universal classifier proof is no longer an external prerequisite
because the required operation equation has now been derived here.

The three approaches remain distinguishable:

| Approach | Checked contract | Consequence for callers |
| --- | --- | --- |
| Direct recovery here | Canonical decoder filling, transported through the fixed decoder, equals the supplied complete operation. | Canonical filling can use the constructor's operation and substitution laws. |
| Existing preservation by construction | `Result.filling` is defined by transporting the supplied operation; `construct_filling` recovers it. | Preserves the earlier API without needing canonical recovery. |
| Existing explicit native comparison | `Result.compareRebuilt` and its two-step variant retain both actual transports and full comparison bodies. | Remains usable for independently chosen results without assuming operation or body equality. |

The [constructor audit](small-universe-constructor-gap-audit.md),
[large-context constructor report](large-context-constructors.md) and
[#606 report](constructor-recomputation.md) recorded the earlier distinction
between returned and canonical operations. The new theorem resolves that
operation boundary for the fixed construction. It does not retroactively
change their acceptance scopes or remove their weaker comparison APIs.

## Checked controls and reuse

[The examples](../../Examples/LargeFamilyFillingRecovery.lean) retain independent
bounded arguments: subsingleton fibers determine the whole operation, and a
family explicitly isomorphic to a discrete constant family has unique lawful
filling. The Cartesian discrete argument quantifies over arbitrary source
sections and subcontexts. Concrete Boolean presentations negate the small
representative before lifting it, so their decoder comparison is not merely an
identity presentation. Their complete recovery equations now also exercise the
general theorem.

The Cartesian `B(Z/2)` control has two lawful selected fillers on the same
carrier. The small classifier recovers each complete record, and the selected
fillers are unequal. The new large-context group-nerve presentation also
exercises general recovery for each group selection. These controls explain
why a proof by carrier-only uniqueness would be insufficient and why preserving
the selected record in the code matters. They do not refute fixed-classifier
recovery.

The preserved [#554 helper record](https://github.com/VladimirMarko/conaled/issues/554)
was inspected before implementation. Its Pi second-family transport and
contraction-filling reindexing lemmas concern different interfaces. The present
proof uses accepted small-record, raising and local-filling bridges, so no
historical helper was ported. The old constructor clients, varying-fiber and
nonidentity substitution examples, nonreflexive-path controls and the
body-retaining recomputation clients remain part of focused validation.

## Cost and decision

Both core modules compile with default heartbeat, recursion and kernel limits;
no local transparency override remains. The combined focused core check built
1,001 jobs, with reported module times of 2.0 seconds for the original proof
and 3.1 seconds for the Cartesian proof. These are development observations,
not an estimate of general proof productivity or a substitute for exact
candidate validation.

A preliminary draft resolved `interval` to the presentation constructor inside
`SmallPresentation.Data`; its malformed dependent statement produced a type
error and a 200,000-heartbeat timeout. Qualifying the actual interval family
removed that error. Later attempts to rewrite through definitionally equal
adapter types failed; explicit equality composition and named box/section terms
resolved them at default limits. A provisional local transparency setting was
removed and the complete proof rechecked. These failures establish neither a
mathematical obstruction nor a need for a larger resource budget.

Adopt the complete recovery and fixed-constructor substitution laws. There is
no remaining general recovery theorem to defer and no construction change to
schedule from this investigation. Retain #671's selected-comparison and body
obligations, and keep Cartesian path algorithms under their separate #631
scope. Acceptance requires the exact integrated candidate audit and independent
Standards and Spec review coordinated by the enclosing implementation loop.
