# Guarded replacement of the dependent pairing client

The guarded replacement recovers the exact substitutions used by
`Examples.DependentCongruence.DependentArguments.dependentPair` in every full
contextual model. Its second component retains the identity type depending on
the first component. Recovery uses the selected J computation and dependent
casts; it does not identify all inhabitants of an identity type.

This is the bounded migration in
[#328](https://github.com/VladimirMarko/conaled/issues/328). The original client,
its public helpers and its interpretations remain available.

## Selected source and guarantee

The [retained inventory](dependent-coherence-fixture.md) names
[`DependentArguments.dependentPair`](../../Examples/DependentCongruence.lean).
Its source was selected at integration commit
`729619a90b56644422b5aeb173950f498e960866`, after the reviewed #323 helper repair
and fresh trial. Supporting definitions live in
[`CongruenceCaller`](../../SquareKit/Internal/PathTransport/Authoring.lean).

The original context contains one base point. A J application at reflexivity
computes to that point. `pairedBeta` uses the computation to convert the first
component of a substitution into an extended context. `boundIdentity` is
reflexivity at the generic variable of that extension. Substituting it along
the two converted substitutions gives the second components. Their types
depend on the first component, so `substitutionCongrAt` and `pairingConverted`
carry explicit type and annotation conversions.

The resulting judgment equates two substitutions into a two-step extension.
It retains more than their target context: it determines the selected point
and the selected reflexivity term at that point. The original theorem works
for every full `PathTransport.Typed.Model`. It does not establish general
path concatenation associativity; #107 remains paused and no #108 theorem was
selected or prepared.

## Replacement derivation and raw structure

[`DependentClientMigration.lean`](../../Examples/DependentClientMigration.lean)
builds a source-only replacement from a typed point `x : A` in Γ. Its
`computed` expression transports x along reflexivity in the family obtained
by weakening A. The public `Tm.transportRefl` helper supplies the J computation
`computed = x`. The replacement then forms

```text
first(t)  = pair A id t
second    = Id (A[weaken]) generic generic
result(t) = pair second first(t) (refl generic)[first(t)]
```

Both `result(computed)` and `result(x)` are typed source substitutions. Source
congruence applies the J equation to the first component and to substitution
in the second. `Source.equality` is the resulting guarded derivation.
`Source.reindex` retains that equation under any further raw composition;
typing such a composition still requires the usual substitution judgment.

This is a checked replacement, not a translation of every constructor of the
annotated Typed API. Its raw terms use schematic variables for Γ, A and x;
the original uses de Bruijn raw syntax and model-indexed codes. The new motive
is an explicit pullback of A, whereas the original uses primitive base and
its substitution equations. No equality of these different raw languages is
asserted. `Source.first_recipes_distinct` checks that the new computation node
and its point variable are distinct raw expressions, and the old
`CongruenceCaller.beta_sides_distinct` retains the original analogous check.
Both source recipes compute before the dependent pairing comparison.

The concrete source assumption list has one judgment, `term Γ A x`. Its family
and context judgments follow through the public rules. `environment_satisfied`
constructs a satisfying assignment for every actual model context, family
and section; the semantic theorem is not conditional on an uninhabited raw
signature. The source proof itself does not take semantic annotations or a
model argument.

## Exact semantic recovery

`Semantics.doublePair_eval` evaluates the new right-hand expression to the
actual pair of a section substitution and the substituted selected reflexivity
term. Its proof tracks the dependent second family and term, rather than
extracting an untyped value from the tagged interpreter.

`Original.first_right_selected` removes the original computation's annotation
casts using their heterogeneous equality laws and identity substitution.
`Original.right_selected` then identifies the whole old substitution with that
same selected pair. `Original.original_guarantee` consumes `subSound` of the
exact inventory client `DependentArguments.dependentPair`; inverse annotation
casts cancel explicitly. The auxiliary `dependentPairedLeft` and
`dependentPairedRight` supply its two typed endpoints.

`right_recovers` and `left_recovers` combine these comparisons with the guarded
interpretation of `Source.equality`. Each conclusion is an equality of tagged
substitution values with the original interpreted substitution, including its
domain, dependent target and chosen components. `recovered_eq` exposes the
same arrow through the interpreter's typed lookup. `recovered_twice` preserves
it under two arbitrary object-context substitutions.

These theorems quantify over full models and use no discreteness hypothesis,
uniqueness of identity proofs or equality of erased observations. They recover
this reflexive-computation client. They neither construct a higher model nor
compare different J recipes at arbitrary nonreflexive paths. Those obligations
remain with the corresponding clients and #321/#322.

The native Type specialization is a separate discriminator. At the input
point n, the recovered substitution selects n. `rejects_erased_point` rejects
replacing the selected point 2 with zero. With successor after doubling, the
input 3 yields 7 through the recovered arrow and the general substitution
recovery theorem. This is a test of selected data; it is not evidence of
nontrivial higher identity. The all-model equality above supplies the precise
witness recovery contract independently of that specialization.

## Author and model obligations

The guarded author supplies the typed-point derivation. Public helpers handle
the transport motive, reflexive branch, source type conversion, pairing and
congruence. The original author supplies common raw types and model-indexed
annotation alignments to its generic conversion helpers. Those original
helpers remain valid and usable.

The adapter work is the explicit evaluation of the guarded pair, cancellation
of the original annotation casts, and comparison of the selected J computation.
Model builders supply the existing full contextual model, including its chosen
J and substitution laws. No new builder field or admission law was added.

Focused development used the normal Lean elaborator and existing module options;
no increased heartbeat or recursion limits were needed. Failed checks concerned
namespace ambiguity, section-variable naming, explicit dependent type inference,
and the retained client's inverse annotation casts. The last item required an
actual comparison lemma; equality of target contexts alone did not discharge
it. These are implementation observations, not a controlled productivity trial
or a measured speed comparison. Exact build/audit receipts and independent
review records are retained by the #235 orchestration.

## Adoption boundary

Adopt this guarded replacement where the required result is the retained
reflexive J computation followed by dependent pairing. The source argument is
independent of model annotations, and its exact old-data recovery is checked.
Keep the old API and both clients available.

Further migration needs a chosen client, a source typing derivation, and a
comparison preserving its selected terms and dependent types in every promised
model. A nonreflexive J or concatenation client needs its own motive, branch
and selected-witness comparison. An endpoint equation in a discrete model does
not discharge that obligation in a higher model. This one replacement supplies
neither a universal Typed-to-guarded translation nor the source adequacy result
owned by #326.
