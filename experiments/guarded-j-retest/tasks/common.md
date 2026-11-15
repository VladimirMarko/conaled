# Author task: selected nested J and root computation

Complete calibration first, preserving a checked calibration file. Then complete
the held-out task in a new attempt. One final self-contained Submission.lean
must contain both phases. Use the frozen interface unchanged.

## Calibration (public prior task)

For an arbitrary point x:A in Γ, arbitrary length-n dependent tail T over the
based path of x, and p:Q over total T, construct a command eta with motive
Id_Q(p,p) and branch reflexivity of p restricted to the root-tail map r. Retain
its source term typing and exact selected J recipe. Also derive the root-tail
map and the branch typing using the provided interface. This is the public
one-certificate recipe from #320, which already has completed baseline and
candidate solutions. Those solutions are not supplied or importable here.

## Held-out contract

1. Construct the outer command kappa with motive Id_{Id_Q(p,p)}(eta,eta)
   and branch reflexivity of eta restricted along r. Retain the actual selected
   J expression and its full source type. Plain reflexivity is not a substitute
   for either selected J. Supply an explicit source-recipe equality for kappa.
2. Derive the outer root computation as a source judgmental equation, with
   separate source typing of both operands at the required aligned family.
   No requested semantic comparison or alignment may be assumed.
3. For arbitrary valid dependent σ from Δ into total(pullback T root), derive
   both substituted operand judgments and their substituted source equation.
   Retain their exact selected terms and family, including any source family
   conversion required by your presentation.
4. Construct an actual σ by weakening the root-tail total through the family
   of eta restricted along r. This is the pullback of Id_Q(p,p), with the
   varying section p retained in its endpoints. Apply the generic comparison
   and both operand judgments to this substitution; do not assume a map with
   the desired behavior instead of constructing it.
5. Interpret the comparison in an arbitrary full contextual model (under
   satisfied source assumptions for the guarded arm). Show semantic agreement
   for the typed operands. Retain the exact selected left term and its family
   under reuse in the exact reduct of the stable Sigma extension. The guarded
   arm also embeds the source derivation and assumptions into Sigma.theory.

Use declaration names calibration, inner, outer, selectedRecipe, rootMap,
rootLeft, rootRight, rootBeta, substitutedLeft, substitutedRight,
substitutedBeta, dependentWeakening, workedLeft, workedRight, workedBeta,
comparisonSound and extensionSelected. Additional declarations are welcome.
Give typing/type preservation explicitly in the statements or indices, not
only in prose. Baseline also supplies selectedRoot as explained in its guide.

The model boundary is every PathTransport.Typed.Model with Sigma.Stable on
its structural reduct when extension reuse is requested. Stable Sigma has eta
and stability; beta-only sums or a higher-model claim are not requested.
Object Id, source judgmental equality, host equality, and semantic equality
must remain distinct. Do not add axioms, admissions, UIP, equality reflection,
a desired-output premise, or a new model law. No theorem from #108 is involved.

The complete nested-certificate/root-computation/substitution contract was
selected after this round's interface freeze. Its ingredients are not all new:
public authoring modules include nested-J examples, and calibration discloses
the one-level certificate. Report this exposure; this is a fixed-order trial,
not two independent first-exposure measurements.
