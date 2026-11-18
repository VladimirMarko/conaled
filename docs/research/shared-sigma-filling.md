# Shared dependent-sum filling

The De Morgan and Cartesian models now use one dependent sequential-filling
argument. Their chosen algorithms and public `sigmaFilling`, fills, uniformity,
and lawfulness signatures remain the same. Each adapter's selected operation
recovers the native operation by definitional equality.

`SequentialFilling.Problem` retains the first box, its selected section and
boundary proof, the second box indexed by that section and proof, the second
selection, and pairing. Its boundary theorem uses the two component boundary
laws and the primitive pair-boundary law. `Substitution` retains separate maps
of boxes, sections and pairs, component uniformity, and the second-box transport
law. Its uniformity theorem derives equality of the whole selected section.
Neither record assumes that final equality.

The shared proof equates first sections together with their Prop-valued boundary
witnesses, then transports the dependent second calculation. Proof irrelevance
applies to those boundary witnesses; this construction does not cover relevant
higher witnesses. Native pair-boundary and second-box transport lemmas remain
in their models. No identification between intervals, caps, contexts or families
is needed. Cartesian caps remain arbitrary sections and faces arbitrary
subcontexts; De Morgan boxes retain their fixed cap and cofibrations.

The checked example uses dependent Fin 1/Fin 2 fibers, a nonempty proper face,
a variable cap, two nonidentity coordinate substitutions, and their nonidentity
composite. It constructs actual boxes, checks both branch values, and compares
whole filled sections after the two substitutions. Existing native dependent-sum
and classifier clients remain in the integrated audit.

The adapter setup is paid once per model. Ordinary callers still use the native
API and have the same component-law obligations. The reusable result removes the
duplicated subtype/congruence calculation; it does not reduce every domain proof
or establish a measured productivity improvement. A global category of filling
problems, shared classifier, cross-model filler bridge, and weak-composition
foundation remain separate questions. The existing endpoint obstruction is
unchanged.

The [design brief](shared-sigma-filling/brief.md), independent
[foundations](shared-sigma-filling/foundations.md),
[use](shared-sigma-filling/use.md), and
[alternatives](shared-sigma-filling/alternatives.md) assessments, and
[synthesis](shared-sigma-filling/synthesis.md) record the decision. The earlier
[shared-constructor assessment](shared-cubical-constructors.md) remains useful
for the wider alternatives. This extraction completes #627; #634 owns further
search and #636 the architectural-guidance reassessment.
