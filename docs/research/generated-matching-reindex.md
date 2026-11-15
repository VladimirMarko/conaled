# Generated matching under substitution (#445)

`SmoothQuotientCechLocal.substitutionEvaluation_isEquivalence` proves effectiveness
of the actual substituted-family evaluation at an arbitrary source context object.
Its sole mathematical hypothesis is effectiveness of the underlying family
evaluation at that object's substituted image. The substitution may forget arrows
or objects. No equivalence or faithfulness of the substitution is assumed.

## Construction and statement review

`CechMatchingComprehensionPull` pulls the three relative families and all six
restriction transformations along a strict diagram map. Each restriction includes
the selected equality transport from the corresponding base square. Construction
of its total strict map takes coherence of both family diagrams explicitly.
These are diagram laws, not an assumed matching equivalence.

`SmoothQuotientGeneratedRelativeSubstitution.relativeFamilyData_sub` identifies
this construction with the actual interpreted substituted family. Its coherence
comes from `relativeFamilyCoherence`. The relative total substitution is the
actual typed lifted substitution, expressed through the independently checked
relative/generated diagram comparisons. Its projection square holds strictly.

The induced functor on each fixed matching fiber is full and faithful. To lift an
arrow, `GrothendieckPreFiber.lift` retains the supplied target fiber arrow and uses
the specified source base arrow. Equality reflection requires equality of the
source base arrows; it does not require the base functor to be faithful. The
matching overlap square is reflected using this fixed-base equality. Thus the
argument retains both actual overlap compatibility and nonidentity local arrows.

`totalMatchingEvaluation_substitution` and
`fiberTotalEvaluation_substitution` compare the actual evaluation functors,
including their arrow actions. The generic `fixedBaseFunctor_comp` then compares
extraction before and after the relative map. Full faithfulness of the induced
fiber map and equivalence of the composite imply effectiveness of the substituted
evaluation. Essential surjectivity is obtained from that composite; it is not
postulated for arbitrary matching data.

The generic statements use an arbitrary universe for the strict diagrams and an
independent source object universe. The smooth quotient specialization uses the
existing generated universe levels. No proof irrelevance is applied to local
arrows or chosen overlap data; equality proofs alone are interchangeable.

## Checked consumers and scope

`Examples.GeneratedFamilyConstructors` applies the final theorem to arbitrary
typed substitutions and to weakening at an arbitrary extended-context object.
The quantification includes the existing finite-tail and path-tail substitutions;
this theorem imposes no extra restriction on their syntax or semantic map.

`Examples.CechMatchingComprehension` checks full faithfulness without a base-map
hypothesis. Its integer-loop example collapses all base loops to a point: the
total functor identifies a nonidentity horizontal loop with the identity, while
retaining the selected vertical loop. This distinguishes fixed-fiber full
faithfulness from the false stronger claim about the total functor.

These are constructor and transfer results. They do not by themselves assert
that the complete generated context/telescope induction or #433 is finished.
Full integrated acceptance and independent review remain with the enclosing
orchestration.

Focused validation passed for both consumer modules (3,661 build jobs, including
cached dependencies) using the normal elaboration limits. Targeted axiom checks
for the final substitution theorem, actual fiber full faithfulness, and extraction
composition report only `propext`, `Classical.choice`, and `Quot.sound`.
The weakening consumer states its base object through the actual weakening
functor. Expanding that projection inside the instance premise caused an
expensive failed normalization attempt; keeping the semantic functor explicit
checks without changing the hypothesis.
