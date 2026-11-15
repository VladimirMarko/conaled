# Detecting equivalence of actual dependent evaluation (#445)

`CechMatchingComprehensionEffectivity` proves that a functor from a groupoid
comprehension into relative matching data is an equivalence when its base functor
and its extracted fiber functors are equivalences. The total functor is supplied
independently. Its projection must equal the source projection followed by the
base functor. There is no hypothesis that it is a total map of a strict natural
transformation.

The extracted functor is `fixedBaseFunctor` applied to the total functor after
fiber inclusion. `comparison` recovers that restriction after forgetting the
fiber. These are the same construction and comparison used by actual generated
`familyEvaluation`.

The proof separates three claims. Faithfulness uses faithful base and fiber
functors, then detects the kernel on vertical endomorphisms. Fullness uses full
base and fiber functors; a selected Grothendieck lift removes the base component
of an arbitrary target arrow. `ofDatumArrow` then reconstructs the remaining
vertical arrow in the appropriate matching fiber. Essential surjectivity uses
essentially surjective base and fiber functors, transporting a target datum along
a base isomorphism. Neither projection is assumed faithful. Nonidentity vertical
loops remain admissible.

`GrothendieckVertical.inclusion_arrow` recovers the entire supplied arrow after
extracting its fiber component. `ofDatumArrow` retains the supplied matching
arrow, conjugated by the explicit reconstruction equalities. In particular,
these constructions do not replace arrows by endpoint equality.

## Checked application and statement review

`SmoothQuotientCechGeneratedEffectivity.totalMatchingEvaluation_isEquivalence`
applies the criterion to the actual interpreted family, actual generated total
evaluation, and its proved projection square. Its hypotheses concern the actual
context evaluation and `familyEvaluation`, not an independently chosen comparison.
`matchingEvaluation_ext_isEquivalence` cancels the already constructed relative
diagram equivalence to obtain equivalence of the original generated extension
evaluation. This is the context-extension induction step needed by #433.

The criterion uses a common arbitrary object/arrow universe `u`; its application
instantiates `u = 1`. The auxiliary vertical-arrow extraction permits independent
object and morphism universes. Groupoid invertibility is essential to the kernel
argument, lift factorization, and target transport. No claim is made for arbitrary
categories without those hypotheses.

This establishes the induction step. It does not establish the constructor cases
needed to discharge every fiber hypothesis. In particular, it does not replace
the remaining comparison of actual base-type evaluation with primitive matching.
Focused Lean builds check this application and all new modules at default limits.
The final complete #445/#433 build and proof audit remain with the integrating
orchestrator.
