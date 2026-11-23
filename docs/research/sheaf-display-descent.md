# Sheaf displays as an independent descent consumer

Issue #667 applies the family descent theorem to sheaf displays with arbitrary
maps. The fiber category is `SplitSheaf.Ty X`, whose arrows are natural
transformations of element families. `SplitSheaf.overEquivalence` identifies it
with `Over X`. Restriction is strict on families; `displayReindex` compares it
naturally with pullback of actual displays. Its components are the existing
`substitutionIso`, whose identity and composition equations remain those of
`SplitSheaf.substitution_identity` and `substitution_composition`.

## Effectiveness and recovery

`SplitSheafDescent` constructs compatible Kripke sections and their evaluation
isomorphism from primitive transport, identity, cocycle and naturality laws.
`SplitSheafStack` turns this construction into singleton descent, including
natural unit and counit on all maps. Local surjectivity supplies global recovery;
it is not needed to evaluate the constructed family on a chart.

`SplitSheafCoproduct` constructs a display over a coproduct from the coproduct
of the total sheaves. Van Kampen universality proves recovery of an existing
display. The restriction functor is full, faithful and essentially surjective,
including for the empty family. These are the two independently proved inputs
to `CoproductDescent`, used by `SheafDisplayFamilyDescent` to give family descent
and the jointly-covering stack. The stack theorem assumes neither an answer
field nor a display descent equivalence supplied by a caller.

Recovery is natural in arbitrary descent maps. `recoveryNaturality` compares it
with refinement and base change; `singletonComparison` identifies chosen
recovery with the explicit singleton construction. The optional
`Internal.CoherentDisplayDescent` module connects this equivalence with coherent
codes on the context's element site through `SheafSlice`. It imports the
coherent classifier separately so ordinary display descent has no dependency
on torsors or the classifier. Original-site presentation comparisons are a
separate concern of #665.

The category and its pullback comparison allow independent base, hom and fiber
universes. The descent construction uses fibers in `Type (max u v)`, as required
by the current sheaf and dependent-product infrastructure. Cover indices live
in that same universe. This does not claim arbitrary larger-fiber descent.

## Checked applications and hypothesis control

`Examples.SheafDisplayDescent` uses a proper two-member cover of the constant
Boolean sheaf; neither member covers alone. A fiber map collapsing Booleans to
false is proved noninvertible, both globally and after passage to descent data.
Recovery squares cover that map, coherent codes, direct displays and two
successive nonidentity base changes. The empty family over the empty context
has a descent equivalence. Over the nonempty Boolean context, empty descent
fails faithfulness, separating the joint-cover hypothesis from the conclusion.

## Reuse and next consumers

The action-independent proofs formerly inside `SheafTorsorDescent` now
specialize the shared compatible-section construction. Torsor action,
equivariance and principality stay in the torsor module, with its public names
preserved. General family-stack and recovery lemmas moved without renaming to
`SheafFamilyDescentCore`, leaving torsor and quotient instances in the original
module. The independent consumer therefore tests shared descent machinery
without inheriting an action or assuming every map invertible.

Associated bundles can target this display category and reuse its all-map
recovery. Cocycle classification (#670) can compare its transition-data
presentation with this construction, while keeping groupoid-specific hypotheses
explicit. Neither application is implemented by the display stack theorem
alone. There is no evidence here requiring a second general descent abstraction
or an increase in Lean resource budgets.
