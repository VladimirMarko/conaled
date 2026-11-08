# Complete, uniformly realizable certificate families

[#388](https://github.com/VladimirMarko/conaled/issues/388) constructs P4 in the
assembly model. Naturals and lifted naturals satisfy all-context completeness.
Tracked function assemblies supply exponentials, and completeness is closed
under exponentials and retracts. A context-dependent bound filter constructs
the varying certificate family and its relative extension theorem.

The comparison is with the uniformly realizable part of the existing external
certificate state space. That restriction is necessary: a checked diagonal
state is total and bounded but has no uniform realizer. The native external
client remains unchanged. P5 / #389 still owns the certificate-state algebra,
countdown arrow and comparison of its extension-selected solution with the
external selected solution. #371 remains open.

## Source and exact model

Van Oosten and Simpson, [*Axioms and (counter)examples in synthetic domain
theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf),
APAL 104 (2000), 233–278, describe finite/full cut realizers in §3, pp.266–268.
Definition 1.11, p.244, uses an exponential restriction isomorphism. Theorem 3.3,
pp.268–269, uses self-reference and a Rice–Shapiro-style monotonicity argument
for a different target. The specialized lifted-natural argument here follows
our [continuity roadmap](assembly-cut-continuity-roadmap.md); it is not a
transcription of that theorem or an import of the effective topos's internal
logic. The retained PDF has SHA-256
`066a36aa48fc38b5105637e8b77ef0b34de9e61751010492b922946b1ce9c2e2`.

The implementation uses the accepted assembly category, inherited-realizer
subassemblies, program-index lift and cut objects. Arrow equality is equality
of underlying functions; program indices are tracking evidence, not part of
arrow equality. Every realizer of an input must be handled. Finite cuts admit
all indices whose domains are the corresponding initial segment, with arbitrary
returned labels. Full cuts admit every total index.

Function objects, categorical products and completeness closure are polymorphic
in the assembly carrier universe. The concrete natural-number and certificate
construction is in `Assembly.{0}`. Its context Γ is any assembly in that
universe; Γ need not have a coded carrier or a global inhabitant. No arbitrary
slice-completeness, local cartesian closure, universe classifier, or general
complete-implies-well-complete theorem is assumed.

## Constructed claims

| Claim | Checked interface |
|---|---|
| Uniform function objects and beta/eta | [AssemblyFunction](../../SquareKit/AssemblyFunction.lean): `function`, `evaluation`, `curry`, `uncurry` |
| Standard categorical packaging | [AssemblyCartesian](../../SquareKit/AssemblyCartesian.lean): chosen terminal/products, `CartesianMonoidalCategory`, `functionAdjunction`, `MonoidalClosed` |
| All-context and exponential completeness agree | [AssemblyFunctionComplete](../../SquareKit/AssemblyFunctionComplete.lean): `cutRestrictionIso`, `cutComplete_iff_restrictionIso` |
| Finite-observation continuity | [AssemblyCutObservation](../../SquareKit/AssemblyCutObservation.lean): `cut_growth`, `cut_finite_witness`; [AssemblyCutContinuity](../../SquareKit/AssemblyCutContinuity.lean): `cutArrow_mono`, `cutArrow_infinity_iff` |
| Concrete completeness | [AssemblyNatComplete](../../SquareKit/AssemblyNatComplete.lean): `nat_cutComplete`; [AssemblyLiftNatComplete](../../SquareKit/AssemblyLiftNatComplete.lean): `liftNatExtension`, `liftNat_cutComplete` |
| Exponential/retract closure | [AssemblyCompleteClosure](../../SquareKit/AssemblyCompleteClosure.lean): `function_cutComplete`, `retract_cutComplete` |
| Bound filter and complete fibers | [AssemblyBoundedSequences](../../SquareKit/AssemblyBoundedSequences.lean): `sequenceFilter_fixed_iff`, `boundedSequences_complete`, `bounded_extension` |
| Relative extension and substitution | [AssemblyBoundedFamily](../../SquareKit/AssemblyBoundedFamily.lean): `boundedFamily_complete`; [AssemblyFamilySubstitution](../../SquareKit/AssemblyFamilySubstitution.lean): `extendFamily_reindex`, `reindexFamilySection_comp` |
| Full-record state comparison | [AssemblyCertificateFamily](../../Examples/AssemblyCertificateFamily.lean): `stateComparison`, `recover_coordinate`, `forget_injective`; [AssemblyCertificateContext](../../Examples/AssemblyCertificateContext.lean): `familyComparison` |
| Proper parameter embeddings | [AssemblySequenceTransport](../../SquareKit/AssemblySequenceTransport.lean): `boundedShift`, composition and non-surjectivity; [AssemblyCertificateTransport](../../Examples/AssemblyCertificateTransport.lean): `forget_shift` |

The inverse to restriction is tracked: completeness is applied in context
`X^I` to evaluation, then curried. Conversely a tracked restriction inverse
extends every context by curry/uncurry. This proves the specified equivalence
without replacing all-context completeness by extension of global points.

## Why the concrete extension works

A source tracker first emits a lifted-value program; `liftObserver` then runs
that program. Its exact graph says the observed result is the arrow's selected
value. Two self-reference constructions establish continuity. `cut_growth`
forces a successful finite observation to persist on larger cuts.
`cut_finite_witness` uses the least successful bounded observation to exhibit a
finite cut witnessing any value forced at infinity. Mathlib's `fixed_point₂`,
`evaln_sound`, `evaln_complete` and `evaln_mono` discharge these steps. An `evaln`
bound is a bound on numeric intermediates, not elapsed execution time.

The extension compiler dovetails triples consisting of a candidate finite
length and two evaluation bounds. Length zero is always accessible. Positive
length n is accessible after the source cut terminates at n−1. A successful
observer run on the canonical cut of length n supplies a value. Flat
monotonicity makes every successful triple agree, so taking the first success
preserves the selected value. The finite-witness theorem proves uniqueness at
infinity. Naturals are simpler: their finite-cut arrows are constant along each
context fiber, and the same argument fixes their full-cut extensions.

[AssemblyCutSearchPrograms](../../SquareKit/AssemblyCutSearchPrograms.lean)
uses fixed universal templates and computable code transformations, uniform in
the source tracker, context realizer and cut index. `liftNatExtensionProgram`
produces a program without waiting for that program's result. Thus bottom has
a realizer too. Classical choice used to describe the unique semantic value
at infinity does not replace this tracking proof or select separate opaque
programs for each input.

## The certificate boundary and uniformity

The ambient sequence assembly `D = (L N)^N` contains tracked maps N→LN. For a
tracked capacity `capacity : Γ→N`, the filter retains a defined coordinate v
exactly when `v < capacity γ + k + 1`. It never decides whether a partial
coordinate will terminate. The filter is idempotent; its fixed points are
exactly the independently stated bounded sequences.

Each fixed-capacity fiber is a retract of D. For the varying family, extend a
tracked section in D and compare its extension with the filtered extension.
Uniqueness forces equality, so the extension factors through the bounded
family while retaining its base. `boundedFamily_complete` states restriction
bijectivity for these base-retaining sections. `extendFamily_reindex` proves
compatibility with every tracked parameter substitution, and repeated
substitution composes. This proves the required relative theorem without
assigning a fictitious global bottom to the total capacity family.

[UniformCertificateStates](../../Examples/UniformCertificateStates.lean)
defines admission independently on the original `State n`: one program must
emit a value program uniformly for every coordinate, with exactly the graph
of the selected certificate value. The assembly comparison preserves those
realizers. Its context version pairs context and state realizers, so an admitted
arrow must produce them jointly. It is not a collection of untracked choices
for separate parameters.

`recover` reconstructs each full certificate using its bounded value and the
canonical trace required by `Cert.steps_eq`. `coordinate_injective` and
`forget_injective` prove faithfulness for full external states. The two proper
capacity embeddings remain actual tracked arrows; their commuting equation
with the external `transport` preserves `Part (Cert n k)`, not just domains.
[NonUniformCertificateState](../../Examples/NonUniformCertificateState.lean)
constructs a total bounded diagonal state outside `UniformRealizable`, proving
that the unrestricted external state space cannot be silently identified with D.

## Checked uses and remaining obligations

[CompleteAssemblyFunctions](../../Examples/CompleteAssemblyFunctions.lean)
instantiates the formerly conditional selected-17, bottom and algebra-transport
cases with constructed completeness. [CompleteAssemblySearch](../../Examples/CompleteAssemblySearch.lean)
checks a full-cut program returning label 99, successful selected value 17,
divergence on the zero cut, and an empty context.
[CompleteCertificateFamily](../../Examples/CompleteCertificateFamily.lean)
checks a jointly tracked capacity-varying section, extension at infinity, full
record recovery and arbitrary parameter substitution. The transport cases retain
value 3 with trace `[2,1,0]` after the two proper changes. Bound-filter cases both
reject and retain a value at different coordinates.

These are construction and preservation results. The explicit selected-state
records used in transport cases are not yet the result of an internally
constructed countdown selector. P5 must build that algebra and arrow, prove
membership of its selected state in this uniform family, and compare its selected
partial graph with the unchanged external cpo client. Operational adequacy of
a separately specified machine and general productivity claims remain separate.
The existing Boolean control still excludes the combined complete-plus-strict-
algebra hypotheses admitting negation; it does not claim Boolean incompleteness.
