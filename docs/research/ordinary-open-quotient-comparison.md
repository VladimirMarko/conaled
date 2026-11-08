# Ordinary-open labels and quotient arrows

Issue [#363](https://github.com/VladimirMarko/conaled/issues/363) constructs the
ordinary-open comparison identified by the
[consumer assessment](architecture-scaling-study/orbifold-consumer-assessment.md).
The forward map is the existing `ordinaryLocallyConstant`. Its inverse glues
constant sections on the open fibers of an independently supplied locally
constant function. This is a bounded geometric control for #362 and #100.

## Semantic contract and construction

For every small group G and ordinary principal-open domain U,
[`ordinaryLocallyConstantEquiv`](../../SquareKit/SmoothConstantComparison.lean)
identifies sections of the existing sheafified constant group with
`LocallyConstant (Points U) G`. Both inverse laws are proved. The forward map
is definitionally `ordinaryLocallyConstant`, with a public computation lemma.
Naturality covers every admitted ordinary smooth map, in both directions;
multiplication is preserved. The empty-domain section is unique.

The input hypotheses are the existing group structure and domain. The inverse
does not require finite G, connected U, chosen local sections, or an assumed
comparison theorem. `openDefining` supplies principal descriptions of the open
label fibers. `sheaf_exists_unique` glues their constant sections. Different
fibers have empty overlap, where the empty cover proves agreement. Injectivity
uses `covering_local_inclusion` on the intersection of two constant-label image
sieves, then `cover_jointly_epic`. Consequently the construction proves point
detection for these particular sections. It makes no such claim for arbitrary
sheaves or arbitrary presentation quotients. These are classical constructions
within the existing Lean smooth-site foundations, not a constructive port.

[`diskChartArrowEquiv`](../../SquareKit/SmoothOrdinaryQuotient.lean) composes
Yoneda, the section comparison, and the existing `chartArrowEquiv`. For smooth
maps m,n from U into the disk, its output is a locally constant C4 label k with
`diskMap (k x) (n x) = m x` at every ordinary point. The action equation is
reflected using the already proved full faithfulness of the ordinary
representable target. The proof retains equality of sheaf maps at all stages.
`manifold_arrow_recovers` in the
[isotropy examples](../../Examples/SmoothOrdinaryIsotropy.lean) proves that
conjugating the actual manifold interpretation by the principal isomorphisms
returns the same embedded map used here; it consumes `homEquiv_principal`.

`diskChartArrowEquiv_label` identifies the designated forward label with
`ordinaryArrowLabel`. Its identity, composition, restriction and inverse laws
are proved for arbitrary groups and actions. The underlying all-stage laws
live in [`SheafActionQuotientLabels`](../../SquareKit/SheafActionQuotientLabels.lean).
Right translation means that arrows labelled k then l compose with label k*l.
The relation is m = k·n, so a conventional forward action label is k⁻¹. These
laws do not use C4 commutativity. `chartArrowEquiv` itself already had inverses;
the newly constructed inverse is the ordinary section comparison.

## Checked geometric controls

The [ordinary comparison examples](../../Examples/SmoothOrdinaryComparison.lean)
start with an independent sign function: identity on the negative component of
the punctured line and c on its positive component. `signLabel_inverse` proves
that the new inverse is the existing `SmoothClutching.transition G c`.
`varyingOriginArrow_labels` constructs an actual disk quotient arrow through
the new equivalence and computes its labels at -1 and 1 as identity and the
quarter-turn. `varyingOriginArrow_not_constant` rules out a constant-only
implementation. `empty_inverse_unique` supplies a concrete empty domain.

The isotropy examples use the zero-dimensional ordinary domain and compare its
actual arrow labels with the existing real-stage stabilizer comparison.
`ordinary_origin_count` retains four arrows; `ordinary_regular_identity`
retains trivial stabilizers away from the origin. `ordinaryIneffectiveArrowEquiv`
retains every locally constant label on any ordinary open, with
`ordinary_ineffective_distinct` distinguishing two point-domain arrows despite
their identical action. The derivative and forward-label examples retain the
existing inverse convention through the new comparison.

`nontrivialObject` equips the existing clutching torsor on the doubled-origin
sheaf base with the ineffective action's invariant zero map. Its no-section
proof is the existing torsor theorem. `nontrivialRecovered_not_chart` proves
that its actual canonical descent recovery still cannot be globally charted.
`nontrivial_comparison_control` connects that result with the newly recovered
transition. The doubled-origin object is not replaced by an ordinary global
chart.

## Named refinement contract

The selected refinement replaces each sign region by its intersections with
`x ≠ -1` and `x ≠ 1`. These principal opens cover because those two equalities
cannot hold together. On each sign region one member removes a point and the
other covers that region. This is an explicit, redundant refinement, not a
claim about minimal covers.

`signRefinement_square` proves the ordinary inclusion square.
`signCoverRefinement_square` proves the square of actual coproduct cover maps.
`signSplitRefinement_square` lifts it to the split cover displays used by
canonical descent. `signRefinement_restriction` is equality of the restriction
functors, so it includes the actual local objects and arrows, not just their
isomorphism classes. The compatible refined labels are glued by the same
sheaf construction; `refinedTransition_recovers` identifies that new gluing
with the original transition.

[`SmoothOrdinaryCoverRecovery`](../../SquareKit/SmoothOrdinaryCoverRecovery.lean)
constructs the locally surjective split displays from the covers and uses the
existing effective quotient descent. For any quotient object over the
punctured line, `signRefinementRecovery_commutes` compares the two canonical
descents using their actual recovery arrows. `signRefinement_arrows` compares
recovered arrows, while `signRefinement_arrows_square` proves their naturality
with those object comparisons before global recovery. The chosen arrow
transport is explicitly defined through `canonicalArrowEquiv`; it is not an
unrelated equivalence between endpoint types. Combined with the restriction
functor equality, these are the named canonical-recovery refinement contract.

This does not construct a general change-of-cover functor on arbitrary,
independently supplied descent data or its higher coherence laws. If that
stronger interface becomes necessary, #100 owns its geometric follow-up in
coordination with #36; it is outside #363's bounded contract.

## Statement review and remaining boundaries

The section statements quantify over the existing general group and every
ordinary domain, including empty and disconnected domains. Naturality
quantifies over actual smooth maps admitted by `EuclideanOpen.Domain`.
The arrow equivalence quantifies over every pair of ordinary disk maps, not
only automorphisms or constant maps. Its relation uses the specified action
and orientation. The generic composition law prevents the commutative C4
specialization from masking an order error. The example's sign function was
specified independently of the sheaf inverse, then connected to it. The
refinement results specify their local restriction and canonical-recovery maps
rather than assuming descent correctness as a field.

The new modules enter the normal public import closure through
`Examples.SmoothOrdinaryComparison`; the repository build and exhaustive proof
audit apply. Candidate execution receipts belong to the issue's implementation
handoff, rather than being inferred from this mathematical description.

Properness and étaleness of a Lie groupoid anchor, general Weil-square
instances, a joint higher smooth model, and interpretation of the exact Agda
source proof remain separate obligations. Finite stabilizers do not prove
properness. The external obstruction investigation remains with its owner.
The archived Agda checkpoint supplied consumer evidence; it was not developed
to conaled's standards and does not establish integration readiness.
