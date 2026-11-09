# Finite-action proper étale presentations

Issue [#435](https://github.com/VladimirMarko/conaled/issues/435) extracts the
quarter-turn disk's geometry into
[`Orbifolds.FiniteActionPresentation`](../../Applications/Orbifolds/FiniteActionPresentation.lean).
The disk API now specializes these constructions. The request and its original
scope are preserved in the [Agda consumer assessment](myers-feedback-2026-11-09-assessment.md).

## Inputs and constructed maps

The algebraic input is Mathlib `Group G` and `MulAction G M`. The action's
identity and multiplication laws supply the inverse equations; no new action
hierarchy is introduced. `Arrow G M` is `G × M`, with source `x`, target `g • x`,
unit `(1,x)`, inverse `(g⁻¹,g • x)` and composition `(h*g,x)` for `g` followed by
`h`. `composableEquiv` identifies `(G × G) × M` with the actual subtype of
composable arrow pairs, proving both inverse laws.

`asHom`, `ofHom` and `homEquiv` connect these coordinates to Mathlib's
`ActionCategory G M`. `ofHom_ident`, `ofHom_comp` and `ofHom_inverse` prove the
operation comparisons. `homEquiv` supplies both inverse laws for the
hom-type/anchor-fiber equivalence, retaining each group label.

The smooth interface takes a discrete topology on `G`, a real model with
corners `I : ModelWithCorners ℝ E H`, a charted space `M`, and
`∀ g, ContMDiff I I ∞ (fun x : M => g • x)`. Smoothness of inverse labels
constructs `actionDiffeomorph`. Thus callers provide an action and its ordinary
smoothness proofs, rather than separately asserting that its presentation is
étale. Open the scope `Orbifolds.FiniteActionPresentation` to use the canonical
zero-dimensional label charts. The arrow model is the product of that model
with `I`.

`sourceChart` and `targetChart` are actual partial diffeomorphisms on each
fixed-label component. `source_etale` and `target_etale` derive local
diffeomorphism; their `contMDiff` consequences supply smoothness of source and
target. `unit_smooth`, `inverse_smooth` and `compose_smooth` prove smoothness of
the remaining structure maps. Composition uses the explicit composable-pair
coordinates above. This does not claim an independently chosen manifold
structure on a raw equalizer subtype.

## The two hypothesis boundaries

`anchor_proper_of_compact` only needs topologies on `G` and `M`, compactness of
`G`, Hausdorff `M`, and continuity of `(g,x) ↦ g • x`. Its conclusion is exactly
Mathlib `IsProperMap` for `(g,x) ↦ (x,g • x)`. The proof factors source through
the first projection from `M × M`, uses properness of projection from the
compact label factor, and applies `isProperMap_of_comp_of_t2`. It never assumes
compactness of `M`, discreteness of labels, or any manifold structure.

`proper_etale` combines this with the discrete smooth construction. Its public
inputs include `Fintype G`, `DecidableEq G`, Hausdorff `M`, `IsManifold I ∞ M`,
and second countability of `M`. These expose usable finite data and the usual
countability convention; the underlying topological and local-diffeomorphism
theorems remain available under their weaker hypotheses. Standard product
instances construct the arrow manifold, Hausdorff topology and second
countability. No effectiveness, anchor injectivity, compact base, or compact
support assumption is present. The normed model need not be finite-dimensional
for these particular proofs.

Explicit finite data does not make the analytic construction constructive.
The disk's named `labelFintype` uses `Fintype.ofFinite` for the complex
root-of-unity labels. The real and complex analytic development has transitive
classical dependencies.

## Checked specializations and statement review

[`DiskPresentation`](../../Applications/Orbifolds/DiskPresentation.lean) retains
its public definitions and theorem statements, now delegating the charts,
structure maps, properness and categorical equivalences to the generic
construction. The existing
[`SmoothDiskPresentation`](../../SquareKit/SmoothDiskPresentation.lean)
comparisons remain in place: `smoothChartEquiv`, actual arrow families, inverse,
composition and restriction comparisons, plus canonical recovery. Existing
origin, regular-point, varying-label and noncommutative controls are retained.

The new [`Examples.FiniteActionPresentation`](../../Examples/FiniteActionPresentation.lean)
uses the trivial action of `S3` on the whole real line. `Trivial.presentation`
applies the generic theorem. `ineffective_noncompact` proves properness and
exhibits distinct arrows at every real point with the same anchor. The file
also checks `NoncompactSpace ℝ` and the arrow manifold/countability instances.
`noncommuting_composition` exercises the actual composable-pair coordinates:
swap 0/1 followed by swap 1/2 has label `h*g`; reversing it is rejected by its
action on label index 0, even though both labels act identically on the base.
`hom_roundtrips` specializes both inverse laws of the generic hom comparison.

The example-driven obligation was the missing connection: the old
`ineffective_control` combined disk properness with an unrelated ineffective
sheaf action. It could not supply properness of this real-line presentation.
The new proof instantiates the shared geometric construction itself. Existing
disk examples alone also could not detect noncommuting geometric label order.
The independently chosen swaps send index 0 to 2 in the required order and to
1 in the reversed order.

Statement review checked arbitrary base points and labels, multiplication
order, both equivalence directions, and the distinct topology hypotheses.
Smoothness is supplied uniformly for every group label, including inverses.
Neither an effectiveness hypothesis nor the desired local-diffeomorphism or
properness conclusion is packaged as an input field. The manifold examples
provide inhabited inputs and reject two plausible overclaims: anchor
injectivity and commutative label composition.

`Trivial.diagonal` specializes the same generic theorem to the trivial finite
group on `ℝ`, where the anchor is the diagonal. `Trivial.diagonal_map`
composes this result with the inverse homeomorphism `PUnit × ℝ ≃ₜ ℝ` to prove
properness of the ordinary map `x ↦ (x,x)`. Neither theorem claims anything about the
unrestricted internal `DPProper` predicate. The
[verified Agda obstruction](myers-properness-096-10-verification.md) still
constrains any proposed bridge. General manifold quotient-arrow comparisons,
descent, Morita invariance and a full synthetic/classical orbifold equivalence
remain outside this extraction.

## Validation and axiom ledger

The pinned environment is Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with the repository manifest's
transitive dependencies. Acceptance uses the committed-candidate build and
exhaustive proof audit described in the repository README. The orchestration
handoff retains exact candidate hashes and verification receipts. Focused
checks and the transitive axiom inspection below supplement that acceptance;
they do not replace it.

The focused build covered `Examples.FiniteActionPresentation` and
`Examples.DiskPresentation`, including the existing smooth quotient comparison.
`#print axioms` on the exported declarations gives the following transitive
sets. `P`, `C` and `Q` abbreviate `propext`, `Classical.choice` and `Quot.sound`.
Names in the first five rows belong to `Orbifolds.FiniteActionPresentation`.

| Declarations | Axioms |
|---|---|
| `source`, `target`, `compose`, `anchor`, `composableEquiv` | None |
| `unit`, `inverse` | P |
| `asHom`, `ofHom`, `homEquiv`, `ofHom_ident`, `ofHom_comp` | P, Q |
| `ofHom_inverse` | P, C, Q |
| `labelCharts`, `labelManifold`, `sourceChart`, `actionDiffeomorph`, `targetChart`, `source_etale`, `target_etale`, `unit_smooth`, `inverse_smooth`, `compose_smooth`, `anchor_proper_of_compact`, `proper_etale` | P, C, Q |
| `Orbifolds.QuarterTurn.DiskPresentation.{labelFintype, homEquiv, proper_etale}` | P, C, Q |
| `SquareKit.SmoothDiskPresentation.{smoothChartEquiv, chartEquiv_comp, chartEquiv_inverse, chartEquiv_restriction}` | P, C, Q |
| `Examples.FiniteActionPresentation.Trivial.{presentation, ineffective_noncompact, noncommuting_composition, hom_roundtrips, diagonal, diagonal_map}` | P, C, Q |

For reproduction after building the two example modules, import both into a
scratch Lean file and use `#print axioms` on each fully qualified declaration
above. The brace notation in the table abbreviates separate names; it is not
Lean syntax. No new axiom is introduced. The generic algebraic comparison's
smaller ledger does not remove the analytic specializations' classical inputs.
