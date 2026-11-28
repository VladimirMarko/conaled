# Decoder recovery across sheafification

The finite-state decoder has codes `Bool`, with one state over `false` and two over `true`. On the open-set site of a discrete two-point space, its raw codes and total state space are constant presheaves. A local-state consumer needs one code on one component and the other code on the other component. Restricting the consumer to global constant codes excludes this family.

The checked construction replaces both codes and total states by locally constant sheaves. A local state over a locally varying code is a locally constant total-state section whose projection is that code. The mixed code has a state section whose restrictions are the selected state 0 over `false` and state 1 over `true`, and is outside the image of the global constant-code unit. `localFamily` exposes the decoder through `SplitSheaf.ofDisplay`; `localFamilyTotalIso` reconstructs its total sheaf and retains the display equation. This is a concrete finite decoder, not a classifier for every family or a universe closed under arbitrary type formers.

The reusable definitions and proofs are in [DecoderSheafification](../../SquareKit/Internal/DecoderSheafification.lean); the [finite-state client](../../Examples/DecoderSheafification.lean) supplies the separating case. This bounded construction uses `TopCat.{0}` and `Type 0` states on its open-set site. It does not quantify over arbitrary sites or universe levels.

The two different raw constant codes do not themselves form a raw matching family on the singleton cover: their restrictions still differ at the empty overlap. Sheafification first makes the locally forced identifications and then admits the mixed section. The restriction checks describe the resulting local decoder, not a failed raw gluing problem with a compatible family.

## The two recovery equations

Write `P` for the raw code presheaf, `E` for its total decoder, and `d : E → P` for the display. Let `P#` and `E#` be their sheafifications. The constructed decoder is `d# : E# → P#`. Its unit comparison is

```text
d ; ηP = ηE ; d#.
```

The construction uses the existing [locally constant sheaf interface](../../SquareKit/LocallyConstantSheaf.lean), its [unit comparison](../../SquareKit/LocallyConstantGroup.lean), and Mathlib’s `toSheafify`, `isoSheafify` and `toSheafify_naturality`. The implementation identifies sheafification of a constant presheaf with the existing locally constant sheaf through `constantIso`. `constantIso_unit` identifies the displayed constant-section maps with the actual sheafification adjunction units. The comparison therefore concerns those units, not alternative maps with the same endpoints.

Exact original-decoder recovery would require the canonical map

```text
E → P ×_{P#} E#
```

to be an isomorphism. On an original code `c` over an open `U`, this is the map `fiberUnit` from `D c` to local state sections above the constant code `c`. At the empty open, the two states over `true` have equal images. `exact_recovery_obstruction` proves that this canonical map is not injective on that fiber. `unit_square_not_pullback` proves directly that the displayed square fails Mathlib’s `IsPullback` predicate, by evaluation at the empty open.

The obstruction does not depend on the selected locally constant extension. Every sheaf has a unique section over the empty open. For any sheaf-valued total space `S` and any presheaf map `E → S`, two distinct original states over the same code have equal empty-open images. Hence no such map can provide exact recovery of the original decoder there. `exact_recovery_requires_subsingleton` derives a necessary condition from an arbitrary proposed pullback square with a sheaf-valued total space: every original constant fiber would have to be a subsingleton. This is a necessary condition, not a sufficient extension criterion. The missing hypothesis is compatibility of the original display with local identification, not an unavailable proof of sheafification existence.

This distinguishes loss of original states from the useful recovery of sheafified states. The new mixed code supplies an independent control for added sections. Neither effect should be hidden by calling sheafification an unchanged code representation.

## Restriction, maps and operations

Restriction acts by precomposition on locally constant sections. `fiberUnit_restrict` proves its compatibility with original states. A fiber map `f : ∀ c, D c → D' c` acts pointwise on total states; `mapState_unit` and `mapState_restrict` prove the unit and substitution equations. Identity and composition of fiber maps are preserved as well.

On an inhabited open, evaluating a constant section at a point recovers the original state. `fiberUnit_injective` proves this, and `state_maps_recovered` recovers maps of fibers from their action after the unit. This limited faithfulness does not repair the empty-open obstruction. Pointwise reversal on the one- and two-state fibers is a selected operation preserved by the extension. It exchanges the two states over `true`, and its involution law is proved for every local state, including locally varying codes. No preservation theorem for arbitrary dependent operations, products or universe structure is inferred from this example.

For already-sheaf inputs, `alreadyLocal` is `isoSheafify`; its forward map is the actual unit. The checked inverse recovers sections and the decoder map. This retains the simpler already-sheaf route of #646 and does not require changing its clients.

## Classification and arbitrary sites

The existing `HomSystem` construction classifies maps into a presheaf `B`. Its `codesIso` identifies its codes with the explicitly raised presheaf `B`, and `codesIso_code` retains the represented-map formula. The finite example uses its sheafness equivalence to show that the corresponding raw `HomSystem` codes are also not sheaves. Sheafification does not alter that prior theorem or retroactively make raw codes local.

For arbitrary sites, a sheaf-level represented-section argument uses sheafified representables and the sheafification/Yoneda adjunction. The existing `SheafGroupoid.sectionParameter` and `sectionEquiv` demonstrate that route. It does not give the old presheaf generic-element reduction unchanged, and it does not prove that an existing decoder extends with exact pullback recovery. The displayed unit equation and obstruction are separate from merely using established sheafification.

The original two-point open site includes empty and joint covers. No change to the sheaf-parameter singleton-cover site is made here; that comparison retains its separate owner. This investigation is not a prerequisite for every use of sheafified representables or sheaf coproducts under #652/#657.

## Disposition and limits

Adopt the locally constant finite-state decoder when the consumer needs local codes and accepts sheafified state recovery. Reject exact original-state recovery for the raw constant decoder: the obstruction is proved, including for any alternative sheaf-valued total extension. Investigate relative locality conditions on other decoder presentations under #647 before requiring their unit squares to be pullbacks. A presentation which already identifies empty-open states and admits the necessary local state sections may behave differently; that is a new construction and recovery proof, not a consequence of this negative result.

