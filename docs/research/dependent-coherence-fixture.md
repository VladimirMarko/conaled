# Dependent coherence comparison: retained obligations

This inventory was written during phase B of [#292](https://github.com/VladimirMarko/conaled/issues/292), after the bounded construction. It records the public obligations pinned by the task at baseline `2525b12052e4c85c57f9050dbf18f7a36ba2ef19`. It is not a prospective author trial or a claim that this inventory was committed before implementation. The separate [external memo](dependent-coherence-discovery/292-external-memo.md) and source log were frozen before local inspection, then preserved in commit `4c0ac58d0c6f71a4de4033166349aa6b2ea03f1b` before local implementation.

| Baseline artifact | Git blob or SHA-256 | Retained obligation |
|---|---|---|
| `SquareKit/Internal/PathTransport/UniversalTransfer.lean` | Git blob `e91f71363556927c54a723ef310bddcc3789aeed` | `Typed.Authoring.UniversalTransfer.proof`, generated transport/concatenation identity; `GroupoidModel.UniversalTransfer.transport_concat`, its semantic interpretation |
| `Examples/DependentCongruence.lean` | Git blob `b71d57cda81162d1671dba3fbbfbffacb63ad013` | `DependentCongruence.DependentArguments.dependentPair`, a generated substitution conversion whose second component depends on the first; retained first-path-reflexive associativity specialization |
| `SquareKit/Internal/PathTransport/Typed.lean` | Git blob `8327aa0a4606b63aaf88046a8c1428ff8f7403f8` | `TmEqDeriv.subComp` and generated substitution conversion composition, preserving raw syntax and model-parametric annotations |
| `docs/research/dependent-congruence-repair.md` | SHA-256 `c31f8658f796918d707c4e050e3d653a7bd213a3aa1364793849e8db40a2e638` | Known substituted-versus-fresh annotation failure and outstanding general associativity, interpretations, diagnostics and handoff |

These files are unchanged by #292. The archived #106 work and #107 pause remain the source of the failure record. No #108 theorem was selected or prepared.

The new [boundary examples](../../Examples/LocalUniversesBoundary.lean) retain the fixed transport derivation under two arbitrary generated substitutions and the dependent substitution conversion under two further compositions. They exercise existing rules; they do not construct fresh named concatenations or discharge the following outstanding comparison.

For a concatenation command `c` and ambient substitution `σ`, the semantic annotation obtained by substituting the existing J term must be compared with the annotation of a freshly reconstructed command on substituted arguments. `Model.j_sub` provides a canonical map between pulled-back path telescopes. The existing term instead contains the composite of its original endpoint substitution with `σ`. The missing work is factorization through that canonical map and comparison of the pulled-back and fresh telescopes, motives, and branches. Raw substitution equality, generated conversion, semantic annotation equality, and an inhabitant of an identity type remain distinct obligations.

`pairingConverted` and `substitutionCongrAt` require callers to align raw types and both semantic annotations with a common type. `PathCommand.argumentsCongr` compares arguments of one fixed command. These facts do not establish the cross-presentation comparison. The new Type-family positive examples do not alter this failure record. The new decoded-equality/presentation-inequality example independently rejects an equality-reflection shortcut; it is not a reproduction or impossibility proof of the historical #107 obligation.
