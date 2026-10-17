# FRP artifact import

Imported on 2026-10-17 from `/home/vlad/Downloads/frp/`. The five supplied
files in this directory are byte-for-byte originals. Their verification
warnings describe the producing conversation. They are historical evidence,
not modules in the current build.

| Original | Content | Maintained copy |
|---|---|---|
| [frp-chat.md](frp-chat.md) | Two responses: push-pull FRP analysis and design; equivalence of event denotations | This historical record |
| [FRPSpec.lean](FRPSpec.lean) | Real-time behaviors, finite ordered batches, finite past support, strict switching, representation obligations | [Spec.lean](../../../Applications/FRP/Spec.lean) |
| [FRPEquivalence.lean](FRPEquivalence.lean) | Chronological co-lists, time-indexed batches, grouping/flattening and operation preservation | [Equivalence.lean](../../../Applications/FRP/Equivalence.lean) |
| [README.md](README.md) | Mathematical arguments and original verification limits | This historical record |
| [ordered_event_bind_counterexample.py](ordered_event_bind_counterexample.py) | Failure of associativity for stable chronological bind with ordered ties | This historical record |

The two event presentations in `Equivalence.lean` are sorted finite-or-infinite
sequences of timestamp/value pairs and functions from time to finite-or-infinite
ordered batches. `eventEquiv` proves equivalence precisely when each batch
occurrence has finitely many predecessors. `totalEventEquiv` restricts both
sides to finite histories. Mapping, snapshot, strictly-before histories, and
switching have preservation proofs. The behavior operations are pointwise.

This is not an equivalence of complete executable FRP systems. The conversion
from finite co-lists to the native `List` model in `Spec.lean` and a stable merge
preservation theorem remain mathematical arguments in the historical notes,
not checked bridges between the two files. Neither file implements a scheduler,
`predicate`, or `integral`. Infinite simultaneous batches and Zeno sequences
are admitted by the raw equivalence and excluded by finite history; the retained
examples prove that distinction.

The advanced implementation discussion is in the first response, section 3 of
the chat. It proposes reactive normal form, explicit knowledge frontiers,
push-driven phase changes, pull-driven evaluation, and a pure transition-system
scheduler. It lists soundness, progress, cancellation, and ownership obligations.
`Spec.lean` contains prefix and reactive-normal-form specifications, but those
runtime obligations have not been discharged.

## Compatibility and verification

The artifacts fit the repository's denotational application layer. Their
noncomputable mathematics does not require a toolchain change. The operation,
semantic equality, and preservation separation follows the direction of Felix's
[Homomorphism](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda)
and [MakeLawful](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
at the repository's pinned reference revision.

This import does not establish full architectural parity with Felix. `Raw` and
`Homomorphism` bundle a specialized FRP signature over `Type` and a function
interpretation. They do not supply Felix's general object maps, separate
per-structure preservation interfaces, or general law transport. Future library
development should express these through the shared `SquareKit` interfaces.
The generic order-enumeration proof is reusable independently of real time.

[Examples/FRP.lean](../../../Examples/FRP.lean) checks one existing integration:
`mapSquare` packages `OldEvent.group_map` in `Squares.Square`, and `map_twice`
uses square composition to transport two successive maps. Other retained cases
check that a change at time 2 still gives the initial value at time 2, and that
simultaneous merged occurrences remain `[3, 7]` in that order.

The first compiler run rejected both drafts. Repairs quote the reserved `at`
field, update local-instance syntax, make batch operations explicit, and repair
dependent transports, subtype coercions, and inference. The original theorem
conclusions and carrier restrictions are preserved. Unused order assumptions
on pointwise behavior equations and elementary occurrence observations were
removed. No admissions or new axioms were added.

Statement review checked the general linear-order assumptions, the additional
`NoMaxOrder` requirement for deriving admissibility from finite history, both
inverse laws, order and multiplicity preservation, and the strict `<` switching
boundary. Existing infinite-batch and Zeno specializations exercise the carrier
equivalence without falsely claiming finite history. The new square composition
case consumes the public mapping theorem.

The maintained files and examples are imported by `SquareApplications` and
covered by the normal source check and exhaustive `ProofAudit`. Reproduce with
`direnv exec . ./check.sh`. Run the historical Python example with
`direnv exec . python3 docs/history/frp/ordered_event_bind_counterexample.py`.

Import validation passed with Lean 4.35.0 and the pinned Mathlib: `lake build`,
the full 96-module source recheck, and the exhaustive audit of 6,043 kernel-safe
declarations. The transitive axiom union was exactly `propext`, `Classical.choice`,
and `Quot.sound`. The Python counterexample passed its assertions. The historical
copies were compared byte for byte with all five supplied files.
All four audit regression cases also passed; the three rejection cases were
run in parallel through the existing test helper.
