# Timing composition migration (#22)

The baseline is `96fe25784c6664880d1dc2b9c6b9814a1712fb12`, including the
relational bridge from #12. This slice changes the proof used by the existing
`Applications.Timing.Digital.compose`; every interpreted circuit composition
therefore consumes the shared bridge. Analog functions, Boolean functions,
and interval-linear timing maps retain their definitions.

| Declaration | Before | After / remaining obligation |
|---|---|---|
| `Digital.object`, `Digital.relation` | Stability relation and local arrow adapter below the gate definitions | Same declarations moved before composition so the existing operation can consume them; no new adapter obligation |
| `Digital.compose` | `g.correct (f.correct h)` assembled the local certificate | `SquareKit.RelationalCategory.ops.comp` composes the existing relation adapters, and `SquareKit.RelationalCategory.witnessMap.map` transports the arbitrary input witness; its output property supplies the certificate |
| `Digital.square_compose` | Used `Relational.witness_compose` directly | Uses `SquareKit.RelationalCategory.witnessMap_laws.comp` through `SquareKit.Comma.Exact.toSquare`; same statement |
| `Digital.relation_compose` | Extensional equality of the two horizontal maps | Retained, relating the existing operation to shared relational composition |
| `Digital.unary`, `Digital.binary`, `Digital.constant` | Local shifted-time and intersection stability proofs | Retained, including `Interval.contains_shift` and `Interval.contains_add`; the shared bridge cannot establish primitive signal semantics |
| `Digital.pair`, `Digital.first`, `Digital.second`, `Digital.terminate` | Local product/projection/terminal stability and timing linearity | Retained; no new digital cartesian abstraction is introduced |
| `Digital.matrix_stable`, `Digital.matrix_compose` | Matrix representation of interval-linear maps | Retained with unchanged statements and coordinate obligations |
| `Circuit.compile_stable`, `Circuit.compile_matrix_stable` | Arbitrary source programs and stable input environments | Retained; interpreted circuit composition now uses the shared certificate above |
| `Examples.RelationalBridge.timing_composition`, `timing_witness_composition` | Generic timing bridge cases from #12 | Retained as public arbitrary-input composition evidence; now exercised by the actual application operation |

Prefixes in the table are `Applications.Timing` except `Circuit`, which is
`Applications.Circuits.Circuit`. This migration replaces local certificate
assembly and the direct witness-composition proof. Moving the two adapters is
accounted for separately and is not claimed as deleted proof work.

## Checked applications and statement review

`Applications.Timing.Examples.delayed_double_not` uses `Digital.compose.correct`
for two existing unary gates with delays 1 and 2 and operation `Bool.not`.
Two Boolean inversions return the original value; endpoint addition gives
`[lo + 3, hi + 3]`. The statement quantifies over every rational endpoint,
Boolean value and arbitrary signal stable on the supplied interval. It does
not assume global stability, ordered endpoints, or a conclusion stronger than
the input stability condition. The public result is used before reducing the
gate computations. `delayed_double_not_constant` discharges that premise for
a constant true signal on `[0,1]` and obtains `[3,4]`, so the contract is usable
on a nonempty window. The missing connection before this change was that the
application's composition certificate did not consume the #12 adapter; the
expected mathematics was already provable locally.

`Digital.compose.correct` retains quantification over arbitrary source and
target shapes, signals, timing vectors, and values. The witness includes both
semantic data components; no value is chosen from an unstable signal and no
witness erasure is asserted. `Digital.square_compose` retains its original
exact equality of squares. The moved `object` and `relation` definitions are
unchanged. Timing still cannot inspect values and values cannot inspect timing.

The existing `Adders.fullAdder_stable`, `fullAdder_matrix`,
`hazard_at_seven_tenths`, `hazard_before_and_after`,
`carry_path_nonempty_iff`, and `repaired_carry_path` remain checked. Inverted
setup/hold bounds remain distinct. There is no feedback or physical model
extension.

## Architecture correspondence

At Felix revision `6f36d28097db7ea5f5df3263db3e8be08f74e490`,
`Felix.Homomorphism.CategoryH.F-∘` expresses preservation of composition.
The shared `MapLaws.comp` consumed here is the corresponding interface; this
client supplies stable-signal arrows rather than another hierarchy of maps.
The pinned `Homomorphism.agda` definition and its composition construction were
inspected. This slice uses the already established #12 bridge, and adds no
claim to implement Felix's unrelated unfinished closed transport or feedback.

## Validation

Run from this ticket worktree through the declared direnv shell:

- `direnv exec . lake build Applications.Timing.Examples`
- `direnv exec . ./check-foundation.sh`
- `direnv exec . ./check.sh`

All three commands passed. The fresh check rechecked all 86 modules and the
exhaustive transitive audit admitted only `propext`, `Classical.choice`, and
`Quot.sound`. A `lake env lean` inspection also checked the elaborated types
of the changed composition and new applications, and the new applications
use only those permitted foundational axioms. No runtime behavior or
proof-audit infrastructure changes require extra regression fixtures.
