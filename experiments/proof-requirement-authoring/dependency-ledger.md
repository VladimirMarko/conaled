# Prepared dependency assistance, route D only

This ledger was prepared manually by the task designer from the concrete source
proof bodies, then compared with Lean's printed terms and checked reference
replays. It is supplied evidence, not extractor output. Choosing an opaque lemma
boundary and choosing these tasks involved mathematical judgment. No generalized
interface or target instance proof is supplied here.

The boundary treats the following library lemmas as leaves. It does not unfold
their induction proofs or claim that native Lean kernel dependencies equal
mathematical requirements.

| Source | Opaque leaves used in body | Other proof/data operations |
|---|---|---|
| `Source.reverseBlocks` | `List.reverse_reverse x`, twice; `List.reverse_append`, at `(x,y++z)` and `(y,z)` | Equality symmetry, congruence under `fun t => (t ++ (y ++ z)).reverse` and `fun t => t ++ x.reverse`, equality transitivity, lambda binding |
| `Source.selected` | `List.append_nil x`, once | Symmetry, congruence under `List.length`, subtype constructor with first component `x` |
| `Source.selected_value` | No additional leaf | Definitional reduction of subtype first projection |

The full leaf statements at this boundary are:

```text
List.reverse_reverse: for every list x, reverse (reverse x) = x
List.reverse_append: for every list x,y, reverse (x ++ y) = reverse y ++ reverse x
List.append_nil: for every list x, x ++ [] = x
```

The `_ambient` argument in `Source.reverseBlocks` has zero occurrences in its
proof term. The first two equality steps do contain the reverse/reverse leaf;
do not relabel that dependency as an unused argument. The listed occurrence
counts are at the displayed source proof boundary, not a global dependency
minimization result. Decide and justify whether to keep or change that proof.
All operations and equality remain typed; preserve the selected subtype data.
