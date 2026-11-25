# Independent primitive visited-space expectations

Frozen before writing the new observer/proof implementation and before any
compiler feedback for this space increment. These are hand calculations from
the actual native TM0 move/write/none rules. No compiler or executable oracle
was used to choose them. Earlier source fixtures and clocks remain unchanged.

Coordinates refer to the initial head as origin 0 unless explicitly shifted.
An initial head cell is visited even on empty input. A move changes position by
exactly one; a write keeps position; a transition returning outer none adds no
new visited cell. Later absent prefixes also add no cells.

Two observations stay separate:

- **Visited:** the set of positions of the head during actual execution.
- **Input plus visited:** all declared initial input positions, even if their
  contents are blank or have not been read yet, together with visited cells.

| Case | Positions at successive prefixes | Exact visited cells | Input plus visited |
|---|---|---|---|
| Halt immediately, empty input | 0, then 0 after outer none and thereafter | `{0}`, size 1 | `{0}`, size 1 |
| Halt immediately, one present false input symbol in `Option Bool` | 0, then 0 | `{0}`, size 1; head is `some false`, unlike empty `none` | `{0}`, size 1 |
| Move right; move left; halt, empty input | 0, 1, 0, 0 | `{0,1}`, size 2 after the first move and thereafter | same |
| Write `some true`; write `none`; halt, initially blank `Option Bool` tape | 0, 0, 0, 0 | `{0}`, size 1; final tape is blank again | same |
| Move left twice, initial input `[some false, some true]` | 0, −1, −2 | `{−2,−1,0}`, size 3 | `{−2,−1,0,1}`, size 4 |
| Right/left case with supplied origin 7 | 7, 8, 7, 7 | `{7,8}`, size 2 | same for empty input |

The two-left input case attains the conservative input-inclusive bound
`max inputLength 1 + primitiveSteps = 2 + 2 = 4`. Its unvisited input cell at
coordinate 1 is included only in the explicitly named input-inclusive measure.
The right/left case ends with its original completely blank tape but has visited
two cells. Final nonblank support therefore cannot stand in for visited space.

## Connected actual empty-peek simulator case

Use one Unit-indexed Boolean stack, Unit source labels, Boolean registers, and
the actual source body `peek (fun _ observed => observed.isNone); halt`.
The actual native TM0 initial state comes from `TM1to0.tr (TM2to1.tr program)`
on `TM2to1.trInit () []`, with source register false. This is a genuine-init
case, unlike the earlier local go-fragment observations.

| Primitive prefix | Actual operation just completed | Position | Register |
|---:|---|---:|---|
| 0 | native initialization | 0 | false |
| 1 | normal dispatch dummy write | 0 | false |
| 2 | peek move left | −1 | false |
| 3 | folded empty-symbol load, move right | 0 | true |
| 4 | goto ret dummy write | 0 | true |
| 5 | halt dummy write | 0 | true |
| 6 | outer-none observation | no new cell; last position 0 | no live configuration |

The visited set is `{0}` at prefixes 0 and 1, then `{−1,0}` at every prefix
from 2 onward. Its size is 2. The live halt at 5 retains the original marked
empty tape and the true register. All native TM1 label-boundary positions are
0, so sampling those boundaries would incorrectly miss coordinate −1.
The extra outer-none observation at 6 does not increase visited space.

## Meaning of the proposed bound

For a supplied native starting configuration and supplied origin, the observer
must read the actual selected primitive command at every native prefix. It may
retain the last position after none only as an observation convention; it must
prove that this retention adds no physical visit. The exact visited set and a
conservative interval covering it must include all the positions above.

For native initialization on an input list of length N and an actual witness
of T primitive transitions, the target input-inclusive bound is
`max N 1 + T`, hence also `N + T + 1`. This is an upper bound, not an exact
space claim for all machines. It does not replace the tighter simulator-specific
height target or claim space for an unexecuted input converter.
