# Independent combined-action adapter expectations

Frozen before writing any adapter implementation/proof source and before any
compiler feedback for this increment. These are hand traces of the exact route
in `work/review/conventional-action-route144.md`, using the native move/write
rules and the combined action `(T.write letter).move direction`.

The work alphabet, blank, supplied initial control, literal input list, and
complete native tape are unchanged by the adapter. Combined controls are a
normal copy, a return copy, accept, and reject. A native move is simulated by
one combined transition. A stationary native write is simulated by printing
and moving right, then preserving that right neighbour and moving left: exactly
two combined transitions. A stopped native Boolean answer costs a further
combined transition, printing the current letter and moving right into accept
or reject. Terminal controls have no successor; outer none is distinct.

For a native live-endpoint witness with T successful primitive transitions,
the exact simulated count is the sum of 1 per actual move and 2 per actual
write. It is at most 2*T. After a proved stopped Boolean answer, add exactly
one actual transition, obtaining a bound 2*T+1, including T=0. This is an upper
bound; a move need not be padded to two transitions.

## Fixed native cases

Use work alphabet `Option Bool`, blank `none`, false letter `some false`, true
letter `some true`, and retain a fully specified native starting tape in each
case. Initially the head coordinate is0.

| Native computation | Combined count to same complete normal-boundary cfg | Combined count including decision | Head positions including decision |
|---|---:|---:|---|
| Already stopped, false head; native witness T=0 | 0 | 1, reject | `[0,1]` |
| Already stopped, true head; native witness T=0 | 0 | 1, accept | `[0,1]` |
| One write of false, then native stop; empty input | 2 | 3, reject | `[0,1,0,1]` |
| One write of true, then native stop; empty input | 2 | 3, accept | `[0,1,0,1]` |
| One write of false, then native stop; present false input | 2 | 3, reject | `[0,1,0,1]` |
| One write of true, then native stop; present false input | 2 | 3, accept | `[0,1,0,1]` |
| Right then left, initially one false letter | 2 | 3, reject | `[0,1,0,1]` |
| Write true then erase to blank, initially empty | 4 | no Boolean-output claim | `[0,1,0,1,0]` through normal boundary |

For a stopped input tape T, the post-decision tape is exactly `T.move right`.
For one native write b, the normal-boundary tape is exactly `T.write b`, with
both tails preserved; the decision tape is `(T.write b).move right`. For the
right/left case the normal-boundary tape is exactly T. For write/erase it is
the original completely blank tape, despite the visited right neighbour.

The two distinct input lists [] and [some false] have native heads none and
some false, respectively. They remain distinct literal initialization inputs.
The adapter must not treat a blank halt as a proved Boolean-output case.

Use a separate actual supplied-start case with native control Bool, start=true,
and ambient Bool default=false. The false control is already stopped and the
true control writes its answer. The combined initialized control is normal
true, not normal false. Its literal initial tape is unchanged.

The final right movement is a real visit. The stationary-write return is a
real visit as well, even when the normal-boundary tape has become completely
blank. For all table cases that contain a movement, the exact visited set is
`{0,1}`; a zero-step normal-boundary witness alone has visited set `{0}`.

Outer none after a combined accept/reject state is a further transition of
the optional-step observer. In the one-write cases it occurs at4, after the
decision control was already reached at3. For the zero-native-step cases it
occurs at2, after decision at1. It adds no new live position.

Existing earlier native live2/none3 and empty-peek live5/none6 expectations are
not changed by these distinct combined-machine cases.
