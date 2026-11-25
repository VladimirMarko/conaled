# Actual native trace concatenation — fixed expectations

Status: fixed on 2026-11-25 before writing the proof draft and before any compiler feedback for this increment. This is implementation assistance within the existing review loop. The draft is outside the project and is not accepted or integrated mathematics.

## Source and scope

The restored source is root-reported C153b `0959a1c9d59660eec33ca4c9d971d74a8bc54378`, tree `655ddb1ee2a730d73a7b0fb5eda5a3e3c40eb669`, under `work/conaled154`. The relevant current owners have been read: the complete `Applications/Resources/TuringSimulation/VisitedSpace.lean`, the actual initialized empty-peek fixture in `Examples/TuringSimulation.lean`, and the native `TM0.Machine`, `Cfg`, `step`, and `init` definitions in pinned Mathlib. This record fixes calculations and intended contracts; it is not a compiler result.

The bounded increment is three reusable concatenation lemmas and connected uses of one existing initialized fixture. It does not prove a height bound, change a clock, invent a new simulator, or modify any existing source. Root owns compilation, integration, proof audit, and the existing independent Standards and Spec review.

## Generic public contracts

For an arbitrary native machine `M`, supplied complete configurations `start` and `finish`, and natural `n`, the sole execution premise is the literal actual-prefix equality

```lean
cfgAt M start n = some finish
```

For every natural suffix length `k`, the intended conclusions are:

```lean
cfgAt M start (n + k) = cfgAt M finish k
commandAt M start (n + k) = commandAt M finish k
headPosition M start origin (n + k) =
  headPosition M finish (headPosition M start origin n) k
```

The command equality preserves the full `Option (Q × TM0.Stmt Γ)`: next control, move direction or written symbol, and absence of a command. The position proof must use the actual `commandOffset` in the recursive definition. Equal tapes or equal successor configurations alone cannot establish a movement coordinate, since moving an all-blank tape can leave that tape extensionally unchanged.

The generic statements retain the native supplied `Inhabited Γ` and `Inhabited Q` instances. They require no finiteness, decidable control equality, normalization, height bound, or support premise. `n = 0`, `k = 0`, and suffixes extending beyond outer none remain included. The split configuration itself is live; this does not assert a live suffix at every later time. Coordinates after outer none are the observer's retained bookkeeping coordinate, not newly visited cells.

## Existing genuine empty-peek fixture

Use exactly `Examples.TuringSimulation.VisitedSpace.peekSource`, `peekTapeProgram`, `peekMachine`, `peekInput`, `peekStart`, and its existing named intermediate configurations. Source main is `Unit.unit`; initial source register is `Bool.false`. The actual translated blank has marker `false` and its sole raw track `none`. The existing genuine initialized tape has the marker `true` at coordinate zero and raw track `none`; this is empty raw input, not present `false`.

The control default must remain `(some (peekTapeProgram (.normal ())), false)`, and the function-valued alphabet default must agree with the existing `Pi.instInhabited` selection. Reopening the example namespace does not inherit its old local instance commands, so any needed local instances must be restated explicitly with those exact values.

The independent primitive calculation, unchanged from the retained fixture, is:

| Prefix | Complete configuration | Coordinate from origin 0 | Next action |
|---:|---|---:|---|
| 0 | `peekStart` | 0 | Dummy write of the current marked symbol; select go |
| 1 | `peekGo` | 0 | Move left |
| 2 | `peekLeft` | -1 | Load the absent raw cell, set register true, move right |
| 3 | `peekBack` | 0 | Dummy write of the current marked symbol; select ret |
| 4 | `peekRet` | 0 | Dummy write of the current marked symbol; select live halt |
| 5 | `peekHalt` | 0 | No command |
| 6 | Outer `none` | 0 (bookkeeping) | No command |

Thus the full prefix-coordinate list remains `[0, 0, -1, 0, 0, 0, 0]`. The live endpoint is reached at five native steps; outer none is the separate sixth step. Full endpoint tape equals the initial tape, final register is true, and the transient left cell remains genuinely visited. These old expectations must not change to repair a proof.

## Connected obligations fixed before the proof draft

1. **Split at the transient left cell.** Use the actual existing equality `cfgAt peekMachine peekStart 2 = some peekLeft`. For every `k`, derive all three generic equalities above, with full-start indices `2 + k` and suffix coordinate origin `-1`. The local suffix positions for `k = 0, 1, 2, 3, 4` are `[-1, 0, 0, 0, 0]`.

2. **Preserve the full selected command.** At global prefix two, the full command is `some ((some peekGotoRet, true), TM0.Stmt.move Dir.right)`, and its actual `commandOffset` is the integer `1`. This must be connected through the new command concatenation result, not inferred from the restored endpoint tape.

3. **Compose the remaining actual run.** From `peekLeft`, one native step reaches `peekBack`, two reach `peekRet`, three reach `peekHalt`, and the fourth gives outer none. Use the new concatenation laws to obtain the full initialized run's live-five and outer-none-six endpoints and coordinates zero. The full live endpoint retains true register and exact initial tape. The command at outer none is absent. Establish the local suffix's configurations from the existing `peek_step2` through `peek_step5` equations rather than taking a desired composed endpoint as a premise.

4. **Check the carried coordinate frame.** With supplied origin seven, the same initialized machine has coordinate six at split prefix two. For every suffix `k`, the complete-start coordinate at `2 + k` equals the coordinate of the suffix started at six. In particular the first move of that suffix returns to seven. This detects an implementation accidentally hardcoded to origin zero. It does not change the machine, input, full tape, or clocks.

The existing literal position facts may discharge small local coordinate calculations. Their connection to concatenation must be explicit in the proofs. A standalone re-proof of the old clock or coordinate list would not exercise the new interface.

## Limits

No `InternalHeight`, interval `[-1, H]`, or `H + 2` span theorem is claimed here. The existing time-derived visited-space bounds remain distinct. The selected empty-peek case does not establish a bound on occupancy of arbitrary other tracks. This increment does not supply a conventional print/move or ordinary-wrapper coordinate transport, a new polynomial-time/NP claim, whole-project acceptance, or a textbook completion claim.
