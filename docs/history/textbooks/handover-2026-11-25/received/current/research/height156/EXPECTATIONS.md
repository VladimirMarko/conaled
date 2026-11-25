# InternalHeight — fixed source-path expectations

**Status:** fixed before any new proof text or compiler feedback for this increment. This is uncompiled implementation preparation within the existing review loop. Root owns all compilers, integration, source/products, checkpoints, and review decisions. The six normal-dispatch research files remain frozen and are not dependencies of this source-only increment.

## Exact source basis

The requested candidate is C155 `a5a917db8717977371b8d76d93f166389c9eec9b`, tree `394733a450268e8943048ea146440dcb75c7ceea`. It was resolved in the local repository. The read working copies of AGENTS, task/formal guidance, `StackToTape.lean`, and `Examples/TuringSimulation.lean` were compared byte-for-byte with their C155 Git blobs and matched. The checkout HEAD is a different base; this record does not substitute HEAD's tree for the candidate or claim a whole-working-tree comparison.

The current native `TM2.stepAux`, `stRun`, `stVar`, `stWrite`, and `stmtStRec` definitions were read. Existing `actionBound`, `actionBound_run`, `stWrite_length_le`, and the reserve induction in `tailSteps_le_reserved` were read in the actual owner. Current retained examples supply all concrete data below. The earlier complete guidance readings were checked against current bytes and match.

## Definition contract, before implementation

`InternalHeight q v S H` is a Prop about one actual finite native TM2 statement body, with natural bound H. It follows exactly these source updates:

| Constructor | Required local guards | Continuation data |
|---|---|---|
| `push k f q` | Old selected length and `f v :: S k` length are at most H | Same v; replace stack k by `f v :: S k` |
| `peek k f q` | Old and new selected lengths are at most H; these lengths coincide | Register `f v (S k).head?`; unchanged stack family |
| `pop k f q` | Old selected length and `(S k).tail` length are at most H | Register `f v (S k).head?`; replace stack k by its tail |
| `load f q` | No new selected-stack guard | Continue with `f v` and S |
| `branch p qtrue qfalse` | No additional guard or maximum of branches | Follow only the actual Boolean `p v`, retaining that current v and S |
| `goto f` | True | End this statement-body inspection; do not follow the label into another body |
| `halt` | True | End this statement-body inspection |

The grouped stack-action equation must expose old length, new `stWrite` length, and recursion at the actual `stVar` register and `Function.update` stack family. Peek's unchanged family agrees with the grouped update by `Function.update_eq_self`.

H only bounds selected stack heights on this executed statement path. It does not constrain every initial stack, unused branches, or an arbitrary final stack family. It does not mention TM1/TM0 configurations, head positions, visited cells, `[-1,H]`, or `H+2`. No desired primitive-space conclusion may be built into its definition.

The predicate needs the stack-index `DecidableEq` used by the native functional updates. It must not introduce a finite-index hypothesis, default register/main values, or decidable alphabet/control equality.

## Generic claims to expose

1. The grouped `stRun` equation described above.
2. Monotonicity in H for the same actual q, v, and S.
3. The sufficient whole-family reserve implication:

   ```lean
   (∀ j, (S j).length + actionBound q ≤ H) → InternalHeight q v S H
   ```

   Its action case must derive the updated-family reserve using the existing `stWrite_length_le`, not assume the needed recursive height property.
4. A uniform starting-bound corollary: if every starting stack length is at most B and `actionBound q ≤ A`, then `InternalHeight q v S (B + A)`. Supplying a program-wide A remains the caller's obligation; this theorem must not assert that an input-dependent choice is already a uniform program bound.

## Independently calculated connected cases

| Retained source data and actual path | Selected height sequence | Fixed expected result |
|---|---|---|
| `Cases.emptyPeek`, followed by halt, register false, `Cases.emptySelectedStacks` | Empty selected false stack: 0 to 0; callback receives none and gives true | H=0 holds; the unrelated true stack still has length 4 |
| `Cases.emptyPop`, followed by halt, same initial register/family | Empty selected false stack: 0 to 0; callback receives none and gives true | H=0 holds; the unrelated true stack still has length 4 |
| `StatementCases.pushPopBody`, Unit register, `StatementCases.emptyFamily` | 0 to 1 to 0 | H=1 holds and H=0 fails, although the existing actual source step has empty initial and final families |
| `StatementCases.branchBody`, supplied register false, `Cases.sourceStacks` | Load changes false to true; choose push; selected false stack grows 2 to 3 | H=3 holds and H=2 fails; the unrelated true stack has length 4 |
| The same branch body and family, supplied register true | Load changes true to false; choose halt; no stack action occurs | H=0 holds despite initial stack lengths 2 and 4 |

The true-register branch case is a supplied source configuration, not a changed initial default. It must follow the branch after the load, rather than branch on the old register.

The source-only cases should consume the public predicate and grouped equation, retain both positive and negative literal outcomes, and reuse the existing `pushPop_source_step` for the endpoint contrast. The exact case expectations must not change in response to a failed elaboration.

For a connected use of the generic sufficient bound, the empty Unit family has uniform B=0 and pushPopBody has action bound A=2. Therefore the uniform corollary yields H=2. This is deliberately coarser than the actual minimal H=1. Monotonicity must also widen the independently established H=1 result to any H at least 1.

The empty-peek H=0 case must separately exhibit failure of the whole-family reserve at zero. Taking the unrelated true index gives `4 + 1 ≤ 0`, which is false. Thus reserve is sufficient, not the definition and not a necessary condition. The same unrelated length-four observation prevents interpreting H=0 as a bound on the whole family's occupied support.

## Boundaries retained

No primitive head interval, visited span, occupied-support theorem, source-to-target space bridge, clock adjustment, new native initialization, conventional-machine result, NP claim, textbook qualification, or acceptance decision follows from this increment. The existing actual simulator and all clocks remain unchanged. Later geometry must still prove every primitive movement bound using this predicate as a source-side hypothesis.
