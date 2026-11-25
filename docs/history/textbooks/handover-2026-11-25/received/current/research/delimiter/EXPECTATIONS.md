# Frozen delimiter-prelude expectations144 — before compiler feedback

This is prospective implementation assistance under `work/delimiter-research`.
It does not extend installed source, establish independent review, change a
qualification count, or claim conventional NP. No compiler has been run for this
design. Freeze these expectations before checking a copied Lean draft. Preserve
this file if a later implementation revision needs a new expectation version.

## Fixed machine choices

- Caller stores: `input` has alphabet `Option Bool`; `work` has alphabet `Bool`.
  Both are actual external stores of the unchanged FrontEndStreamMachine program.
- Caller labels: `prefix`, `certificate`, `reverse`, `drainInput`, `drainWork`.
- User registers: `Option (Option Bool) × R`, where the first field records a pop
  result and the second preserves the supplied initial `R`. The scratch states
  distinguish an empty pop, a popped delimiter, false, and true.
- New package input is the caller input store; new main is caller `prefix`.
  Output remains the old fuel store. Its initial registers are exactly
  `FrontEndStreamMachine.initialRegisters (none, initial)`.
- The complete program is `FrontEndStreamMachine.program caller`, unchanged in
  every old owned label. The old comparison package has that same caller/program,
  initial registers and fuel output, but framedRaw input and the old framer main.
- Literal input is `input.map some ++ [none] ++ cert.map some`. It is loaded
  literally into the designated input store. No frame encoding occurs at init.

Each item below is one actual TM2 label activation, with its finite statement
body evaluated using Mathlib's `TM2.stepAux`:

| Phase and pop | Statement actions and next label |
| --- | --- |
| prefix: bit b | Pop input; push false then b onto work; go to prefix |
| prefix: delimiter | Pop input; push true onto work; go to certificate |
| prefix: empty | Empty input pop; go to drainWork |
| certificate: bit b | Pop input; push b onto work; go to certificate |
| certificate: delimiter | Pop input; go to drainInput |
| certificate: empty | Empty input pop; go to reverse |
| reverse: bit b | Pop work; push b onto framedRaw; go to reverse |
| reverse: empty | Empty work pop; reset all temporaries/scratch, retain initial R; go to old main |
| drainInput: any letter | Pop input; go to drainInput |
| drainInput: empty | Empty input pop; go to drainWork |
| drainWork: bit b | Pop work; go to drainWork |
| drainWork: empty | Empty work pop; reset all temporaries/scratch, retain initial R; go to old main |

The prefix pushes have this exact order: push false first, then b. Consequently
work contains the reverse of the desired frame. Successive reverse-phase pops
and framedRaw pushes restore the desired frame order. The maximum number of
stack actions in any caller body is3. Source label counts are not primitive
tape counts; the existing generic compiler must pay for every stack action.

## Counts derived from these phase actions

Let `N` be literal raw length. A valid pair has prefix length `I`, certificate
length `C`, `N = I+C+1`, and frame length `F = 2I+C+1`.

| Protocol case | Phase activation counts | Exact prelude count |
| --- | --- | --- |
| Valid pair | prefix I+1; certificate C+1; reverse F+1 | 3I+2C+4 = N+F+2 |
| Missing delimiter, N bits | prefix N+1; drainWork 2N+1 | 3N+2 |
| First delimiter after I bits; second after C more bits; arbitrary tail length r | prefix I+1; certificate C+1; drainInput r+1; drainWork (2I+C+1)+1 | 3I+2C+r+5 = N+(2I+C+1)+2 |

In the repeated-delimiter row `N=I+C+r+2`; the arbitrary tail can itself contain
delimiters. No early failure bypasses draining that tail or the work store.
All cases satisfy `preludeSteps ≤ 3N+2`.

## Complete boundary-state convention

Each recorded boundary includes the actual label, complete registers, input
store, work store, framedRaw, and an assertion that the other fifteen old
physical stores are empty. There are no other caller stores. Before handoff
all old temporaries remain zero. Scratch equals the actual previous pop result;
work pops are injected as `some <$> head?`. The base `R` remains the supplied
initial value at every boundary. Handoff resets scratch to none and gives the
old package's exact complete initializer.

Successful handoff has empty caller input/work and framedRaw equal to the exact
existing `BitPairFraming.frame input cert`. Failure handoff has empty caller
input/work and framedRaw=[]; it is the old package's initializer on [], not a
claim that the old controller will clear arbitrary caller context.

## Independently fixed small table

Notation: `0` is `some false`, `1` is `some true`, `#` is literal `none`.
Frame strings contain only ordinary Boolean bits. All entries use initial
R=false unless their identifier explicitly says true. Counts end at the live
old initializer, before its first activation.

| Identifier | Literal raw input | Handoff framedRaw | Prelude steps | Exact prelude peak cells |
| --- | --- | --- | ---: | ---: |
| empty_missing | empty | empty | 2 | 0 |
| delimiter_only | # | 1 | 4 | 1 |
| prefix_false | 0# | 001 | 7 | 3 |
| prefix_true | 1# | 011 | 7 | 3 |
| certificate_false | #0 | 10 | 6 | 2 |
| certificate_true | #1 | 11 | 6 | 2 |
| two_certificate_bits | #01 | 101 | 8 | 3 |
| mixed_valid | 10#01 | 0100101 | 14 | 7 |
| missing_false | 0 | empty | 5 | 2 |
| missing_true | 1 | empty | 5 | 2 |
| missing_mixed | 10 | empty | 8 | 4 |
| repeated_empty | ## | empty | 5 | 2 |
| repeated_tail | ##0 | empty | 6 | 3 |
| repeated_mixed | 1#0#1 | empty | 11 | 6 |
| repeated_tail_has_delimiter | #1##0 | empty | 9 | 5 |
| mixed_valid_initial_true | 10#01 | 0100101 | 14 | 7 |
| repeated_mixed_initial_true | 1#0#1 | empty | 11 | 6 |

The two true-initial cases must retain true and restore the exact scratch-none
initial state at handoff. The `empty_missing` and `delimiter_only` cases must
stay distinct, as must false input bits and absence of a letter. The delimiter
is a genuine nonblank input letter under the eventual ordinary tape injection.

## Space and composed source bounds

For a valid pair, prefix-boundary occupancy after j bits is N+j; after the
delimiter and during certificate scanning it is F. Reversal transfers cells
without increasing the total. Thus the exact prelude peak is F.

For a missing delimiter the exact prelude peak is2N. For repeated delimiters
the exact peak is N+I, attained before/at the first delimiter. Input draining
and work draining decrease occupancy. Every prelude prefix therefore has total
occupancy at most2N, including all caller and old stores.

The handoff word has length at most2N. Existing genuine-init controller bounds
then yield total source time at most

`(3N+2) + ((2N)^2 + 10(2N) + 36) = 4N^2+23N+38`

and full-run prefix occupancy at most `max (2N) 1 ≤ 2N+1`. The old controller's
exact suffix is `runSteps handoffWord`. On malformed inputs this is specifically
`runSteps []`; consume the existing unchanged F01 witness before replacing it
numerically by20. Its old fixed source clock is20, not19.

For a fixed full-program action bound A, the generic native route should give

`3 * (4N^2+23N+38) * (1 + A * (2 * (2N+1+A) + 2))`

primitive steps from encoded native init to the related live literal halt.
This formula is a prospective consequence of real source run/prefix proofs,
not an assumed time premise. Ordinary input reflection/output emission and the
separate print-and-move adapter keep their own real cost obligations.

## Language boundary

On a valid literal pair, the eventual answer must equal `verifyBitsRun input cert`
through exact frame handoff and `verifyFramed_frame`. Malformed delimiter words
must answer false after actual cleanup. Existing `BinaryYes`, original little
endian threshold bits, both distance directions and witness bound C≤I² remain
unchanged. For a short witness the literal pair has length `I+C+1≤I²+I+1`; the
internal frame still has its existing exact length `2I+C+1`. No result here
substitutes a free whole-word encoder or closes the remaining NP/model tasks.
