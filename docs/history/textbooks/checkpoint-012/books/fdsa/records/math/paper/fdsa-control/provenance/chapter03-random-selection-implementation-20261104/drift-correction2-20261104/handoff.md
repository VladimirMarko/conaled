# Drift elaboration correction 2

Candidate `cd20a36f52b4ddd95be3cb9d85c0b95368ef1248`, tree `702b4b3eaabb318828de9e0b56fa7cb27d1ecf63`, parent `f535b1ef557795c4e09c97ce0daf599961c9b268`.
Branch `work/fdsa-ch03-random-selection`, clean worktree.
Commit `fix(selection): normalize duplicate rank example indices (#174)`.
Finding **C03-RANDOM-DRIFT-ELAB-002** remains proposed/pending the root's actual
successor validation. All eight sources and own provenance writes are now held.

## Actual evidence and exact correction

Actual attempt3 closed with exit1: owned12511, terminal `7747b5`, root closure
`2dccc3`. The complete log/closure/terminal were read in `f1097f`. Core
`Applications.Resources.RandomSelectionDrift` built in8.9s; the sole remaining
error was the free variable hidden in `Fin [x,x].length` during kernel decide
for `stable_duplicate_positions`. Outer11,916 bytes SHA-256
`92bc4a7db977e676e224446ea6aa5ece534de2055e1c8e89cf0e9e9c81f1647a`;
native11,632 bytes SHA-256
`5bb1bee4abffe521d449a3a023f1a550e4d0994d71984f1d4de0ded6f465cd73`.
Attempt2's separate reconciliation and saved partial records were read fully in
`ad8904`: an actual start exists but no session receipt or terminal. No success,
failure, exit or live session is inferred from those historical files.

Only one proof argument in `Examples/RandomSelectionDrift.lean` changes:

```lean
  occurrenceRank_tie [x, x] 0 1 (by
    change (0 : Fin 2) < 1
    decide) (by rfl)
```

The explicit closed finite type is definitionally equal to the dependent list
length. The proof continues consuming the public stable occurrence-rank theorem;
arbitrary payload/order and equal-value proof remain unchanged. There is no
changed mathematical claim or expected result. The full changed example file
was read in `cf9e91`. Diff: three insertions, one deletion.

All139 public and15 private declaration headers and contexts are unchanged from
f535. All seven other files are byte-identical, including the newly built drift
core and all six prior passing files. Executable definitions, sampler, selected
child, costs, constants, imports/options and all cases remain intact. The prior
private helper's local omitted-order disclosure remains in the record; this
correction makes no further implicit-context change. All120 earlier author
records, current14 closed-run records, eight interrupted-attempt snapshots and
14 earlier drift-failure records retain their hashes.

## Root-only check and complete input

```text
lake build Applications.Resources.RandomSelectionDrift Examples.RandomSelectionDrift
```

`Statements139-correction2.lean` contains the entire unchanged full explicit-@
input, bound to this candidate and all eight source blobs. It has7,759 bytes and
SHA-256 `11642119a2fafb69c23bc1e16d41fe82a34cc8d0319d7256eb6717bcaba35084`.
It has not been run by the author. There is no successor actual type output.
The fixed full-task review base remains
`2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Starting state preceded edits (`d3f12a`). Exact proof replacement, complete
header/inventory preservation, evidence hashes, input binding and whitespace
check exited0 in `735f36`. Staged diff matched the saved diff byte-for-byte;
local commit exited0 in `daec39`. These are source integrity checks, not Lean
validation. No author compiler/runtime/cache/profile/dependency action occurred.
No full-pair pass, full candidate audit, independent Standards/Spec outcome,
immediate verification, finding closure or chapter acceptance is claimed.
Tail/worst-case continuation awaits the actual drift pair pass and root release.
