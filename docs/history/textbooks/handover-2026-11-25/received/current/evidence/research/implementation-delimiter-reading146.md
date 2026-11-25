# Implementation reading: successful delimiter probe 146

## Outcome and role

The exact combined delimiter probe **passed**: actual exit 0, 40.35822616799851
seconds, with 321 before/after input descriptors identical. I read the entire
successful 1,082-line log, all 198 readable types, its one expanded type, and all
eight selected axiom roots. No error, warning, or `sorryAx` appears. Each printed
root lists exactly `propext`, `Classical.choice`, and `Quot.sound`.

This is implementation proof/output reading by `/root/certificate_size`, which
helped write the earlier drafts. It is **not an independent reviewer axis**,
ordinary-source acceptance, an integration approval, or a conventional NP result.
No compiler, source/install/cache/process action, public-M content read, or
reviewer action was performed for this record. Only this Markdown file and its
paired JSON reading record are written.

## Exact successful evidence

- Combined source: `work/delimiter-research/query-repair3/DelimiterGeneral146b.lean`,
  153,582 bytes, SHA-256
  `626a70835cd01b2435c64c9b5726552a55b4d5b5bf63afe8923d2751973518ed`.
- Entire actual log: `work/continuation/delimiter-general146-attempt2.log`,
  82,702 bytes, 1,082 lines, SHA-256
  `c774ac143d3fb74750e056bd7ed2f2cf6b6b4089038e44dd18b7a6f11f38e83b`.
- Final result: `work/continuation/delimiter-general146-attempt2.result.json`,
  SHA-256 `2886c5949ceef50d97dc5a050409cbef74336c32b3202f059c13ab8ab8d403fa`.
- Child exit: `work/continuation/delimiter-general146-attempt2.child-exit.json`,
  SHA-256 `f888dfce50d65728427fd98e5890ff101274366daf565eb3d843317c17d13a30`.

The child receipt establishes the actual child exit; its
`post_run_hashing_completed` field is false. The later final result separately
supplies the complete before/after binding maps. Both maps have 321 non-null
entries and are equal; the actual input list has the same 321 unique keys. The
316 preparation-closure descriptors all match actual bytes, hashes and normalized
permission modes. The five additional bindings are the native runner, recorded
runner, attempt preparation, query INPUTS file, and query SNAPSHOT file. I parsed
and compared every descriptor; I did not reopen every bound dependency or compiled
artifact. No public-M source was accessed through the binding list.

The command in the receipt is the existing native-profile route through the
`work/acceptance139` Lake environment with `lean -EhasSorry` on the exact combined
source. It contains no added resource/time setting. This focused result does not
resolve whole139 or establish the current installed library's whole acceptance.

## Final source identity and repair

All five final source files were freshly read in full. Their complete namespace
bodies match the successful assembly byte-for-byte at the recorded source-map
ranges. The final files are:

| File in `general-repair3` | Lines read | SHA-256 |
|---|---:|---|
| `DelimiterPrelude144b.lean` | 634 | `4f986f887f30cfe4ab90eec8894fe2c3b78d3d37cf516fcd4331a89aafe67408` |
| `DelimiterPreludeExamples144c.lean` | 267 | `30e5cb81d457bc8d4c4fe889cfb7b00df600ea1691e8dcfe38a65a939accc208` |
| `Protocol144b.lean` | 267 | `44e41e29237af04093bef4896b4568601252d4e2480b576e0b72e3fee46379da` |
| `NativeLoops144b.lean` | 417 | `ece5e04f35bb69e71f9308ea62c30e0fdaecd634b737f6c48cf49b9cd8a32fd5` |
| `PrefixComposition144b.lean` | 354 | `15dcaffb7fd2f57f76d13d8fce4beb94387ec9daff3b6354f035eff3863459ce` |

The complete 11-line `CHANGES.diff` was read. It changes exactly one proof lambda
in `pair_split_append` from `(input.map some ++ [none]) ++ rest` to
`input.map some ++ ([none] ++ rest)`. This aligns the congruence function with the
right-associated target already produced by simplification. It changes no
statement, input, clock, state, premise, machine action, or expected value. Four
files are byte-identical to repair2; NativeLoops differs by exactly that one
replacement. The 44,086-byte compiler/controller prefix and every other combined
byte, including all queries, are unchanged from query-repair2.

The preceding repair2 attempt remains a failure: exit 1, 305 unchanged bindings,
45.72596734599938 seconds. Its sole diagnostic, read in full at lines 1–8, is the
reported append-association mismatch. I have not treated its recovered axiom
output as evidence of success.

The frozen file comments still describe their preparation-time uncompiled
status. The successful receipt now covers their exact namespace bodies in this
combined probe. Their separate research imports were not independently built or
installed by this reading task.

## Native initializer, malformed inputs, and cleanup

The source machine's actual main is the caller prefix phase, and its actual input
index is the caller input store over `Option Bool`. The raw input is literally
`input.map some ++ [none] ++ cert.map some`. Input `none` is a present delimiter:
its observed pop is `some none`; empty input gives outer `none`. The separate
prefix-delimiter and prefix-empty transition lemmas preserve that distinction.
There is no whole-word framing operation in a machine statement or initializer.

`machine_initList_eq` gives the full new initializer. It starts the actual five
phase program with the literal raw input, empty work/framed stores, and the exact
initial register state. `prelude_handoff` reaches the **full** old initializer,
not merely a projected framed word. `oldMachine_initList_eq` identifies the old
main, `initialRegisters (none, initial)`, exact framedRaw contents, all fifteen
other existing stores empty, and both caller input/work stores empty. The actual
handoff statement loads `reset` before jumping. The base user value is preserved;
scratch and all old temporary registers are reset. Local branch proofs use full
configuration extensionality over every store index.

The machine and old machine retain the same full program, initial registers and
fuel output index. `total_iterate` composes the real prelude run with the existing
controller `init_iterate` on the exact handoff word. The endpoint is literal
`Turing.haltList (machine initial) [verifyDelimited raw]`; the read definition of
`haltList` fixes label none, initial registers, the singleton fuel output, and all
other stores empty. Thus full caller cleanup is preserved through final output.

`protocol_cases` is exhaustive. A word either contains no delimiter, is exactly
one literal pair, or has a second delimiter followed by an arbitrary tail. The
pure success/failure equivalences and actual missing/repeated loop runs are both
present. Repeated input drains the entire arbitrary tail, including any further
delimiters, and then drains work. Missing input drains its accumulated work.
Both malformed forms hand off the empty framed word, and `malformed_output`
reaches the full singleton-false halt. Its malformed predicate is the intended
language condition; no execution, cleanup, time, or space assumption has been
added to the final run or bound theorems.

## Exact clocks and actual total-source bound

Let I and C be the input/certificate bit lengths, N the complete literal raw
length, and r the length after a second delimiter. The checked formulas and
constructed actual runs preserve:

| Raw form | Prelude count |
|---|---:|
| Valid literal pair, N=I+C+1 | 3I+2C+4 |
| Missing delimiter, N=I | 3N+2 |
| Repeated delimiter, N=I+C+r+2 | 3I+2C+r+5 |

The uniform prelude bound is 3N+2. The source count is exactly
`preludeSteps raw + FrontEndStreamMachine.runSteps (handoffWord raw)`. Its checked
upper bound is 4N²+23N+38: the produced framed word has length at most 2N, the old
controller bound is H²+10H+36, and the paid prelude contributes at most 3N+2.
`outputsInTime` stores this actual count and its complete literal-halt execution.
These are native TM2 statement counts. They are not newly claimed primitive TM0
transition counts. The additional transition to outer none is separately proved
at `totalSourceSteps raw + 1`.

All seventeen exact fixture statements match the original repair1 declarations
under whitespace normalization, and all their successful printed types were
read. The frozen clocks are:

| Fixture | Prelude steps |
|---|---:|
| `empty_missing_handoff` | 2 |
| `delimiter_only_handoff` | 4 |
| `prefix_false_handoff` | 7 |
| `prefix_true_handoff` | 7 |
| `certificate_false_handoff` | 6 |
| `certificate_true_handoff` | 6 |
| `two_certificate_bits_handoff` | 8 |
| `mixed_valid_handoff` | 14 |
| `missing_false_handoff` | 5 |
| `missing_true_handoff` | 5 |
| `missing_mixed_handoff` | 8 |
| `repeated_empty_handoff` | 5 |
| `repeated_tail_handoff` | 6 |
| `repeated_mixed_handoff` | 11 |
| `repeated_tail_has_delimiter_handoff` | 9 |
| `mixed_valid_initial_true_handoff` | 14 |
| `repeated_mixed_initial_true_handoff` | 11 |

No exact small-case peak claim has been retargeted. This source set proves the
universal occupancy bounds below; separate sharp per-fixture peak theorems remain
outside this result.

## Every native prefix and physical stores

`prelude_boundary` constructs an actual execution witness for every
n≤preludeSteps, including the final handoff. It uses the real partial-loop runs
and a complete configuration invariant. `prefix_obligation` then combines this
execution with the occupancy calculation. `prelude_prefix_cells` transfers the
bound to any actual reached configuration by deterministic equality.

The read `stackCells` definition sums lengths over every actual stack index.
The sixteen existing stores plus caller input/work are all included. The proved
`state_stackCells` is raw.length+work.length+framed.length because the complete
state fixes every other stack to empty. The invariant calculation gives at most
2N for every inclusive prelude boundary. The old controller's actual `init_peak`
is applied after the complete old-initializer handoff; its bound max(H,1) is at
most max(2N,1). Prefix composition therefore gives **max(2N,1) for every inclusive
native source boundary through the literal live halt**. N=0 is covered by the
max-with-one term. This is actual total stack occupancy, not a count of a chosen
store or a projected logical payload.

The theorem is about native source-step boundaries. Primitive simulation
microsteps, visited tape extent, and ordinary input/output overhead require their
separate compiler/adapter consumers. This reading does not promote the native
bound into those results.

## Expanded binder and axiom reading

The ordinary `state_stackCells` output is at log 956–962; its explicit-argument
readable type is at 1057–1063 and expanded type at 1064–1079. All three lack a
`Fintype R` binder. The expanded application supplies only the fixed
`instFintypeCallerStore` to the store sum. The deliberate local omission removes
an unused section assumption; package theorems still retain their intended
`[Fintype R]` assumption.

The eight selected roots are `prelude_handoff`, `prefix_obligation`,
`total_iterate`, `total_prefix_cells`, `outputsInTime`, `literal_pair_output`,
`malformed_output`, and `state_stackCells`. Their complete reports occur at
1036–1056 and 1080–1082 and contain exactly the three standard axioms listed
above. The 199 printed type targets match the submitted 199 query targets with
multiplicity; the eight root targets also match in order. The expanded display
uses a command-local `pp.all true`; no compiler resource or linter setting is
changed by that display query.

## Actual reading limits

The paired JSON records each source/log range and its hash, every printed output
block's range/hash, full descriptor-comparison results, and the exact fixture
statement comparison. Successful-log reading was contiguous in six chunks:
1–200, 201–400, 401–600, 601–800, 801–1000, and 1001–1082. All five source files
were read from first to final line. The child receipt, source maps, preparation
manifest and snapshot were read in full. The complete result, actual input list,
and preparation binding map were parsed and all descriptor entries compared;
individual dependency contents were not reread through those maps.

Additional source reading covered FrontEndStreamMachine 42–90 and 1935–1979
(local stores, complete configurations and physical-cell sum), and the pinned
Mathlib Computable file 100–140 (native init/halt and output-time definitions).
Earlier reading of the controller execution/peak contracts is retained in the
prior research records. The unchanged 44,086-byte compiler/controller assembly
prefix was identity-checked, not freshly audited line by line. No public-M tree
was read. No full-library, ordinary-owner integration, independent-review,
qualification-count, or conventional complexity-class conclusion follows from
this implementation reading alone.
