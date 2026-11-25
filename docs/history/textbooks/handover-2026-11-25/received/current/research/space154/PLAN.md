# Height-specific primitive space: reconstructed proof plan

**Status:** reconstructed from conversation on 2026-11-25 after the fresh environment was confirmed wiped at 04:46 UTC. This is an **unproved optional development plan**, not an acceptance decision or an independent review.

The original attempted write to `work/space154/PLAN.md` returned only “Script running with cell ID g7:12”; the environment then became unavailable. Its original completion is unknown, and root reports the old file absent after the wipe. This document reconstructs the complete useful plan from the implementer's last final message. Its new hash identifies this reconstruction, not an original saved artifact.

The source-specific analysis below was performed before the wipe against C153b `0959a1c9d59660eec33ca4c9d971d74a8bc54378`, tree `655ddb1ee2a730d73a7b0fb5eda5a3e3c40eb669`, and pinned Mathlib. Those source identities were supplied by root; the relevant file contents were actually read then. This reconstruction does not claim a fresh source reading or a fresh compiler result.

Root reports restoration under `work/restored154` (root locator `P153-root`; packet name `conaled-textbooks-153-checkpoint-2026-11-25T000051Z`), with the project later under `work/conaled154`. The completed restore location has not been verified here. Resolve the source references below against root's actual restored current source before implementation. No compiler, project-source/product/settings mutation, external action, or new delegation accompanies this reconstruction.

The retained guidance selects no different mandatory mathematical increment. This height theorem remains optional research; current whole/audit/receiving obligations and quarantined UNKNOWN outcomes stay separate.

## 1. Target theorem and its scope

Write

```
P₁ := TM2to1.tr P
P₀ := TM1to0.tr P₁
```

Start from the **full existing relation** `TM2to1.TrCfg a d`, with actual primitive configuration `TM1to0.trCfg P₁ d` and global head origin zero. Retain the supplied source main/register defaults and the native marked-alphabet blank `(false, fun _ => none)`.

The theorem should construct an actual primitive `EvalsTo` witness, preserve the full related endpoint, and prove at every primitive prefix up to that witness's actual count:

```
-1 ≤ VisitedSpace.headPosition P₀ start 0 i
VisitedSpace.headPosition P₀ start 0 i ≤ (H : ℤ)
```

Then derive:

- `visitedCells ... i ⊆ Finset.Icc (-1) (H : ℤ)`;
- visited cardinality at most `H + 2`;
- the same bound for the visited hull, represented by `visitedInterval ... 0 0 i`;
- no extra visited cell when appending the separate outer-none observation after a proved stopped endpoint.

The existing `VisitedSpace.space_le_of_run` gives a **time-derived** bound: visits at most `B + 1`, input-inclusive interval at most `max N 1 + B`. Neither that result nor `primitiveBound_stack_tr ≤ 3` proves the height theorem.

**Selected-stack height does not bound every occupied cell.** The existing `peek_empty_other_four` selects an empty track while another track has four symbols. Its head can satisfy the proposed bound with `H = 0`, but its occupied support cannot have cardinality at most one. The separate occupied-region bound `max H 1` needs an initial bound on **all** tracks, propagated through updates. An input-inclusive interval also needs its declared input length justified.

## 2. Existing sources to reuse

The following current owners were inspected before the wipe. Paths are relative to the project source root.

| Owner | Relevant existing material |
|---|---|
| `Applications/Resources/TuringSimulation/StackToTape.lean` | outward_exact, return_exact, action_step, shuttle_witness, statement_tail_witness, normal_step_witness, actionBound, stWrite_length_le, reserve induction, actual-source-prefix composition |
| `Applications/Resources/TuringSimulation/TapeToPrimitive.lean` | primitiveSteps, statement_exact, statementEvalsTo, finite_run_bounded, halted_step, primitiveBound_stack_tr |
| `Applications/Resources/TuringSimulation/VisitedSpace.lean` | Actual cfgAt, commandAt, headPosition, exact visits, global-coordinate movement/write laws, terminal no-new-cells, preservation of never-visited cells |
| `Examples/TuringSimulation.lean` | Other-track case, primitive empty push/pop/peek cases, genuine-init empty-peek sequence |
| `Applications/Resources/RotationCertificate/FrontEndStreamTapeMachine.lean` | Actual controller source-prefix bound **max raw.length 1**, and fixed tapeActionBound caller |

Useful anchors in the inspected C153b source:

- StackToTape: outward_exact 43–68; return_exact 120–146; action_step 160–184; shuttle_witness 227–248; statement_tail_witness 317–373; normal_step_witness 378–399; actionBound/reserve arguments 403–481; actual-source-prefix composition 545–597.
- TapeToPrimitive: complete body was read.
- VisitedSpace: actual prefix/command/position definitions and visits 58–195; space_le_of_run 341–355; coordinate frame 371–406; terminal and unvisited-cell preservation 416–569.
- Examples/TuringSimulation: other-track case 96–132; primitive empty action cases 460–528; actual-init peek sequence 1061–1178.
- FrontEndStreamTapeMachine: controller prefix bound and fixed syntax constant 37–106.

Pinned Mathlib sources were inspected directly at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`:

- `Mathlib/Computability/TuringMachine/StackTuringMachine.lean`, complete TM2to1 slice 331–710: marked alphabet, addBottom, stVar, stWrite, trStAct, trNormal, tr_respects_aux₂, tr and TrCfg.
- `Mathlib/Computability/TuringMachine/PostTuringMachine.lean` 480–524: trAux folds actual loads/branches; move/write each emit one primitive command; goto/halt emit one stationary self-write; trCfg retains the full tape.

## 3. First reusable lemmas: concatenate actual coordinate traces

The pre-wipe bounded search found no existing head-position concatenation theorem. The small generic additions should express:

```lean
cfgAt M a n = some b →
  cfgAt M a (n + m) = cfgAt M b m

cfgAt M a n = some b →
  headPosition M a origin (n + m) =
    headPosition M b (headPosition M a origin n) m
```

Prove the first from literal optional iteration. Prove the second by induction on `m`, using the first and the definition of `commandAt`.

These lemmas let ordinary `EvalsTo` segments carry a conjunction of endpoint position and prefix bounds. No alternate transition system is necessary.

**Crucial restriction:** full tape or successor-configuration equality alone does not determine displacement. Moving on a uniform blank tape can leave its relative `Tape` value unchanged. Therefore the existing `iterate_some_eq_of_step_eq` cannot by itself transport coordinate information. For folded load/branch cases, establish equality of the actual selected `trAux` command, and hence of `commandOffset`, as well as the successor configuration.

A particularly small source-specific lemma is:

```lean
(TM1to0.trAux P₁ a (TM2to1.trNormal q) v).2 =
  TM0.Stmt.write a
```

Its proof follows the actual TM2 statement induction, including changed registers and selected branches. Combined with `primitiveBound_trNormal = 1`, positivity, and `statement_exact`, this gives the real stationary one-primitive dispatch/activation segment.

## 4. Local primitive cases provide the geometric argument

Define the abbreviation

```lean
base L := Tape.mk' ∅ (TM2to1.addBottom L)
```

and retain the whole-family encoding premise:

```lean
∀ j, L.map (Turing.proj j) =
  ListBlank.mk ((S j).map some).reverse
```

At a translated go/ret boundary, use tape `(Tape.move right)^[r] (base L)` and explicitly carry absolute coordinate `r`.

The following position lists are hand calculations from the inspected transition definitions. Each includes both starting and ending primitive prefixes; repeated coordinates are real writes.

| Boundary and condition | Actual primitive positions | Steps |
|---|---|---:|
| Normal dispatch, or ret over marker | [0,0] | 1 |
| Go at r<n, where n=length(S k) | [r,r+1,r+1] | 2 |
| Ret at r>0 | [r,r-1,r-1] | 2 |
| Push at n, new length n+1 | [n,n,n+1,n+1] | 3 |
| Peek at n | [n,n-1,n,n] | 3 |
| Pop at n>0, new length n-1 | [n,n-1,n-1,n-1] | 3 |
| Pop at n=0 | [0,0] | 1 |

The peek subtraction must be integer subtraction: at zero it reaches −1.

Branch justification comes from existing source-specific facts:

- `stk_nth_val` and `addBottom_nth_snd` identify the selected track as present before its length and absent at its length.
- `addBottom_head_fst` and `addBottom_nth_succ_fst` distinguish empty/nonempty pop and stop return scanning at zero.
- For empty peek, the left half of `base L` is blank, so the actual register callback receives `none`, even when another track is nonempty.

For each row, obtain the full endpoint from `statementEvalsTo` and the existing action/outward/return theorem. Prove its coordinate summary separately from the **actual emitted commands**.

Intermediate tape preservation also matters. Push/pop copy the marker component and update only track `k`. Use `Tape.write_nth`, `Function.update_self`, `Function.update_of_ne`, `addBottom_modifyNth`, and the global-coordinate movement law to retain the marker at global zero and every other track. Peek and scanning writes are self-writes. Reuse the existing whole-family action endpoint relation; do not weaken it to a single-track observation.

Old and new selected lengths bounded by `H` put every row inside `[-1,H]`. Empty peek is the sole negative excursion.

## 5. Use actual internal heights; keep the syntax reserve as a corollary

Introduce a proposition `InternalHeight q v S H` following the **actual source statement path**:

- For `stRun o q`, require old selected length ≤H, new selected length ≤H, and recurse on `q` with actual `stVar` and `Function.update` effects.
- For load, recurse at the actual updated register.
- For branch, recurse into the branch actually selected by the current register.
- For goto/halt, return `True`.

Define it structurally on the original push/peek/pop constructors; expose a grouped `stRun` equation for `stmtStRec`.

This hypothesis concerns source stack lengths, not the desired primitive positions. **It permits empty peek with H=0.** Using only `length + actionBound ≤ H` as the public premise would exclude that useful sharp case.

Prove the reserve lemma separately:

```lean
(∀ j, (S j).length + actionBound q ≤ H) →
  InternalHeight q v S H
```

Reuse the update/reserve argument already present in `tailSteps_le_reserved`, including `stWrite_length_le` and actual register/branch selection. Uniform source-boundary stack bound `B` and syntax bound `A` then give `H = B + A`.

Composition order:

1. Prove a primitive shuttle summary by joining outward segments, the action segment, and return segments. Its full endpoint is ret at global zero with updated register and all encoded tracks.
2. Follow `statement_tail_witness` using `stmtStRec`, retaining all primitive prefix bounds and final coordinate zero. Activate continuations through the stationary dispatch lemma.
3. Follow the existing actual-source-prefix induction. At each live source prefix before `T`, assume `InternalHeight` for its actual selected statement, register, and stacks.
4. Derive the visited/hull inclusion and cardinality using the existing visit membership theorem, min/max edges, and `Int.card_Icc`. Reuse `halted_run_adds_no_cells` for outer none.

Prefer a single constructed witness carrying timing and geometry together. **Do not assume two witnesses to equal endpoints have equal counts**; a nonterminal computation can revisit an endpoint after a cycle. Retaining a previously selected actual witness requires the appropriate deterministic prefix/count connection, not endpoint equality alone.

## 6. Existing cases and concrete consequence

First connect the genuine-init empty-peek fixture with `H = 0`, preserving:

- source main `Unit.unit`, register default `Bool.false`;
- the explicit native continuation-control default;
- marker true at zero and all stack tracks empty;
- **live halt 5 / outer none 6**;
- positions **[0,0,-1,0,0,0,0]**;
- exact visits **{-1,0}**.

The configured live2/none3 case remains separate. Reuse empty pop, empty push, the other-track case, and existing push/pop statement cases. Do not replace their expected clocks.

For the current complete controller, the existing source-prefix proof supplies total stack cells ≤ `max N 1`, and `A = tapeActionBound caller` is fixed before the input. The reserve route therefore proposes

```
H = max N 1 + A
marked primitive visited span ≤ max N 1 + A + 2
```

This would be a new linear-in-input height consequence for a fixed programme. It is not yet proved and is distinct from the existing time-derived bound.

Finite-control restriction needs an additional command-preservation bridge. The restricted transition must retain the identical native `Stmt`, yielding `commandOffset` equality at supported prefixes and then head-position/visited-set equality. Same tape, endpoints, and count alone do not state that geometric fact. Preserve the actual package main/register defaults.

Stop this increment at the marked simulator and its finite restriction. The ordinary reflected wrapper, delimiter prelude, emitter, and combined print/move adapter have different coordinates and transient movements; each requires its own paid coordinate analysis.

## 7. Smallest useful implementation increment

The first independently useful cut is:

1. actual coordinate-trace concatenation;
2. the `trNormal` stationary-command lemma;
3. the empty-peek local primitive segment;
4. connection to the existing genuine-init empty-peek fixture.

Then extend to the remaining local rows and one complete shuttle. The remaining obligations are the internal-height reserve lemma, whole-statement and source-run composition, interval cardinality, and finite-control command transport.

**All proposed lemmas remain unproved.** This plan supplies source-specific proof obligations and case analysis; it grants no acceptance or qualification credit. Root owns all compilation, restoration, source installation and checkpoint writes. Pause after saving and hashing this reconstruction until root assigns an increment and verifies the fresh native environment. Preserve this concise plan, not duplicate integrated source bodies or superseded operational histories.
