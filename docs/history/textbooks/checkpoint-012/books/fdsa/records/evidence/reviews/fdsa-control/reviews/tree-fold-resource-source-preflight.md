# XT03 bounded source assessments

These are independent bounded source readings, not final Standards/Spec review,
elaboration evidence, a build, an audit, or acceptance. The original frozen
requirements and initial base remain unchanged. Source identities at the reading
phase are retained in `tree-fold-source-preflight-snapshot.json`. Root owns all
implementation and did not edit each assigned file while its reading was active.
The old Chapter 1 gate continued unchanged; no second compiler/checker/project
hash helper was run.

## Core operation and natural-cost laws — book_inventory

**No concrete finding against XT03-01–03 in the inspected source.** No
`XT03-SP` issue IDs are needed for this pass.

The reader read the full frozen requirements and
`Applications/Resources/TreeFold.lean`, then checked the exact reused
`Trees.fold_map`, `Trees.fold_fusion`, `Measured.bind`, `reweight_bind` and
`CallCount.tick` definitions. This assessment concerns the source read during
that pass; the reader checked no digest or elaborated types. Root's separately
retained source identities are not represented as reviewer-checked digests.

### XT03-01 — Raw construction and grouping

`run` is one specialization of the existing ordinary fold at `Measured β C`.
The payload, summary and observation types have independent universes. Its only
observation requirement is `[Add C]`; it does not introduce zero, associativity,
commutativity, ordering or payload instances.

The node equation preserves the frozen grouping exactly:

```text
(L.observation + (R.observation + F.observation)) + entry
```

The actual implementation binds the left result, right result and callback
before posting the entry observation. Nil returns `(empty, entry)`.
`run_node_tick` connects Nat entry one to the existing post-body tick operation.
`run_map` retains the explicit limitation that it compares runs on given tree
values and does not charge a separately computed map.

### XT03-02 — Value and observation transport

`run_value` uses ordinary fold fusion with `Prod.fst` and needs no algebraic
observation laws beyond the operation's `Add` requirement.

`run_value_entry` changes only the entry observation while retaining the same
callback and empty value. It therefore supports the required comparison of
reached callback arguments, without claiming anything about separately changed
callback closures.

`run_value_of` correctly presents its global callback-value law as sufficient,
rather than necessary.

`reweight_run` has the required additive-hom statement. Its proof transports the
nested binds and final entry addition through fold fusion. The additional
`AddMonoid` assumptions remain local to this theorem; no commutativity is
assumed or used.

### XT03-03 — Natural costs and callback domains

`run_cost_entry` compares the actual entry-`e` run with an actual zero-entry run
of the same operation. Its proof uses `run_value_entry` on both children before
collecting the natural costs, so the callback terms are compared at equal
returned summaries. The implementation itself still performs one fold; the
second run appears only in the comparison theorem.

The constant and upper-bound premises have the intended domain:

- The fixed entry, empty value and callback determine the runs.
- Child inputs range over arbitrary finite trees, with an arbitrary node label.
- The callback is inspected at those runs' returned summaries.
- The premise is neither a law on all possible `β` values nor a claim restricted
  to one supplied tree's subtrees.

The resulting formulas retain one fixed `k` or `K` for the family. Nil, zero
entry and zero callback work have the intended boundaries. `structural_le_cost`
gives only the natural nonnegative structural lower bound; no positive callback
lower bound is inferred from an upper bound. Collected-entry arithmetic remains
confined to Nat.

### Assessment limits

The source proof decompositions match the intended mathematics. The reader did
not check elaboration, tactic success, compilation, audits, clients under
XT03-04–06, documentation or integration. This is not final Standards/Spec
approval or acceptance. No file edits, compiler/checker/hash-helper runs,
Git/ref/cache/gate operations, remote actions or child delegation occurred.

## Ordered/product/reachable-summary clients — architecture

**No concrete mathematical, scope, or API mismatch was found in this bounded
source reading.** No `XT03-OP` defect ID was assigned merely for an untested
elaboration possibility. The observation client covers XT03-06 through the
actual core operation, including the distinctions that matter.

### Product execution and projections

`splitRun` uses `run (1, 0)` and lifts each actual callback result with
`AddMonoidHom.inr Nat Nat`. It introduces no independent tally.

The three measured equalities are correctly stated and preserve values:

- `split_first_run` retains `(combineRun l a r).1` while replacing its
  observation by zero.
- `split_second_run` recovers the same callback at entry zero.
- `split_total_run` recovers the same callback at entry one.

The first two proofs' final `rfl` is plausible against the inspected definitions:
projections of `inr c = (0, c)` reduce directly, with product eta for the second.
The total proof correctly handles the one nondefinitional arithmetic step,
`0 + callbackCost = callbackCost`, using `Nat.zero_add`. Its callback equality
preserves the returned summary as well as the observation.

`split_structural` consumes `run_cost_const` on the projected callback;
`split_work` and `split_total` extract the corresponding measured equalities
with `congrArg Prod.snd`. Thus the structural component is connected to the
same run and its actual summary flow.

Both sample proofs use the appropriate existing execution contracts:

- `append_sample_pair` combines `split_total` with
  `TreeFoldExamples.single_sample`, then cancels the structural nine.
- `cache_sample_pair` combines the actual `TreeCache.nodeRun` callback with
  `TreeFoldCacheExamples.size_sample`, again cancelling the structural nine.

The resulting `(9, 6)` and `(9, 12)` pairs and totals 15 and 21 match the frozen
cases. Neither proof transfers costs from value equality.

### Ordered trace and noncommuting boundary

`trace_node` preserves exactly the core grouping:

```text
(leftWord ++ (rightWord ++ [label])) ++ entryWord
```

This agrees with the core's `(left + (right + callback)) + entry` observation.
It does not commute or regroup observations to manufacture the desired order.

`trace_value` consumes `run_value_of` and `Trees.fold_numNodes`; `trace_sample`
therefore connects both size four and the callback word `[0, 2, 3, 1]` to the
actual measured fold.

The singleton counterexample is also correctly connected:

- Actual entry-token execution decodes to `[0, 0, 1, 0]`.
- The actual zero-entry execution followed by `3 • entryToken` decodes to
  `[1, 0, 0, 0]`.
- `trace_not_collected` transports an assumed equality through `words` and
  contradicts those concrete lists.

This establishes the intended failure of collecting entries at the end for
noncommuting observations. The root-level names `toMul_add`, `toMul_zero`,
`toMul_ofMul`, and `toMul_nsmul` match the pinned APIs. The proofs do not invoke
commutativity.

### Reached-summary boundary

`resetStep` has the required consequential behavior: it always returns zero,
costs zero at the reached summary pair `(0, 0)`, and costs seven at `(1, 0)`.

`reset_value` is valid by constructor reduction: both the nil result and every
node callback return zero. `reset_reached_cost` then rewrites the actual child
values, rather than assuming a global callback law.

`reset_cost` uses the public upper-bound theorem with reached bound zero and
combines it with `structural_le_cost`. Both child observations remain in the
core recurrence despite their summary values being discarded.

`reset_unreachable` and `reset_not_global` explicitly refute the stronger global
zero-cost assertion. Their payload argument `a : α` does not impose a global
`Inhabited α` instance.

### Assumptions and remaining elaboration uncertainty

The generic product examples retain independent payload and summary universes.
The core retains independent observation universes, requires only `Add` for
execution and unconditional value erasure, and introduces additive-monoid
assumptions only for homomorphism transport. No payload equality, order, or
default inhabitant leaks into these contracts. Fixing the trace example to Nat
is appropriate for its concrete labels and word tokens.

The remaining compilation checks are local proof elaboration, chiefly:

1. Simplification of concrete FreeMonoid words with the supplied `simp only` lists.
2. Definitional unfolding of `annotateRun` when
   `congrArg Prod.snd TreeFoldCacheExamples.size_sample` closes the raw-run cost equality.
3. Definitional reduction of coerced projection and sum homomorphisms.

The reader inspected the relevant definitions and found no specific reason these
expressions should fail; they remain uncompiled. No source, tracker, Git, cache,
compiler, checker, or gate action was performed, and this assessment is not a
final-review result.

## Primitive, append and annotation clients — tail_examples_preflight

**One concrete proof-expression concern: XT03-CP01. No mathematical or
frozen-scope discrepancy was found in the two client files.**

### XT03-CP01 — Raw run versus annotateRun during rewriting

In `Examples/TreeFoldCache.lean`, the original `list_node_cost` proof first
changed the left side to a raw `run` expression. After `run_node_cost` and
`append_node_cost`, its child-read expression therefore contained:

```lean
Trees.Cached.read []
  (run entry .nil (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) l).1
```

The next rewrite, `list_read`, was stated using the ordinary `def annotateRun`.
Matching required unfolding that semireducible wrapper. Pinned rewrite guidance
in `Mathlib/Tactic/ErwQuestion.lean` distinguishes `rw`'s reducible matching from
`erw`'s default transparency. The reader classified this as an expected
elaboration blocker, not a mathematical problem or an observed compiler result.
The remaining raw-run versus wrapped cost expressions could likewise prevent
the rewrite tactic's cheap reflexivity step from closing the goal.

The bounded proposed repair exposed a typed raw child-read equality, took
`run_node_cost` as a hypothesis, rewrote that hypothesis, and explicitly
unfolded `annotateRun` in the final `simpa only` comparison. The sketch was
uncompiled.

### Mathematical and connection checks

- Actual append sequencing: the right-associated callback executes singleton
  append first and then appends the actual suffix to `l`; the left-associated
  callback feeds its actual first result into the second append. The values
  agree by the existing append contract and list associativity.
- Callback costs: the expressions are respectively `length(l)+1`,
  `length(l)+3`, and `2*length(l)+3`. The fold recurrences replace actual
  returned-list lengths through the public value bridge and
  `Trees.inorder_length`.
- Finite cases: nil costs one; singletons cost 4, 6, 6; the saved sample returns
  `[0,1,2,3]` with costs 15, 23, 25. The proofs use the client recurrences.
- Actual annotation: `annotateRun` uses the existing measured `nodeRun`.
  `annotate_value` supplies its sufficient callback-value equation; validity
  and erasure reuse existing annotation laws; `annotate_read` explicitly
  consumes recursive validity and erasure of the returned tree.
- Size/height annotation: the constant-three premise applies the existing
  node-cost theorem to the actual child results. The whole-pass formula and
  sample cost 21 follow correctly, and returned values connect to the saved
  size/height samples.
- List annotation: the intended recurrence uses `left.numNodes+4`, already
  including the three smart-constructor charges. This yields singleton work 7,
  right-subtree work 14 and sample work 27, with the correct root read.
  XT03-CP01 concerns expressing that argument to the rewriter.
- Empty and payload boundaries: arbitrary payloads and `BinaryTree Empty` are
  retained without an inhabitance assumption. No uniform linear cost claim is
  made for arbitrary list combines.

The reader read the full two stopped client files and only the core interfaces
and imports needed to assess their uses. No edits or compilation occurred;
this is not final-review approval or acceptance.

### CP01 implementation and same-reader bounded recheck

Root independently read the pinned transparency guidance and retained the
original `Examples/TreeFoldCache.lean` bytes in
`tree-fold-preflight-snapshots/Examples-TreeFoldCache-before-CP01.lean`, SHA-256
`99d976310dc90a251e10f8ba0c931b141c808bf8bcf7cfc4cdfe482f9b686200`.
Only the proof of `list_node_cost` was changed:

```lean
have hread : Trees.Cached.read []
    (run entry .nil (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) l).1 =
      Trees.inorder l := list_read entry l
have h := run_node_cost entry .nil
  (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) a l r
rw [TreeCacheExamples.append_node_cost, hread, Trees.inorder_length] at h
simpa only [annotateRun] using h
```

The same reader compared only this theorem/proof with the preserved snapshot
and returned: **XT03-CP01 is addressed at the source level.** The explicitly
typed raw `hread` removes the need for `rw` to unfold the wrapper, and the final
explicit unfolding reconciles raw and wrapped costs. The theorem statement,
its `left.numNodes+4` charge and parentheses are unchanged.

Finding state: **implemented and source-rechecked; compiler confirmation and
final-review confirmation remain pending**. No files were edited by the reader,
and no compiler, checker or hash helper was run.

## Source/scope documentation — book_inventory

Found **one documentation scope clarification, XT03-DOC01**. No other concrete
source or tariff mismatch appeared in this bounded pass.

### XT03-DOC01 — Qualify the remaining-work list

The original final scope paragraph in `docs/research/fdsa-tree-fold-resource.md`
stated that the entire exclusion list remained mandatory. That list mixed
original book obligations with possible implementation mechanisms, including a
general translator, arbitrary history machinery and a particular left-mass
proof representation. Frozen requirements preserve the original source
obligations; they do not mandate every excluded mechanism as a future framework
or deliverable.

The proposed clarification was to state that those capabilities are outside
XT03 while original book obligations remain required in their owning chapters
or separately frozen shared work. A mechanism or proof representation is not
required merely by appearing in the exclusion list. This changes wording,
not the mathematics or frozen scope.

### Exact documentation assessment coverage

The reader read the entire new reconstruction note and only the appended
"Shared measured whole-tree folds (FDSA-XT03)" subsection of
`fdsa-reconstruction-map.md`, comparing them with frozen requirements and the
retained source preflight. These points matched the evidence:

- Literal right association is attributed to printed page 5, without a
  generated `T_inorder` or compiler-normalization claim.
- The three append executions, callback costs and sample totals 15/23/25 are
  distinguished correctly.
- Callback work survives nonrecursive-helper inlining.
- XT01's positive local-access tariff remains separate from the leftist
  source's zero-helper tariff.
- Arithmetic annotation costs 21 on the sample; list annotation costs 27,
  with callback and structural components explained correctly.
- Reached-cost premises quantify over arbitrary finite child trees under fixed
  parameters, not all summary values or just one input's subtrees.
- Function construction is separated from later invocation; fold/map value
  equality does not pay for an extra mapping pass.
- Nat-specific entry collection, noncommutative counterexamples and the product
  observation explanation retain their distinct assumptions.
- Both documents describe an unaccepted draft, preserve prerequisite acceptance
  and leave chapter obligations open.

This document pass did not independently verify the client code, import closure,
elaboration or compiler behavior. No edits, compiler/checker/hash-helper runs
or final-review claims were made.

### DOC01 implementation

The pre-correction note and map are retained in `tree-fold-preflight-snapshots`,
with exact identities in `DOC01-identities.json`. Original note SHA-256:
`51830ed0b59ecdd291d0a62fd7a604356729441532beb7d73d0af00a546491b9`.
Original map SHA-256:
`cb2910f2a343b1d30512183876408b3fd3acd8162993419410dbf9191bc9d8eb`.

Root changed the note to describe items outside XT03, retained all original
book obligations, and explicitly avoided imposing a particular auxiliary
statistic or a new general translator/history framework beyond source scope.
The appended map closing paragraph now makes the same scope distinction.
Frozen requirements were not edited. Same-reader bounded recheck requested;
final-review confirmation remains pending.

### DOC01 same-reader bounded recheck

The same reader inspected the corrected scope paragraph in the reconstruction
note and corrected closing paragraph of the appended XT03 map section.
**XT03-DOC01 is resolved at the source-text level.** Both now distinguish
excluded capabilities from original book obligations that remain mandatory;
the explicit wording removes the unintended framework/statistic requirement.
Construction-versus-invocation and extra-pass qualifications remain intact,
as does the absence of any build/audit/final-review acceptance credit.
No additional finding arose. Disposition: **implemented and source-rechecked;
final confirmation pending**. No edits, compilation, checking, hashing or
final review was performed by the reader.

## Retained finding summary

| ID | Nature | Current disposition |
| --- | --- | --- |
| XT03-CP01 | Expected rewrite transparency blocker in the list-annotation recurrence proof; no observed compiler failure | Implemented, same-reader source rechecked; compiler and final-review confirmation pending |
| XT03-DOC01 | Exclusion list accidentally promoted optional mechanisms to mandatory future scope | Implemented, same-reader source rechecked; final-review confirmation pending |

Original source bytes and full relevant identities remain recoverable. No
finding was dropped or counted as final approval. All other bounded readers'
no-finding outcomes remain limited to their stated source coverage. The
public import closure, elaborated statements, focused builds, complete
candidate gate/audit, both final axes and immediate candidate verification
remain outstanding.
