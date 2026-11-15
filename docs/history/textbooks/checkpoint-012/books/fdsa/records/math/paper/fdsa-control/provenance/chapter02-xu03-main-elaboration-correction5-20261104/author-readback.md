# XU03 main-example correction5 — author readback

Recorded: 2026-11-04T09:46:38.941159+00:00. Author: `/root/shared_acceptance_sequence`.

**Source-only proof repair; uncompiled.** The root released the checkpoint 0096
capture hold for exactly six proof-body corrections in the idle isolated Tail
worktree. No compiler, Lake, dependency hydration, cache, candidate check,
axiom audit, immediate verification or process polling was performed. Existing
review/control records and the central/foundation trees were not changed.

## Exact scope and evidence

The parent source is `070e3608c439aec23404d23e90de47c6cf835216`, branch
`work/fdsa-permutation-tail-validation`, initially clean. Its complete main
example is byte-identical to the file in the actual failed central candidate
`0a7ef0784e1b140b356b4ce7b79ba65a79edf3c3`. The before source is 8,786 bytes,
197 lines, SHA-256
`30e07aaede25b10d2484c2a4674bffa66d77094a545fd49f72bc000bd132ddb7`.
The repaired source is 9,826 bytes, 222 lines, SHA-256
`bc6753118198b91de684e50bd6196b4b68035b92461a34c0528dbd7f7742099e`.

The complete original 197 lines, complete repaired 222 lines and full diff were
read. The source inventory confirms all 18 theorem headers and all 7 definitions
are byte-identical. Exactly six existing theorem proof blocks differ. Both
local instances, all 4 imports, both options, namespace/open commands, every
comment and every other declaration block remain exact. The private
`mass_of_law` statement and proof are unchanged. No theorem or helper definition
is added or removed.

The frozen XU03 requirements were read completely and retain SHA-256
`80323e579fe63419a10d7b26eb55f7ac540fea98a8a7c9c4efe36dce5f088b9c`.
The original six-path unit scope and its predecessor-acceptance sequence remain;
this correction does not narrow the independent review scope or close a gate.
The Nix waiver does not change exact Lean/Lake/dependency pins or proof/audit
requirements. The authorized handoff contains no compiler execution.

The completed focused 9 result has exit 1 at clean unchanged central X. Its full
17,133-byte log matches SHA-256
`8da63603aa28b114dc5f183bdc4a1be9abe470ebfef1c5bf3353628be979fd0f`.
Its relevant actual lines show Boundary Built in 128s, Main failed in 82s and
Uniform Ran. A boundary target success and a Ran label do not establish a
main, uniform, whole-unit or aggregate pass. All six complete main diagnostics
are copied in `actual-diagnostics.txt`; `diagnostic-mapping.json` relates each
to its specific source correction. The existing result/logs remain untouched.

## Statement and connection review

The experiment still uses the original Fin4 positions `[0,1,2,3]`, selected
set `{0,2,3}`, one global key-to-label permutation and its inverse-order
observation. The remaining set is still selected.erase 0 = `{2,3}`. The changed
proofs retain the independently specified values and existing generic-law
connections:

| Existing theorem | Preserved expectation and actual connection | Proof-only correction |
| --- | --- | --- |
| `tail_23_mass` | Actual tail `[2,3]` has conditional mass 1/2 through `cond_tail_eq`. | Establish the identical positive support premise through the exact permutation-finset equality, then ordinary `decide`. |
| `tail_32_mass` | Distinct tail `[3,2]` also has mass 1/2 through `mass_of_law tail_hasLaw`. | Establish the same `orders positions remaining` support premise by that equality and reduction. |
| `repeated_tail_mass_zero` | `[2,2]` remains unsupported and has mass 0 through `cond_tail_eq`'s off-support branch. | Establish the identical nonmembership premise; no premise or output value changes. |
| `filtered_tail_mass` | The actual tail filtered to `{3}` has sole output `[3]` of mass 1 through `mass_of_law filtered_tail_hasLaw`. | Establish membership in the same singleton-subset order support. The generic filtered-law and on-event projection bridge are untouched. |
| `environment_changed` | `afterFirst ≠ law`, because the same event for first key 0 has mass 1 under afterFirst and 1/3 under law. | Apply inverse to the derived equality and use its involution to obtain the impossible numeral equality 1 = 3. |
| `last_tail_mass` | After revealing the next head 2, the actual nested conditional measure gives sole last tail `[3]` mass 1 through `mass_of_law last_tail_hasLaw`. | Establish membership in the unchanged support `orders positions (remaining.erase 2)`. |

All quantifiers, types, hypotheses, conclusions, original complete positions,
measurable structures and actual sample/measure arguments remain unchanged.
The new reductions establish only concrete support premises. Their probability
conclusions continue to use the same public source-fiber/HasLaw statements.
No independent sampled tail, branch-independence premise, arbitrary history
claim or changed expected result is introduced. The proof of changed full
environment remains essential to the two-step case and is preserved.

## Exact API reasoning

The existing support definition is
`orders positions S := (positions.filter (fun a => decide (a ∈ S))).permutations.toFinset`.
The five actual failures all stop during reduction of this `.permutations`
expression. Pinned Mathlib proves
`List.permutations_perm_permutations' (xs : List α) : xs.permutations ~ xs.permutations'`.
Its existing `List.toFinset_eq_of_perm` converts that list-permutation witness
into equality of the two finite supports. Each repaired proof applies this
identity to exactly its own original filtered positions, then uses ordinary
kernel-checked `decide` on the alternate finite enumeration. It changes neither
the support nor its list values. This is the same theorem-backed enumeration
change used by the now-successful boundary target.

The environment argument keeps `hmass` derived by evaluating the assumed
measure equality on `firstEvent observedOrder 0`. After the existing rewrites,
`hmass` states `(1 : ENNReal) = 1/3`. `congrArg (fun x : ENNReal => x⁻¹)`
preserves equality. `one_div`, `inv_one` and `inv_inv` reduce its two sides to 1
and 3. The last `norm_num` proves the contradiction on these finite numerals.
Pinned ENNReal supplies `DivInvOneMonoid` and `InvolutiveInv`; this argument
uses no field instance and remains valid with ENNReal's zero/infinity inversion
conventions. No extra hypothesis is added to the theorem.

`api-excerpts.txt` records exact declarations and source identities from
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, checked against the pinned
Git objects. Relevant APIs were read directly; no new elaborated-type output
is claimed. The complete source reading and preservation inventory check the
formal statements, while actual elaboration remains outstanding.

## Verification boundary and handoff

`git diff --check` passed. Only `Examples/PermutationTail.lean` differs in the
repository. Source marker inspection found no admission, new axiom,
unsafe/partial declaration, native-decide shortcut or listed bypass marker;
that inspection is not an axiom audit. No linter/option was suppressed.
Before the local commit, existing hook configuration was inspected without
changing it; no executable commit hooks were present.

The local Conventional Commit is
`02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9`,
`fix(fdsa): elaborate conditional-tail main examples (#174)`, with parent
`070e3608c439aec23404d23e90de47c6cf835216`. Its single changed path is
`Examples/PermutationTail.lean`; the final index/worktree is clean. The source
blob is `baa3e26a3c72a4589765562167d1d85edc011e67`, and its committed, working
and saved after-copy bytes are identical. The first commit attempt stopped
because the recovered host had no author identity; its failure log is retained.
The retry used the established ChatGPT identity from the preceding five Tail
commits through command-local options, without changing persistent configuration.
The root owns the next focused compiler run and both independent reviewers
remain separate. The complete candidate
build, source/coverage/integrity checks, exhaustive audit, full original-scope
Standards and Spec outcomes, immediate candidate verification and predecessor
acceptances remain mandatory. Nothing in this handoff accepts the unit or
relabels unchanged historical evidence as validation of this successor.

**Completed and HOLD:** committed source-only successor, explicitly uncompiled.
