# #316 implementation handoff

## Integrated candidate

Status: ready for independent Standards/Spec review; approval remains pending.

- Candidate: `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`
- Incorporated integration tip and review base: `f0773fee8fa40214c67606c46ba8c41eed8e674b`
- Tree: `a3baf0c1f6213e135371f9f1ee428fc144c6162c`
- Worktree: `/tmp/conaled-314-320/316`, branch `research/dependent-higher-316`

The merge commit is `chore(dependent): incorporate reviewed integration baseline (#316)`.
Its first parent is the validated candidate
`ca54f31646bd60e1866efc39f257db5b27dc17fc`; its second parent is the review base.
The merge completed without conflicts or manual source edits. All 13 authored
#316 files retain exactly the same Git blobs and SHA-256 hashes. The complete
diff against the new review base is the same 13-file task change. The statement
review, outcome, and limitations below therefore remain applicable.

Artifact validation passed on this exact new candidate using:

```sh
direnv exec . python3 /tmp/conaled-314-320/reviews/316-integrated-validate.py
```

The commit-specific, read-only result is
[316-validation-d7d2beeea699bccc2f7eb0fee7f8fa52e6718186.json](316-validation-d7d2beeea699bccc2f7eb0fee7f8fa52e6718186.json).
The script and record reside outside the source diff. Checks confirmed:

- All Agda sources, the manifest and reproduction script match the successful
  receipt; log, dependency graph, and receipt also match the retained fresh run.
- All 235 closure source hashes match the retained source and compiler-data
  trees. The checkpoint archive, compiler archive, and compiler binary match
  their receipt pins; the six omitted builtin sources match setup pins.
- Archived repository inputs, the frozen #292 memo, and development/toolchain
  configuration are unchanged from the successful candidate.
- All 10 local Markdown link targets exist. Python compilation and `--help`
  execution pass, as does `git diff <review-base>...HEAD --check`.
- The checkout is clean at the candidate above.

These input identities support reuse of the fresh 235-module Agda check
completed at `2026-11-04T23:37:08Z`. No Agda rerun was needed. Relative to the
new review base, #316 adds no Lean sources or shared build-tool changes, so no
integrated Lean build/audit was run or claimed. No Lean cache was provisioned.
No tracker, master, integration-branch, or remote changes were made during
this preparation. Independent review must use the new base and candidate.

## Pre-integration candidate and validation provenance

Status: candidate ready for independent Standards/Spec review. No review approval claimed.

- Worktree: `/tmp/conaled-314-320/316`
- Branch: `research/dependent-higher-316`
- Incorporated integration/review base: `9b0a0fe143c6f97f399632d4bb34a179db012181`
- Candidate: `ca54f31646bd60e1866efc39f257db5b27dc17fc`
- Requirements: `../specs/orchestration.md`, `../specs/316.json`, coordination `../specs/321.json`, and root-approved successor #322. Source archives and frozen #292 memo remain unchanged.
- Existing uncommitted report and Agda sources were preserved and completed. No unrelated working-tree/index edits existed. Candidate is clean.

## Outcome and remaining construction

The permitted precise-prerequisite outcome is used. The report compares direct strict omega-groupoid, Kan/local-universe, chosen simplicial universe and cubical routes against the actual fragment. It distinguishes mathematical existence, mechanized inhabitants, cardinal assumptions and host implementation obligations. The direct strict two-groupoid family/Grothendieck/open-identity/arbitrary-motive contextual-J theorem remains unconstructed. Its concrete B²Z path-family test and failed strict-natural-contraction shortcut identify the missing higher data, beyond a generic coherence warning. Root-created #322 owns that direct construction under #289. #321 retains cubical calculus/model/source-compatibility scope.

The new positive evidence is actual safe Cubical Agda source checking: generic inductive-identity derivation, two substitutions with the dependent pair and transported apd source, a K(Z,2) second-identity witness connected to the generic proof, explicit endpoint comparison, integer detection and higher-erasure refutation, plus circle-cover nonconstant transport. This is not a Lean higher model, source interpretation theorem, verified importer or higher adoption-gate pass. #320 must retain that boundary. #107 remains paused; #108's gate and theorem are untouched.

## Statement review and cases

`FrozenMemo` quantifies A and B at arbitrary levels, retains every dependent context component, and proves composition against an independently written direct assignment. Its J-beta quantifies an arbitrary motive, not only the transport motive. `conjugation` has both endpoint comparisons in the required order. These are source-theory derivations, not a constructed Lean model of every Agda rule.

`HigherWitness` uses the pinned library's two pointed K_n-to-loop equivalences, then PathIsoEq at each layer. The pointed path supplies encode(refl)=0. It constructs h=decode(1), proves encode(h)=1 and h≠refl without postulating a model/witness law, instantiates w-twice/apd-twice at that h, and proves the observed conjugate has detector1 and cannot be reflexivity. The observer targets the memo's conjugation, not apd-η itself.

`Monodromy` retains the generic dependent pair and witness at the circle-cover instance. Its named single-loop computation and generic η composition give3 with first loop and2 with that loop erased. Both full repeated-substitution laws use FrozenMemo's public proofs.

Large proof/loop expansions were interrupted by their owner and replaced by abstract proof boundaries without changing the mathematical observations. `attempts.json` preserves the distinction between these interrupted runs and successful checks.

## Validation

No Lean sources, Lake configuration, proof-audit exemptions, host axioms or shared project tooling changed. Per README's isolated-experiment boundary, validation uses Agda plus artifact checks; no integrated Lean build/audit result is claimed and no Lean cache was copied.

Successful fresh final reproduction:

```sh
direnv exec . python3 experiments/dependent-higher-identity/check.py \
  --work-dir /tmp/conaled-314-320/316-agda/final-316 \
  --compiler-archive /tmp/conaled-314-320/316-agda/state/Agda-v2.8.0.2-linux.tar.xz
```

This extracted the preserved archive into a new private tree, verified the kit, performed fresh offline compiler setup with its positive/negative smoke checks, then checked Everything with `--ignore-interfaces`, `--safe`, no unsolved metas/incomplete matches and an explicit library registry. It completed at2026-11-04T23:37:08Z, equivalent to2026-11-05 00:37:08 Europe/Zurich; the checker invocation took60.26s. The dependency graph has235 modules:4 local,209 Cubical,22 compiler-owned.229 are reported in fresh Checking lines;6 previously installed compiler-owned imports are separately hashed against kit pins. The tracked validation.json, check.log and imports.dot retain the evidence.

Post-commit validation on exact candidate ca54f31646bd60e1866efc39f257db5b27dc17fc passed:

- clean git status;
- every Agda source, manifest and reproduction-script blob hash matches the successful receipt;
- committed log and graph match receipt hashes;
- all235 closure source hashes match the retained exact source tree and compiler data;
- local Markdown link targets exist;
- `git diff <base>...HEAD --check` passes;
- Python script compiled and executed successfully.

The report and README state the external compiler/primitive trust boundary, dependency-scoped flags, experimental indexed-inductive transport, and difference between a whole-module import closure and minimal logical proof dependencies. The Agda check is not Lean's exhaustive axiom audit. No active checker or memory-heavy process remains; other ticket acceptance builds are free to proceed.

## Review routing

Root owns independent review coordination and tracker/shared-doc integration. No push or tracker mutation was performed by this implementer. Please review the full candidate against the saved #316 specification, including its permitted exact-prerequisite outcome, and the preserved source distinctions. Implementer remains available for corrections within this existing loop.
