# Preface/Perm review continuation under the supplied native kit

Recorded: 2026-11-03T23:31:28.189417+00:00

This is coordination of the existing review loop in `1002-Perm.md`, not a new
implementation loop or a third review axis. The historical review record remains
unchanged. No chapter is accepted by this preparation.

## Immutable scope

- Fixed base and verified merge-base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Candidate and clean isolated checkout HEAD: `c988f183887896c00b09aaff9077a6ea7fb8d68f`.
- Full scope: 25 changed files, 496 insertions and 17 deletions; no exclusions.
- Comparison: `git diff 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd...c988f183887896c00b09aaff9077a6ea7fb8d68f`.
- Candidate commits, oldest first: `142adf2`, `cba657b`, `777bab9`, `bed44c1`,
  `de575a8`, `39c3e2f`, `1da24c7`, `3279bac`, `c988f18`.
- Previous independently source-reviewed candidate:
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.

The sole source delta since that candidate replaces the first-line `import Lean`
with `import Init` in `Squares.lean` and `Dependent.lean`. The rest of both files
and the previous 23 task files are byte-identical. Each axis must assess the full
candidate using the retained rounds 1–8 analysis, focusing new source examination
on this delta and its affected consumers. Prior source analysis is reusable;
prior incomplete full validation is not success evidence for this candidate.

## Requirement snapshot

| Work-state path | SHA-256 at briefing |
| --- | --- |
| `REQUIREMENTS.md` | `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84` |
| `AMENDMENTS.md` | `969feb05f90df6009e7d7920a9334f0e4c0a65f9380a8aa1b5ecc6a4360c1640` |
| `specs/1002-Perm.md` | `db34fbdab1881cdedbd3d7ae48ce8e2d0439c9cc7cebb8f1c00c449c60c0fef9` |
| `specs/1002-full-requirements.md` | `43dbf2c1104ec2503a0dc89206001fd541daaf7f677ad7e89c7fcbda61f5939a` |
| `specs/1034-import-footprint.md` | `f67b6a1c4deb8df3a4eb0d4db98affbbce21d6753a0a1fe685590623a6966e42` |

Read the requirements together. Historical requirements mention Nix/direnv;
#1031 permits separately acquired exact pinned tools, and the current user
selected the supplied unified native kit. Chapter order, full mathematics,
independent axes, local tracking and no GitHub writes remain unchanged.
The old #1002 spec's round-1 candidate and seven-file count are historical;
the immutable current scope above and #1034 supplement define this round.

The reference source is now at
`/workspace/scratch/60f07f0e98c8/reference/vfa/Perm.v`; the old specification's
relative reference path belongs to its original workspace. The current official
archive and all 17 chapter hashes were verified against the retained inventory
in `validation/1036-source-recovery.json`.

## Standards and review instructions

Use candidate `AGENTS.md` and its pointers, README development/build/audit,
`.agents/skills/code-review/SKILL.md`, its heuristics, the shared review procedure,
architectural quality, applicable ADRs, and statement-review guidance in
example-driven development. The existing record retains the intended
mathematics, connected cases, source coverage, and each prior source correction.
Root owns all compiler, process and cache actions; reviewers read immutable
sources and supplied evidence only. Do not infer process ownership from old
numeric PIDs or treat a captured running record as a successful gate.

## Evidence already available

- `validation/1034-integration.json`: exact two-line source delta and full scope.
- `validation/1034-foundation-completion.json` and its retained attempt: six
  original foundations checked against exact captured source with isolated
  outputs. This is focused evidence, not the full integrated audit.
- `validation/1036-unified-setup/`: actual native setup, cache, valid/invalid
  proof, Lake-child, native executable and Mathlib smoke evidence.
- `validation/1036-doctor.json`: successful post-relocation official input and
  real dedicated dependency-store verification.
- `validation/1036-isolation.json`: source candidate and nine exact package
  links into the dedicated real `vfa-validation/.lake/packages` store.
- `tooling/UNIFIED-NATIVE.md`: current invocation and sole-writer discipline.

The new full fresh attempt is
`validation/1002-candidate-c988f18-unified-fresh1`, started
2026-11-03T23:29:01.187276+00:00. At briefing it is incomplete, with no passed
candidate record. Its kit uses `LEAN_NUM_THREADS=1`, fresh `--jobs 1`, and no
explicit Lean CLI `-j1`; do not identify it with the previously reviewed
native-j1 runtime or transfer historical performance observations to it.

## Findings and remaining sequence

| Item | Retained disposition |
| --- | --- |
| ST-001 | Fixed by the earlier independently reviewed composition relocation |
| ST-002 | Open, medium; historical four-family output mismatch requires the incident assessment/recovery evidence |
| SP-VAL-001 | Open; completed exact-candidate validation evidence is missing |
| Standards | Blocked pending independent current assessment and required evidence |
| Spec | Blocked pending independent current assessment and required evidence |

After actual fresh completion, preserve its matching native verification record
and terminal/log provenance. Establish stable idle inputs, run the unchanged
`1034-pre-guard-assess.py` against the new candidate and the exact dedicated
store, classify the diagnostics, and preserve any material suspects before
repair. Historical original mismatched bytes are unavailable; current copies
cannot reconstruct them or prove their cause.

Then retain a separate successful guarded candidate build, post-build integrity
check and exhaustive audit record. Complete the managed no-cache/rehashed
`+ProofAudit` prerequisite and all four audit regressions. Investigate unexpected
prerequisite rebuilds and re-establish affected guard evidence. Both independent
axes must assess the exact candidate and complete evidence. Root finally runs
`./check.sh --verify-candidate HEAD` immediately before acceptance.

The separate protocol clarification in
`reviews/1002-fresh2-record-protocol-clarification.md` remains authoritative for
attributing native success records if a parent wait status becomes unavailable;
it never permits inventing an observed zero exit. Fresh success alone does not
close the incremental incident or substitute for the remaining sequence.
