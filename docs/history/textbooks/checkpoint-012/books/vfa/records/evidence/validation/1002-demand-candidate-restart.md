# Demand dependency correction and new exact candidate

2026-11-02. Previous candidate 777bab9 has a retained, concrete proof-elaboration
failure in FRP.Demand:139:16. The normal full gate exposed an implicit dependency
on natural-number successor-order simplification after the broad Mathlib import
was removed. Source statements and intended mathematics were not weakened.

The pinned `Mathlib.Order.SuccPred.Nat` supplies Nat.instSuccAddOrder and the
imported simp lemma Order.lt_add_one_iff. Adding precisely that direct import
passed the full staged Demand check once: exit 0, 129.985 seconds, no diagnostics.
`../staging/frp-demand-import/README.md` records exact settings, unchanged
non-import bytes, explicit artifact mappings, the two emitted direct imports,
all 15 unchanged protected input identities, and generated-output removal.
`1021-demand-correction.json` verifies that the committed source exactly matches
that checked source. No generated artifact was installed in a project cache.

New candidate: `bed44c16cee3e1eff6a4175bad9a7ed50651b927`.
Base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Full scope: ten files, 470 insertions, two deletions, no exclusions. Commit message:
`fix(frp): declare successor-order proof dependency (#1021)`.

Root verified the old candidate, clean checkout, exact recorded process group
and each member's workspace location, then sent SIGINT only to group 175155.
The external runner recorded return code -2; interactive session 30567 reported
wrapper exit 130. The old log ends with KeyboardInterrupt and retains the Demand
error. Every recorded process was confirmed stopped before checkout changed;
282 completed project .olean files were retained under normal guard rules.
`1002-777bab9-interruption.json` and `1002-candidate-777bab9.run.json` preserve
the exact outcome. That attempt did not reach an accepted audit or success record.

After switching the clean isolated worktree to bed44c1, the unchanged command
`LEAN_NUM_THREADS=1 nix develop --command ./check.sh --candidate HEAD` started.
Its complete command and durable subprocess outcome are recorded in
`1002-candidate-bed44c1.run.json`; its `.log` preserves all output. No tooling,
dependency pin, guard or audit policy was changed. All full build/audit,
regression, independent review and final verification gates remain required.
No chapter or #1021 is accepted by this correction.
