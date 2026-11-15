# Bounded handoff of accepted ordinary compiler outputs

Read-only assessment by /root/cache_migration_assessment, 2026-11-03.
This is operational preparation under10000, not an implemented or approved
migration, a compiler result or an acceptance certificate. Root owns any future
mutation. The assessment changed no file, process, compiler, cache, ref or
remote state and did not execute the stock hashing subprocess.

## Observed space and selection

At02:17:56UTC the existing warm-chapter02-candidate-r3.py selection rules would
select741 complete donor groups/5187 files:359478145 logical bytes and an
estimated374005760 destination allocated bytes. Available space was462946304,
leaving88940544 before further full901 outputs,99 compilation/audit or another
restore-tested checkpoint. The largest selected group was
SquareKit.Internal.PathTransport.Typed,22673999 bytes. Eleven modules with
pre-existing target outputs were skipped. No unstable/incomplete selected group
was observed by the parser. These observations occurred while901 was building;
they do not validate those outputs or predict the final selection size.

Ordinary build logical sizes observed were901459556589,998019280,
a353857483,36165698972,3dd87102765 and57789351399 bytes. The donor also contained
about99.4MB in102 generated setup files outside saved-output groups. Both donor
and target were device27, all observed regular files had link count1, and no
build-directory symlink was observed. Reflinks are separately known unsupported.

The current full-copy warmer fits this snapshot only. It does not preserve a
credible reserve for further compilation/checkpoints or repeated downstream
copies. The suggested change is only the lifecycle of ordinary outputs after
accepted-candidate validation: bounded copy, independently verify, then retire
the corresponding source ordinary files. Keep source, dependencies, verification
records, stock guard, hash adapter, source selection and target's own gate intact.

## Required ordering and safeguards

1. Wait for actual exact901 full build/audit, matching record, both reconciled
   independent axes and immediate final verification/acceptance. Preserve that
   evidence first. Never migrate from the active donor.
2. Freeze both build directories. Reconfirm exact clean source heads, pinned
   configuration/tooling and absence of compiler/writer users. Source files,
   dependencies and .lake/verification.json are outside retirement scope.
3. Select modules using the existing identical-source and complete-output rules.
   Skip a whole module if any target module output already exists. Preserve the
   target's existing25 focused groups, and do not mix or overwrite generations.
4. Use bounded batches, provisionally64MiB, with a measured checkpoint/compilation
   reserve. The assessor suggested256MiB as a lower provisional reserve; root
   should compare it with actual checkpoint peak needs and choose more if needed.
   Stop before a batch if reserve would be consumed; never weaken it to make a
   transfer fit. The observed largest group fits64MiB.
5. Before retirement, copy every required artifact/sidecar, publish each trace
   last, retain original trace descriptors, sizes and SHA256, and verify stable
   source identities/content. Run unchanged stock inspect_outputs on the fixed
   target batch in the pinned environment. Record complete target success before
   starting any source deletion.
6. Retire only the verified source group: remove its source trace first, then
   its already copied artifacts/sidecars after rechecking captured identities.
   Leave skipped groups, setup files, source/configuration files, dependency
   outputs and verification records intact. Each verified group then has one
   ordinary retained copy in the next candidate.
7. Run99's unchanged own stock candidate gate. Migration copies no approval,
   audit success or verification record. Stock Lake/integrity checks still
   decide reuse and rebuilds. Apply the same separate gates to later candidates.

Whole-directory moves, per-file rename migration, hardlinks and trace editing
were rejected. Verified copying has the simpler recovery property: the complete
source group remains until its complete target independently passes the stock
output check. The measured problem needs bounded temporary duplication, not a
different validation model.

## Failure and continuation requirements

Journal each group/batch through planned, copied, target-verified,
source-retirement-started and source-retired. Persist the successful complete
target verification before deleting any source file. Preserve old attempts;
use a distinct continuation record rather than overwrite a failed run.

A pre-verification failure retains the entire donor group and diagnostic
target partial copy. A retirement failure retains the complete verified target,
and the journal identifies remaining donor files. A retry must reconcile its
own pre-existing target files with its prior journal/hashes or stop for root
investigation; it cannot silently skip an interrupted owned transfer. Never
overwrite unrelated outputs. Source change or unexplained hash mismatch must
stop with evidence; do not rewrite traces or call guard repair to reconcile it.
Insufficient space stops before the next batch, retaining completed handoffs.

The old warmer refuses an existing final record and records completion only
at the end. Preserve the no-overwrite protection and add explicit durable
progress before retirement. Implementation, meaningful failure-path checks
and independent operational review are still required before any migration.
