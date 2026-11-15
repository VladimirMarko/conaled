# Native ordinary-output handoff: feasibility at checkpoint 044

Read-only investigation by `/root/recovery_audit`, 2026-11-03. This is planning
within the existing task, not an implementation, review round, approval, actual
transfer, accepted-donor receipt or statement of process quiescence.

## Decision

**No supported native route currently satisfies the approved output-migration
contract in this proc-less workspace. Use separate ordinary builds in the
appropriate isolated checkouts when ordinary artifacts are needed.** The
running native fresh901 gate must continue untouched. Its eventual success,
if obtained, would neither establish donor acceptance by itself nor populate
a complete ordinary Lake output cache for migration.

The user's saved direct-toolchain exception permits launching pinned tools
without Nix. It does not remove the handoff's process-user checks, source and
runtime identity requirements, stock verifier, durable lifecycle, donor
acceptance or target gates. The existing helper has no supported alternate
quiescence provider. Replacing its checks with a successful assertion, setting
a false Nix marker, calling its fixture seam directly or rewriting evidence
would not preserve the approved contract.

## Exact compatibility obstacles

Locations below refer to the current files read, without executing them.

| Boundary | Existing implementation and native evidence | Consequence |
| --- | --- | --- |
| Launch environment | `session/validation/migrate-accepted-outputs.py:300–316` requires `IN_NIX_SHELL` equal to `pure` or `impure`, `LEAN_NUM_THREADS=1`, and no `LEAN` variable; it removes `LEAN_PATH`. `session/environment/run-native-toolchain.py` supplies the real pinned native profile and one thread but does not turn that launch into a Nix shell. | The user exception removes the policy need for Nix, but the approved helper still has the literal precondition. A truthful native implementation would be a changed candidate requiring continuation of the existing operational review. This alone would not solve quiescence. |
| Required process visibility | `migrate-accepted-outputs.py:257–297` reads its ancestor `/proc/<pid>/stat`, enumerates `/proc`, then inspects cwd/argv and workspace-owned fd/mapping users. It is called initially at `:349` and repeatedly by `stable_scope` at `:351–363`. The initial ancestry read and enumeration have no proc-less fallback. | Given the supplied proc-less environment, this required evidence cannot be obtained through the supported helper. No live probe was made. Waiting for a known job or observing a terminal record is not the helper's complete process-user check. |
| Native adapter scope | `session/environment/native-own-exe.c:1–13,40–45,65–94` only permits a narrowly validated fallback for the executing process's own `exe` readlink, after an underlying ENOENT. It implements neither process enumeration nor stat/cmdline/cwd/fd/maps. | The approved adapter cannot provide the missing quiescence evidence. Extending it into a general process-filesystem replacement is outside this task and is not proposed. |
| Cooperative locks | Migration takes both `active-validation/full-build.lock` and `focused-build.lock` nonblocking (`:317–322`). `run-native-validation.py:389–400` uses those same names, selecting the appropriate one. | Lock names are compatible. The active full gate owns its lock. Later acquiring both locks would prevent cooperating controller jobs, but the approved contract also requires the repeated visible-process check and a frozen source/target. Lock acquisition alone cannot substitute for it. No lock was acquired or probed here. |
| Exact stock-command grammar | Migration `recorded_command` (`:88–98`) accepts `--candidate HEAD`, optionally with `--fresh` before or after it. The actual native record and `run-native-validation.py:175–177,253–258` use `--candidate HEAD --fresh --jobs 1`. | The old reader rejects the native fresh command because of the additional required serial-job arguments. Removing them from historical argv would misstate the actual run; omitting them from the active run would change its frozen inputs. |
| Evidence path namespace | Migration `evidence` (`:64–79`) accepts only session-relative paths beginning `validation/` or `reviews/`. Its full-check binding (`:131–133`) requires `full.verification_evidence` to equal the receipt's verification path exactly. Native records write and verify the workspace-relative `session/validation/<run>.verification.json` (`run-native-validation.py:194–201,332–338`). | No receipt path can satisfy both current checks for an unmodified native record. The mismatch also affects an incremental native full record; changing command mode alone does not fix it. Neither the original command record nor the stock success record should be rewritten to fit the old envelope. |
| Native evidence binding | The native controller validates runtime, exact command, both exit fields, terminal observation, equal queued/start/final snapshots, clean inputs, saved log and verification bytes, and links final verification to the same full record (`run-native-validation.py:164–203,243–278,316–338`). The old migration reader checks its older subset and has no explicit native runtime/controller identity contract. | A future compatibility change would need to consume the genuine native evidence chain and bind the actual launch/profile inputs, while preserving the original records. Accepting a loosely relabeled old envelope is not an established native route. |

These are independent obstacles. Supporting native command/path metadata would
not establish process quiescence. The current official-profile approval and
successful focused runs do not approve a changed migration helper.

## What remains compatible, and what the old approval covers

The complete 677-line helper, 352-line tests, 311-line implementation handoff,
requirements, preparatory design, both full axis reports, coordinator report,
retained finding record, readiness record and fixture evidence were read. The
old approved operational candidate is
`2748089840723943ddc8ae58acd82f5728b2098b`, fixed base
`27a2b897983eb0e60b6ebe1ffa2b0b6c4ece6405`. Both axes passed helper readiness
with zero findings. They explicitly left real Nix/compiler/hasher invocation,
actual Git/dependency and process preflight, lock contention, real migration
and power-loss recovery unexercised. The fifteen disposable tests use a
literal-byte fixture verifier; their CLI refusal test stops on missing
acceptance before any external runtime. They supply no native/proc-less
preflight coverage. See `session/reviews/output-migration-{standards,spec,coordinator}-r1.md`
and `session/validation/output-migration-{readiness-r1,r1-fixtures}.json`.

The existing transfer lifecycle is independent of Nix at the filesystem level:
identical tracked source and complete-group selection; whole-module skip for
existing target outputs; private regular files; exclusive trace-last copies;
source and destination identity/byte checks; durable target verification before
trace-first retirement; fixed pair journals and explicit failed-attempt
reconciliation. Its 64 MiB batch cap, 320 MiB reserve and additional 32 MiB
journal allowance remain binding. None needs to be weakened to describe native
execution, but these properties alone do not authorize entry through an
unsupported production preflight. See helper `:486–664` and requirements 4–9.

The unchanged guard still has a potentially compatible native execution path:
`conaled/scripts/lake_integrity.py:71–99` runs the original
`lean --run scripts/lake-output-hashes.lean` and compares actual artifact hashes
against saved trace descriptors; the Lean script uses `Lake.computeBinFileHash`.
An approved native launch can supply that actual compiler. This investigation
did not execute the hasher or establish production migration verification.
The helper's fixed guard/hash-script identities, no-repair rule and independent
source/target verification must remain intact. The fixture verifier is not an
alternative production validator.

Acceptance also remains separate. Requirements 1 and 8 demand real donor
full/audit/verification evidence, both independent axes for each scope (10013
and 10018 for donor901), immediate final verification and recorded acceptance.
The source verification stays at the source; the target receives no approval
and still needs its own complete workflow. No accepted receipt or migration
plan was constructed in this investigation.

## Fresh outputs do not provide the proposed saving

The actual `session/validation/import-901-native-fresh-r2.json` was read once
as a status snapshot. It identified candidate
`901f734161920a76f3b399a575805b9a1d31e971`, checkout `import-correction-r3`,
mode `full`, runtime `native`, stock mode `fresh`, `status: running`,
`terminal_result_observed: false` and `acceptance: false`. It is not terminal
success or accepted-donor evidence. No process visibility or later outcome is
inferred from those fields.

`import-correction-r3/scripts/check.py:313–326` compiles and audits fresh
project outputs inside a `TemporaryDirectory` under `.lake/fresh-check-*`, then
removes it. README `:204–218` states that this route reuses external dependency
caches but neither reuses project artifacts nor populates Lake's ordinary cache.
Migration selects only ordinary `.lake/build/lib/lean/*.trace` groups
(`migrate-accepted-outputs.py:510–549`). Existing ordinary artifacts, if any,
must be assessed independently; their completeness is not implied by fresh
success. Do not capture, relocate or relabel active temporary fresh outputs as
ordinary Lake groups.

Consequently an ordinary-output handoff cannot reduce the project compilation
performed by another required `--fresh` gate. It could only help a later
permitted incremental build or ordinary-artifact consumer, after its own
preconditions are satisfied. `scripts/test-proof-audit.py` is such an ordinary
consumer: it reads `.lake/build/lib/lean/Applications` and imports `ProofAudit`.
Fresh validation alone does not create that ordinary layout.

## Safe continuation

1. Let native fresh901 complete under its frozen inputs. Preserve its real
   terminal outcome, applicable regression evidence, separate review scopes
   and immediate final-verification/acceptance sequence. A failed or interrupted
   gate remains failed or interrupted.
2. After the active compiler workload ends, use the approved native launcher
   and existing serial/cooperative scheduling to build required ordinary
   targets directly in each appropriate isolated checkout. Preserve existing
   focused outputs and use the unchanged stock checks where applicable. Keep
   each target's own full/audit/review/final-verification obligations; ordinary
   build success is not acceptance and does not replace a required fresh gate.
3. Leave the approved migration helper, old requirements/reports, current
   runtime/controller and candidate records unchanged. There is no supported
   native production invocation to recommend now, and no transfer saving should
   be included in the immediate plan.
4. Reconsider migration only if a permitted environment or documented capability
   can supply the required real quiescence evidence. Any genuine native support
   would then continue the existing output-migration loop with exact captured
   source, the preserved invariants, native evidence compatibility, meaningful
   tests and both independent axes. This note starts none of that work and
   proposes no weaker replacement contract.

Only this analysis file was written. No compiler, build, test, hash calculation,
helper invocation, network request, process-filesystem probe, lock operation,
transfer, retirement or source/runtime/record mutation was performed. Historical
approval identities above are attributed to the retained records, not newly
recomputed artifact hashes. No production or formal approval is claimed.
