# conaled / PFDS union — current recovery status

Updated for checkpoint040 on 2026-11-03 (Atlantic/Reykjavik).
Goal: the complete union of the published book and 1996 thesis, in book chapter
order with necessary cross-cutting foundations. The whole union is **not complete**.
Local tickets/history only; no GitHub writes. Expose and upload each recovery
checkpoint immediately. Governing requests: requirements/REQUEST.md,
REQUEST-union-v2.md, and REQUEST-recovery-039.md.

This status supersedes checkpoint039's live scheduling. Its full prior status is
preserved at validation/status-before-checkpoint040.md. Historical logs and
running records remain unchanged. Never reuse old exec-session handles.

## Accepted frontier

Chapter1 introductory accounting is accepted; its16 forward complexity contracts
remain open. Chapter2 is earliest unaccepted. Chapter3 algorithm implementation
has not begun. Later chapter source preparation is retained as preparation.

Main conaled/pfds/local is clean at76d77a107deb37c30e0b061c30b03a3f8c6aa12c.
Original upstream base remains7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd.
Complete local history,24 tickets,135 coverage rows and83 exercise records survive.
The coverage ledger and prior accepted statuses are unchanged.10023 is now
explicitly blocked on required validation in the unavailable recovered environment.

## Exact unaccepted candidates

| Scope | Exact candidate | Preserved branch | Disposition |
| --- | --- | --- | --- |
| 10013/10018 | 901f734161920a76f3b399a575805b9a1d31e971 | pfds/import-footprint-r3 | Existing static reviews; fullr2 terminal result unknown |
| Chapter2 | 99a29dcd02eb529fbefbb675e244a8c47b78cdef | pfds/ch02-review-r3 | Existing static reviews; own gate pending prerequisites |
| 10014 | a3feaff319ad5fad912fb8bdc113f33fea4e2a60 | pfds/suspensions-review-r3 | Existing focused/static evidence; own full gate pending |
| 10019 | 361f5f3f6bb3de1974510ce355883dac2bf25333 | pfds/pure-suspensions-review-r2 | Existing static reviews; own full gate pending |
| 10020 | 3dd930c3e3989f3e5530463f3ac937a629551335 | pfds/cache-counts-review-r1 | Existing focused/static evidence; own full gate pending |
| 10021 | 577be121e074ddb5de6727a7481c115cb61b3b27 | pfds/persistent-accounting-review-r3 | Existing focused/static evidence; own full gate pending |
| 10022 | 5e048f781aa04be9ce993f1e7455bdc82df22bff | pfds/body-counts-review-r1 | Existing focused/static evidence; own full gate pending |
| 10023 | d24c443ba22019613b1ce646d6eed7279c791ad6 | pfds/signed-potential | Source findings corrected; both r2 axes Blocked on validation |

The901 validation dependency is separate from ancestry:901 is not an ancestor
of99. Twelve of its14 recorded files match99; public imports and its research
document differ. The99→a3→361→3dd→577→5e→d24 ancestry chain is valid. Every scope
retains its own fixed bases, requirements, full gate and review obligations.

All listed candidates need their own clean isolated pinned-Nix stock
./check.sh --candidate HEAD, full project build, exhaustive audit, matching
.lake/verification.json, both independent full-scope review outcomes, and
immediate ./check.sh --verify-candidate HEAD before accepting identical bytes.
No admission, new axiom, native proof shortcut, proof-budget increase, linter
suppression or weakened gate is authorized. Freeze compiler inputs. At most
one full gate plus one focused wrapper may run concurrently.

## Current environment blocker

Nix, direnv, Lean, Lake and elan are absent from PATH. /nix and /proc are absent.
The official rootless local-store route needs Linux mount/user namespaces; the
actual namespace probe failed because /proc/self/uid_map is absent. The standard
store creation request `mkdir -m 0755 /nix` was rejected before execution by the
automatic policy, which disables sandbox escalation. No installation occurred.

Read environment/recovery-040.md, recovery-040.json and recovery-040-approval.json.
Official Nix manuals were fetched successfully; this is not a general network
failure. No compiler, project build, proof audit or candidate verifier ran in
this recovered workspace. Pins, flake, lockfiles, checks and policies are unchanged.
Continuation needs a conventional permitted Nix environment or one supporting
the documented namespace route. Source review cannot close these gates.

## Recovery and unknown terminal results

Input039:76523489bytes, SHA256
c9df19c0c3af4c08295cca6e0dabeadf3775e4ec8f0148e90295f8e2317947d1.
The restore script verified members and restored to a new directory. Independent
audit verified all901 manifest members,895 session files,46 named refs,342
candidate-source comparisons and10 requirement hashes; Git fsck and bundle
verification passed. Read research/recovery-040-audit.md and
validation/recovery-040-audit.json. Fresh upstream AGENTS.md is byte-identical
to the restored copy. Its digest is preserved in the environment record.

Full901r2 and signed-potential9c focusedr2 have only historical partial records,
without terminal exit codes/end times. Their recoverable disposition is
interrupted, terminal outcome unknown. No original termination cause is inferred.
All44 signed-potential inputs match9c, and some core/consumer completion lines
survive, but neither complete eleven-target success nor final-input checking
is recorded. That example source also predates the newd24 annotation correction.
validation/recovery-040-interruptions.json binds the original records/logs and
focused targets. Preserve them and repeat required scopes with genuine evidence.

Only main and signed-potential source checkouts are materialized here. All other
candidates survive in Git refs. Nix stores, dependencies, ordinary outputs,
inactive-output stashes and old worktree paths were not in the source checkpoint.
Historical cache-migration/retirement records do not establish their presence.
Old wrappers contain absolute paths under /workspace/scratch/ca9a61d0bf30 and
must not be executed unchanged. Restore reviewed locking/recording behavior at
the actual new paths before validation; preserve all original records.

One10014 tracker link now names the actual preserved terminal record at
validation/checkpoint016-progress/suspension-derived-r10.json. Both historical
reviewers already used that path. No acceptance/dependency decision changed.
Evidence: validation/recovery-040-tracker-correction.json.

##10023 source correction and independent review

Both fixed bases remain5e048f781aa04be9ce993f1e7455bdc82df22bff. Full scope is
six files/three commits/no exclusions under requirements/signed-potential.md v1,
SHAbb28d4f56eb48c80d2a9905b6e349d3e4b6fdb4e4ad2a01976408432a434ac81.

The first complete independent reviews of9c identified missing noncomputable
boundaries on FractionalSavings.step and DebtSign.step in
Examples/SignedPotential.lean. Exact pinned Mathlib source confirms Real division
is noncomputable. Root added only those two qualifiers in commitd24c443. Types,
bodies, theorem statements, proofs and numerical expectations are unchanged.

The same independent reviewers reassessed the entire corrected scope. Standards
SIGNED-POT-STD-CODE-001 and Spec SIGNED-POT-SPEC-001 are fixed with source-review
evidence. No unresolved static source/prose finding remains. Standards
SIGNED-POT-STD-VAL-001 (High) and Spec SIGNED-POT-SPEC-VAL-001 (Blocking) remain
unresolved; both outcomes are Blocked. No compiler-success claim is made.

Root read all complete reports and reconciliations. The retained record is
reviews/signed-potential.md. Full reports are
reviews/signed-potential-{standards,spec,coordinator}-r1.md and -r2.md.
The correction and exact two-line patch are recorded in
research/signed-potential-noncomputable-correction-r1.md and
validation/signed-potential-noncomputable-correction.patch.
Current identities and root receipt are
validation/signed-potential-recovery-review-r2.json and
validation/signed-potential-recovery-review-receipt.json.
All writers are frozen; the corrected source is committed and clean.

## Manuscripts

The thesis was reacquired from
https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/dissertation.pdf
and matches its recorded628877byte SHA256
f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072.
Byte verification is not a new content-inspection claim.

The published book is absent and must be reattached for further source checks.
Expected9356709bytes, SHA256
b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41.
Historical source reading, inventories, exercises, variant corrections and page
identities are preserved. Historical Library IDs do not authorize retrieval of
other-conversation files. Manuscripts remain outside repository/checkpoint
payloads. Read research/recovery-040-source-availability.json and
research/union-source-identities.json.

## Exact continuation once the environment is available

1. Recreate exact candidate checkouts from saved refs and restore clean pinned
   dependencies through the documented Nix/Lake workflow. Assume no ordinary
   outputs or approval records have been restored.
2. Repeat901's full gate and continue its existing10013/10018 review handoff
   through final verification. In the permitted separate focused slot, repeat
   the original eleven-target scope on correctedd24.
3. Run99's own full gate and retained reviews, then immediate final verification
   before a main fast-forward. Only Chapter2 acceptance permits Chapter3
   implementation. Complete Chapter3 requirements and readiness inventories survive.
4. Continue a3→361→3dd→577→5e→d24 own gates/reviews in sequence. All source
   debit/work/forcing and operational chronology obligations retain their owners;
   algebraic accounts do not discharge them.
5. Continue the entire book/thesis union and appendices. Do not replace missing
   proofs by preparation notes or count unavailable gates as passing. Preserve
   and immediately expose/upload each new recovery checkpoint.

The reviewed checkpoint generator remains unchanged at SHA256
617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab.
It tests an actual restoration before publishing each archive. A checkpoint's
post-creation upload receipt necessarily postdates that archive and is retained
for the next one; no receipt or proof-completion claim is invented in the payload.

## Post-creation receipt for checkpoint040

Saved and exposed after actual restoration passed: libfile_3e3a75a310b08191a4332feca5f3e166, 76588781 bytes, SHA256 69623d41d0b159d0ac766eec3f3dcf70779dd75245edfdd057b4e346359f3941.
The exact manifest, creation result and upload receipt are retained locally for the next checkpoint. This receipt necessarily postdates the040 payload.
