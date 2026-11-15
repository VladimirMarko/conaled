# conaled / PFDS union — current recovery status

Updated for checkpoint042 on 2026-11-03 (UTC).
Goal: the complete union of the published book and 1996 thesis, in book chapter
order with necessary cross-cutting foundations. The whole union is **not complete**.
Local tickets/history only; no GitHub writes. Expose and upload each recovery
checkpoint immediately. Governing requests: requirements/REQUEST.md,
REQUEST-union-v2.md, REQUEST-recovery-039.md, REQUEST-direct-toolchain-041.md,
REQUEST-environment-handoff-042.md, and REQUEST-native-toolchain-042.md.

This status supersedes checkpoint041's QEMU-only continuation. Its full prior
status is preserved at validation/status-before-checkpoint042.md. Historical
failed/partial records remain unchanged. Never reuse old exec-session handles.

**Recovery entry point: environment/RECOVER-ENVIRONMENT.md.** The archive README
and restore-success output now point there. The user asked for native alternatives
because emulation is too slow. A native compatibility profile genuinely runs the
unchanged exact compiler; QEMU remains a tested fallback. Read the current
operational review record before treating any new runtime as approved.

## Accepted frontier

Chapter1 introductory accounting is accepted; its16 forward complexity contracts
remain open. Chapter2 is earliest unaccepted. Chapter3 algorithm implementation
has not begun. Later chapter source preparation is retained as preparation.

Main conaled/pfds/local is clean at76d77a107deb37c30e0b061c30b03a3f8c6aa12c.
Original upstream base remains7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd.
Complete local history,24 tickets,135 coverage rows and83 exercise records survive.
The coverage ledger and prior accepted statuses are unchanged. 10023 still needs
its required validation; direct Lean/Lake execution is now available.

## Exact unaccepted candidates

| Scope | Exact candidate | Preserved branch | Disposition |
| --- | --- | --- | --- |
| 10013/10018 | 901f734161920a76f3b399a575805b9a1d31e971 | pfds/import-footprint-r3 | Existing static reviews; QEMU fresh interrupted; native full pending |
| Chapter2 | 99a29dcd02eb529fbefbb675e244a8c47b78cdef | pfds/ch02-review-r3 | Existing static reviews; own gate pending prerequisites |
| 10014 | a3feaff319ad5fad912fb8bdc113f33fea4e2a60 | pfds/suspensions-review-r3 | Existing focused/static evidence; own full gate pending |
| 10019 | 361f5f3f6bb3de1974510ce355883dac2bf25333 | pfds/pure-suspensions-review-r2 | Existing static reviews; own full gate pending |
| 10020 | 3dd930c3e3989f3e5530463f3ac937a629551335 | pfds/cache-counts-review-r1 | Existing focused/static evidence; own full gate pending |
| 10021 | 577be121e074ddb5de6727a7481c115cb61b3b27 | pfds/persistent-accounting-review-r3 | Existing focused/static evidence; own full gate pending |
| 10022 | 5e048f781aa04be9ce993f1e7455bdc82df22bff | pfds/body-counts-review-r1 | Existing focused/static evidence; own full gate pending |
| 10023 | 3cf3de4fbc24c1a144353ae64b13b72f5ead54a5 | pfds/signed-potential | d24/956 failures retained; corrected native eleven-target focus passed; own full gate pending |

The901 validation dependency is separate from ancestry:901 is not an ancestor
of99. Twelve of its14 recorded files match99; public imports and its research
document differ. The99→a3→361→3dd→577→5e→d24→956→3cf ancestry chain is valid. Every scope
retains its own fixed bases, requirements, full gate and review obligations.

All listed candidates need their own clean isolated exact-toolchain stock
./check.sh --candidate HEAD, full project build, exhaustive audit, matching
.lake/verification.json, both independent full-scope review outcomes, and
immediate ./check.sh --verify-candidate HEAD before accepting identical bytes.
No admission, new axiom, native proof shortcut, proof-budget increase, linter
suppression or weakened gate is authorized. Freeze compiler inputs. At most
one full gate plus one focused wrapper may run concurrently.

## Native alternative and current environment evidence

The native implementation executes the official Lean/Lake/leanir ELF bytes
without CPU emulation. It supplies only missing own-executable metadata through
a bounded library: delegate to existing readlink first; act only on ENOENT for
an exact own link with a per-invocation marker matching canonical absolute ELF
launch metadata. Other operations/errors and inherited preload precedence remain.
No compiler/kernel binary, project pin, stock check, mount or host permission
was changed. Its unsupported cases and frozen-input contract are explicit.

Source: environment/native-own-exe.c and run-native-toolchain.py. Exact versions
remain Lean4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc and bundled
Lake5.0.0-src+eb6cafb. Native version, real valid/false theorem and executable
checks passed. All18 bounded metadata tests passed on the guarded resolver.
A new cold native profile was reconstructed from immutable candidate source;
its valid theorem/no-axioms check, false-theorem rejection, Lake build/link/run42,
all18 metadata cases and evidence-runner refusal tests passed. See
validation/native-toolchain-candidate-validation-r6-042.json and the explicitly
matched reuse/current-controller checks in -r7-042.json. The final operational
scope is18files, fixed base76d77a1, current candidateaf2c53dce68ebb122c81175312d6bb30df9aac05.
Both independent replacement axes passed this exact operational candidate with
zero unresolved findings. Root read both complete reports and reconciliation,
then verified all18 committed/isolated/delivered files, requirements, reports
and native profile identity. Operational acceptance is recorded in
validation/native-toolchain-final-verification-042.json. Incomplete earlier
rounds supply no approval; no formal acceptance follows from this tooling pass.

Review coordination continues the same reviews/direct-toolchain.md loop.
Completed r2 approval of the unchanged eight QEMU helpers remains historical.
The replacement coordinator is direct_toolchain_validation_plan, with independent
Standards recovery_audit and Spec chapter02_continuation_plan. The native fixture
author was excluded from independent review. Existing finding IDs/closures remain.

The supplied guide is preserved byte-identically, with SHA256
 ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1.
Its other checkpoint039/adwh branch is a separate workstream. Its exact Ubuntu
QEMU package was independently authenticated through the installed public keyring,
signed InRelease and exact index/stanza/package; that binary was not executed or
selected. See environment/environment-route-comparison-042.md and
qemu-ubuntu-042/. Do not follow its other-conversation Library references.

Native startup is much faster, but large imports still incur heavy I/O/page
faults. One same-fixture pair was31.786s native versus86.080s QEMU; another native
run took102.323s. All11870 imported regions mapped successfully, totaling about
2.009GB of artifacts. These are measured examples, not a general speedup claim.
See environment/native-performance-analysis-042.md and complete actual records.
No additional normal native execution host is exposed in this session.

## Current formal run outcomes

- `validation/import-901-direct-fresh-r1.json` is the preserved QEMU partial
  record. Root interrupted its owned tool session after the user's native
  steering; the tool returned130 and the full lock was free. The wrapper did
  not finalize a compiler result. The explicit interruption record binds its
  original bytes/log. It reached28/957 module completion messages; that is not
  a full pass or audit. Old unknown-terminal901 runs remain unknown.
- `validation/signed-d24-direct-r1.json` genuinely finished1 with unchanged
  inputs and clean exactd24. Example proof names and a budget equation failed.
- `validation/signed-956-native-r1.json` genuinely finished1 with unchanged
  inputs and clean exact956. Examples.SignedPotential compiled; only the
  transport example failed because the generalized budget inferred Real before
  the intended whole-sum cast. These are source failures, not runtime acceptance.
- Exact3cf adds the inner Nat type before the Real coercion. Definitions, theorem
  statements, hypotheses and numerical expectations are unchanged. Its native
  eleven-target run `validation/signed-3cf-native-r2.json` finished with exit 0
  at 17:14:27 UTC, terminal result observed, unchanged inputs and clean exact3cf.
  All eleven requested targets succeeded (Lake reported 935 jobs, including
  dependencies). This is focused development evidence, not the full audit.
  The native full901 gate has not yet been launched.

The native runner captures exact source/dependency/runtime/controller inputs,
keeps exclusive new evidence and lock discipline, and always records
`acceptance:false`. `--focus-candidate` pins an explicit corrected40-digit SHA
in the fixed signed-potential checkout; it cannot override full/verify901.
Every formal candidate still needs its own full build/audit, both independent
reviews and immediate matching stock verification. No chapter acceptance moved.

## Historical QEMU toolchain recovery (checkpoint041 baseline)

The user explicitly clarified that Nix is optional for continued development.
The former Nix installation failures remain historical evidence in
environment/recovery-040.md, recovery-040.json and recovery-040-approval.json;
they no longer block the permitted direct-toolchain route.

The official Lean 4.35.0 Linux release was downloaded and its exact size and
official SHA256 verified. Its unchanged compiler reports commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc; the bundled Lake reports
5.0.0-src+eb6cafb (Lean 4.35.0). This workspace lacks /proc, so normal native
startup cannot locate the executable. A verified official Debian QEMU user-mode
binary supplies the guest's own executable metadata. A separate profile launches
byte-identical Lean/Lake/leanir executables; no compiler patch, system install,
mount, protected-path access, or permission change is used.

Actual tests pass for both versions, valid theorem checking with no axioms,
false-theorem rejection with a type error, Lake compiler selection, and native
executable compilation/linking/execution. The pinned mathlib cache executable
built successfully, and ordinary cache get downloaded and decompressed all
9031 requested dependency files with exit 0. All nine dependency repositories
remain clean at the exact manifest revisions after the operation. Each candidate
has its own project build directory and shares only the dependency store.

Read environment/README-direct-toolchain.md and the adjacent provenance,
CLI/build test, package-link and post-cache identity records. The authored
helpers and recorded validation wrappers passed both independent review axes
on synthetic artifact candidate822cb7adeed4943acaf10454e9facfc2e3ee8ceb.
All eight delivered files match the approved snapshot at final verification;
see validation/direct-toolchain-final-verification-041.json and
reviews/direct-toolchain.md. The smoke tests do not replace any formal
candidate's full check or audit. The first full run after this tooling recovery
must use the stock fresh route with one job; final verification reads its mode.
Project pins, flake, lockfiles, checks and proof policies remain unchanged.

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

Main, import-correction-r3 and signed-potential source checkouts are materialized
here. All other candidates survive in Git refs. Nix stores, dependencies, ordinary outputs,
inactive-output stashes and old worktree paths were not in the source checkpoint.
Historical cache-migration/retirement records do not establish their presence.
Old wrappers contain absolute paths under /workspace/scratch/ca9a61d0bf30 and
must not be executed unchanged. Restore reviewed locking/recording behavior at
the actual new paths before validation; preserve all original records.

One10014 tracker link now names the actual preserved terminal record at
validation/checkpoint016-progress/suspension-derived-r10.json. Both historical
reviewers already used that path. No acceptance/dependency decision changed.
Evidence: validation/recovery-040-tracker-correction.json.

## Historical10023 d24 source correction and independent review

Both fixed bases remain5e048f781aa04be9ce993f1e7455bdc82df22bff. Full scope is
six files/three commits/no exclusions for that historical d24 round under
requirements/signed-potential.md v1,
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
That d24 review snapshot remains preserved. Current proof-only corrections956/3cf
and their compiler evidence are listed above; they require applicable new review.

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

## Exact continuation

1. Recreate the current environment using environment/RECOVER-ENVIRONMENT.md.
   Preserve the user's native preference and the completed operational
   review/identity evidence. Do not treat old smoke tests as formal acceptance.
2. Retain the corrected3cf focused success and continue the existing10023
   review loop on its full current scope. Preserve actual earlier failures.
   Its own full/audit gate remains later in the existing integration sequence.
3. Run901's own fresh stock gate through run-native-validation.py using a new
   run ID and --fresh; close its existing10013/10018 review findings with actual
   terminal evidence and immediate final verification. Source/gate inputs stay frozen.
4. Run99's own correctly bound full gate/reviews/final verification before main
   fast-forward. Only Chapter2 acceptance permits Chapter3 algorithm work.
5. Continue a3→361→3dd→577→5e→3cf exact own gates/reviews in sequence, then the
   whole book/thesis union and appendices. The source work/debit/forcing and
   operational chronology obligations retain their owners. No source gap or
   unavailable gate counts as complete.

The checkpoint generator differs from its previously approved source only in
its generated README and restore-success pointer. Current SHA256 is
22928db23012fb28c9dee74b3af4998d18587ec91e728d0b2afcf647c6ac47ad.
The full previous source and small patch are preserved. Real archive restoration
still must pass before each archive is exposed/uploaded. A post-creation upload
receipt necessarily postdates its own payload and is retained for the next one.

## Post-creation receipt for checkpoint040

Saved and exposed after actual restoration passed: libfile_3e3a75a310b08191a4332feca5f3e166, 76588781 bytes, SHA256 69623d41d0b159d0ac766eec3f3dcf70779dd75245edfdd057b4e346359f3941.
The exact manifest, creation result and upload receipt are retained locally for the next checkpoint. This receipt necessarily postdates the040 payload.

## Post-creation receipt for checkpoint041

Saved and exposed after actual restoration passed: libfile_e5a8e0445df081918d892f49e57cbd6d, 76796513 bytes, SHA256 42886cbe040211571e9dba330e67e08dcfc1c3d6a962b40fb54cf987cf4f0301.
This receipt and the detailed creation/upload records postdate the041 payload and are retained for the next checkpoint.

## Post-creation receipt for checkpoint042

Saved and exposed after actual restoration passed: libfile_b729cb34fd608191a7a0a4d4e539db74, 78935007 bytes, SHA256 d256cc3c0fd1f0bedcedbb5c74dd4c44f4d53d3c3533fc429a16ecac54896192.
The archive contains the approved native tooling and complete environment recovery
guide, both operational reviews, local history/tickets and the genuine focused3cf
success. Its own upload receipt postdates the payload and is retained for the next
checkpoint. Native full901 remains the next gate.

## Native continuation after checkpoint042

The approved native runner launched `import-901-native-fresh-r1` on exact901
with stock `./check.sh --candidate HEAD --fresh --jobs 1`. Its record and log
are under `validation/`. Consult their actual terminal state; launch is not
success. Runtime, controller, dependencies and source inputs remain frozen.
The existing prerequisite review loop is being taken over by the current
coordinator and independent reviewers with retained findings and identities.

## Current10023 static review after checkpoint042

Both independent axes completed the full current3cf six-file/five-commit scope.
There are zero new or unresolved source findings, and the genuine eleven-target
focused success is established. Standards retains its High validation finding;
Spec retains its Blocking validation finding. Both outcomes remain Blocked on
3cf's own full build, exhaustive audit, success record and immediate final verify.
Root read both complete reports and reconciliation; identities are retained in
validation/signed-potential-root-static-receipt-r3-043.json.
