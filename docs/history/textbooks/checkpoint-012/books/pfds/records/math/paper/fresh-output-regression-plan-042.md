# Fresh outputs as regression-fixture inputs: read-only planning

Prepared 2026-11-03 by `/root/direct_toolchain_validation_plan` at root's
request. No artifact was copied, moved, deleted, opened for mutation or used
for a test. No compiler, build, candidate verifier or test was executed. This
is a feasibility and scope assessment, not operational approval or validation.

## Conclusion

The approved ordinary-output migration helper does **not** implement or approve
this proposed operation. A separate, explicitly bounded capture protocol could
retain genuine completed fresh artifacts as untrusted quarantine data, then
use a complete matching generation solely for the unchanged negative-audit
regression suite after the actual full fresh gate succeeds. Its implementation,
artifact-appropriate validation and independent review would belong to the
existing operational recovery work. If that protocol is not established, keep
the genuine ordinary `lake build +ProofAudit` preparation already planned.

This proposal would save the second full project recompilation needed only to
populate the normal path expected by `scripts/test-proof-audit.py`. It does not
skip the original full fresh build, its exhaustive audit, the negative tests,
either formal axis, or final stock verification.

## Existing rules and exact stock behavior

The approved helper scope is preserved in `requirements/output-migration.md`,
`research/ordinary-output-handoff-design.md`,
`research/output-migration-implementation.md`, and
`reviews/output-migration-coordinator-r1.md`. Its production operation requires
an inactive accepted donor, complete separate formal scope reviews and final
verification, both established locks, exact source/dependency identities and
ordinary outputs described by real Lake traces. It copies and verifies before
retirement. Its approval is not an approval of arbitrary output copying from
an active build.

Pinned `scripts/lake_integrity.py` reads each real trace in
`expected_artifacts`, requires the supported trace schema and artifact
descriptions, and checks the described files. A fresh direct-Lean compilation
does not generate those Lake scheduling traces. Fresh output bytes must never
be described as ordinary Lake groups that passed this guard. Do not synthesize
traces, descriptors or sidecars to make them appear eligible for that helper.

Pinned `scripts/check.py` has a further lifecycle constraint:

1. `compile_modules` launches the real compiler with `lean -o <private-output>`
   for each project module. Its completion log line is emitted after the
   subprocess returns; dependent jobs are released only on successful results.
2. The fresh route compiles the project closure, then separately compiles
   `ProofAudit.lean` to `ProofAudit.olean`, executing the real audit.
3. The `TemporaryDirectory` context deletes the entire fresh output directory.
4. Only afterward does the checker recheck candidate/compiler identities and
   save `.lake/verification.json`, then report terminal success.

There is consequently no stock **after-success, before-cleanup** capture hook.
Changing cleanup, the controller, compiler or active invocation would alter
the frozen validation inputs and is outside this proposal. A contemporaneous
copy can only be quarantined evidence until the actual terminal success and
after-input identity checks are supplied.

The unchanged `scripts/test-proof-audit.py` consumes the Applications directory
under `.lake/build/lib/lean`, imports the actual `ProofAudit` module, creates its
own temporary probe modules, and executes four positive/negative cases. It
does not inspect project Lake traces or request a project rebuild. `lake env`
supplies its search environment. The proposed private fixture directory could
satisfy that path contract with accurately described fresh artifacts; it must
not be offered to an incremental candidate build as a validated Lake cache.

## Conditions for a distinct fixture-only route

These are requirements for a possible implementation, not assertions that the
operation already exists or has been approved:

- Pin one root-owned run ID, exact candidate and source tree, native runtime,
  dependency/configuration identities, and the unambiguously owned private
  fresh directory. Ambiguous directory ownership or multiple candidate
  generations must stop capture; do not select an arbitrary newest directory.
- Observe completed module events from the actual stock run. Capture only
  regular files from the corresponding completed module generation, including
  every emitted module part required for import. Preserve exact paths, sizes
  and SHA256 identities, with stable source-file metadata/content before and
  after copying. Retain incomplete or failed copies as diagnosed quarantine;
  never overwrite an earlier generation or copy into the active checkout.
- Keep the stock run's source, dependencies, runtime, controller, private
  outputs, cleanup and acceptance records untouched. An observer is not an
  additional compiler. It must not pretend to acquire an exclusive full lock
  held by the active owner or bypass the ordinary migration helper's refusal.
- Bound space use and retain the established recovery reserve. Copying a fresh
  generation adds disk usage; it has no retirement allowance from the approved
  ordinary-output migration. No source output deletion or filesystem-link
  substitution is needed or justified.
- Do not consume quarantined data until the exact originating full run has
  genuinely completed successfully, all required source/audit coverage is
  established, its before/after inputs match and its saved verification record
  is retained. A failed or interrupted run leaves the quarantine unvalidated.
- Check completeness against the exact candidate's integrated module/import
  inventory, not the number of files or Lake jobs. Bind all copied output
  groups to that one run and their completed modules. Preserve the provenance
  manifest, complete raw log and successful run record separately.
- Materialize a separate private exact-candidate fixture with unchanged
  committed sources and unchanged test script, clean pinned dependency sources,
  the same approved native runtime, and its own private project input directory.
  Stage only the captured matching generation in the path required by the
  stock suite. Copy no `.lake/verification.json`, review result or acceptance
  marker. Record that these are **fresh compiler outputs staged as fixture
  inputs**, with no claim of ordinary Lake-trace validation.
- Execute the unchanged regression command only after that protocol's evidence
  is ready. Preserve actual runtime/source/artifact identities and all four
  real case outcomes. Do not use a successful fixture result as formal donor
  acceptance or as permission to feed this generation into normal Lake reuse.

The `ProofAudit.olean` output is produced near stock cleanup, so a passive
observer cannot assume it will capture a complete final audit artifact. If
that artifact is unavailable but the project closure was captured completely,
the fallback within the new fixture protocol is a **genuine compilation of
only the unchanged ProofAudit module** against that exact retained closure,
after the full fresh run has passed. Record its real command, native identity,
inputs, audit result and outputs. That avoids inventing an audit artifact or
depending on a narrow cleanup race; it still does real compiler/audit work.
Missing other required output parts, inconsistent snapshots or unestablished
import completeness must remain a blocker rather than being hidden by a fake
trace or copied success record.

## Validation and approval boundary

Because this is outside the earlier accepted ordinary-output contract, do not
claim its prior review covers a new capture helper. Keep any new operational
implementation in the existing recovery loop, retain its explicit scope and
validate meaningful public filesystem/lifecycle behavior before independent
review. In particular, actual incomplete generation, changed source artifact,
failed originating run and pre-success consumption must not become successful
fixture input. Real compiler results remain distinct from disposable fixture
tests of the capture mechanics.

The prerequisite formal review can then assess the successful fresh gate,
the exact fixture provenance and actual stock regression results alongside
the unchanged other required evidence. It must not misstate the provenance as
ordinary-output integrity verification or drop the separate final stock check.
The accepted donor migration helper and its existing receipt/retirement rules
remain unchanged and outside this proposed fixture-only operation.

Root reported genuine Elan 4.2.4 setup and exact selected Lean 4.35.0 probes in
`environment/elan-4.2.4-provenance/setup.json`. That resolves the separate setup
question for the checker suite once root supplies its actual execution; it
does not validate this output-capture idea or any regression suite by itself.
