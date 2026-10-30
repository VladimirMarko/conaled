# Lake integrity incidents

Use `./check.sh` for routine integrated acceptance and the candidate commands
in [README.md](../../README.md#build-and-audit) for committed acceptance.
Focused Lake builds remain useful during development but bypass the guard.

This is temporary guidance while [#272](https://github.com/VladimirMarko/conaled/issues/272)
is open. Check its status first; if closed, follow its resolution and retire any
remaining active pointers rather than continuing incident reporting. Its body and comments own the incident history, record format, and repeat-alert
procedure, including relay from sub-agents to the top-level agent. Read that
issue before diagnosing a suspected recurrence. #222 continues to own the
stronger reuse contract; recovering one incident does not complete it.

## Classify the output

- `Integrity guard: rebuilding ...` means the pre-build check invalidated that
  module's outputs and Lake will rebuild it in the same invocation. Let the
  command finish. Missing outputs/traces on a new checkout or after an
  intentional clean are normal; they do not need an incident report.
- `output mismatch`, unexpected missing/malformed evidence in previously built
  modules, or repeated invalidation of unchanged modules warrants an incident
  record even if automatic recovery succeeds.
- `Integrity guard rejected build outputs` means the post-build check failed
  before the audit. `Integrity hashing failed`, invalid hash results, or an
  unsupported layout/cache configuration also stop verification. Retain the
  diagnostic and investigate the stated failure; they do not all mean corrupt
  output bytes.
- Unknown declarations or other errors from direct Lake/editor use are only
  symptoms. Compare source, artifact and build evidence before calling them a
  cache defect. Ordinary source errors stay with their development task.

## Investigate and recover

1. Save the command, exit status and relevant output. Before further manual
   cleanup, preserve surviving affected traces, sidecars and artifacts locally,
   together with the candidate and toolchain identities. Automatic pre-build
   invalidation may already have removed the mismatched files: state that
   limitation and use the recorded diagnostic, not an invented reconstruction.
2. Consult #272 for matching evidence. For a known recurrence, follow its alert
   and recording procedure promptly, including when recovery succeeded. Match
   identities and circumstances where available; shared error wording alone
   is insufficient. Collect evidence from this occurrence even when it matches
   a prior one. Keep investigating across occurrences until the evidence gives
   a clear answer to the relevant question; state that answer and its limits
   before narrowing the investigation. A known reuse mechanism does not settle
   how inconsistent artifacts were created or propagated. Alerts supplement
   this evidence gathering rather than replace it.
3. Check for concurrent writers or copied project outputs. Coordinate a stable,
   isolated checkout before retrying. For hashing/layout/schema failures,
   inspect the named tool or adapter/configuration incompatibility and correct
   it through the normal implementation and review workflow. Preserve the
   guard: bypassing it or changing its expected hashes is not a repair.
4. After correcting the cause or stabilizing the checkout, rerun the guarded
   command. For committed acceptance, use `./check.sh --candidate HEAD`, then
   `./check.sh --verify-candidate HEAD`. If rejection or unexplained invalidation
   recurs, record the unresolved evidence and alert the coordinating agent or
   owner rather than repeatedly cleaning and retrying.
5. Use `./check.sh --fresh` when stale outputs are suspected, as required by the
   README; include `--candidate HEAD` when validating a committed candidate.
   Record its result separately. Fresh mode bypasses project outputs and leaves
   the incremental cache unrepaired. Claim incremental recovery only after a
   guarded incremental run passes; fresh success alone does not close the
   incident. Verification records describe their recorded mode, not both modes.
6. Complete the incident comment in #272 with recovery results, remaining
   uncertainty and owner-alert status. For a delegated investigation, supply the
   evidence to the coordinator so it can maintain one comment and relay alerts.
   Keep the tracker open after individual recoveries while the underlying
   problem remains unresolved. Once fixed or otherwise handled, complete its
   retirement checklist: remove the temporary agent trigger, reporting/alert
   duties and active pointers, retain useful historical evidence, and close
   the tracker. Ordinary acceptance and still-needed recovery guidance remain.

Publish concise redacted diagnostics and hashes. Keep raw session logs and
binary artifacts local. If tracker access or owner relay is unavailable, retain
an explicit pending action instead of claiming that a comment or alert was sent.
