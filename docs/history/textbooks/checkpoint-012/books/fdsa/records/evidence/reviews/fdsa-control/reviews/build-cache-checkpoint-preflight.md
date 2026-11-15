# Optional build-state recovery artifact: Standards preflight

Date: 2026-11-02. Read-only applicability assessment, not an implementation
review, source review, mathematical acceptance, or an integrity-incident
diagnosis.

## Disposition

Preserving expensive, regenerable build state in a **separate optional recovery
artifact** is consistent with the user's explicit request to recover work after
workspace/chat loss, subject to the conditions below. It supplies recoverable
bytes, not acceptance evidence or a new guarantee of verified cache reuse.
The normal source/history/control checkpoint must remain complete without it
and continue to exclude caches under ADR 0001. This ruling does not approve an
automatic cache-transfer implementation or amend repository build policy.

**Prefer capture after the running gate and all of its output writers finish.**
An active-build subset is permissible only if its complete artifact families
are positively known to be finished and immutable throughout capture. The
read-only metadata/source inspection performed here does not establish that
condition for the current build. Therefore there is no present basis to label
an ongoing-build capture a stable, verified subset. Do not interrupt the gate,
change its output paths, create locks, run additional compiler/hash-helper
processes, or alter the checker to obtain such a subset.

## Grounding

- `AGENTS.md`, Implementation and validation, requires the applicable README
  gate and keeps read-only investigation outside a new implementation loop.
- `README.md`, Build and audit, permits reuse of normal Lake outputs but
  requires stable isolated inputs, before/after integrity guards, Lake input
  rehashing, disabled artifact-cache restoration/writes, and an exhaustive
  audit on every acceptance invocation. It prohibits sharing writable project
  build directories across active checkouts. The guard does not protect
  against concurrent replacement or authenticate trace provenance.
- `docs/adr/0001-modules-and-proof-dependencies.md` excludes caches from the
  source deliverable. The auxiliary recovery artifact must not become a
  necessary component of that deliverable or be represented as source.
- `docs/adr/0010-composition-and-proof-audit.md` rejects importing arbitrary
  cached local `.olean` files without Lake dependency tracking. Its routine
  gate still requires the full audit, and its fresh-mode obligations remain.
- `docs/research/lake-output-cache-mismatch.md` records that a mixed output set
  could survive `--rehash` alone. It says complete artifact-set transfer needs
  explicit atomicity and provenance assumptions; such transfer is not an
  already implemented policy change. The current guard checks actual output
  bytes against their original traces, rather than trusting sidecars.
- `docs/agents/lake-integrity-incidents.md` explicitly preserves affected
  traces, sidecars and binaries with identities before cleanup during an
  incident. That supports preserving raw evidence without treating it as a
  repair. This preflight reports no incident and does not trigger one.

## Capture conditions

1. **One identified origin.** Associate the artifact with the exact checkout,
   commit/tree, clean-state observations, compiler/Lake identity, pinned
   dependency revisions and build configuration. Preserve original trace
   bytes, including recorded paths. Do not relabel old candidate `1aabd51`
   outputs as repaired draft `a14977b` outputs or mix output sets from other
   worktrees. An identity manifest describes the origin; it does not prove
   that compilation produced those bytes.
2. **Complete families.** Preserve each selected module's original trace,
   trace-described output parts and associated sidecars together, retaining
   relative layout. `scripts/lake_integrity.py` recognizes module-system
   `.olean` parts, `.ilean`, C and additional trace-described outputs; an
   `.olean` alone is insufficient. Do not synthesize traces, patch expected
   hashes, copy fresh-mode private outputs into normal Lake paths, or fabricate
   missing files. An incomplete overall build may be explicitly recorded as
   partial; absent modules must be rebuilt later.
3. **Quiescence is the safer boundary.** After the check exits, confirm its
   descendant writers have finished and do not start another writer during
   capture. A successful exit makes its validation result historical
   evidence, not portable acceptance. A failed or interrupted build can still
   be preserved honestly as unvalidated recovery state, with its failure
   evidence and no claim that its outputs passed the post-build guard.
4. **An active subset needs a stronger fact than timestamps.** A log line,
   existing trace, unchanged size/mtime or two metadata reads do not prove
   that no writer will replace any member during capture. A concrete future
   capture design must establish completion and immutability for the entire
   selected set without interfering with this gate. Otherwise defer; do not
   advertise a best-effort live copy as a coherent snapshot. The full
   post-build guard and exhaustive audit are still pending while this gate
   runs.
5. **Keep recovery and acceptance separate.** Do not install a saved
   `.lake/verification.json` as current acceptance. A historical record/log
   can accompany the artifact outside the active verification-record path.
   Exclude private fresh-check directories, active temporary/lock files and
   external dependency caches from this project-output proposal. The current
   integrity guard does not validate dependency-cache integrity. Any archive
   checksum protects transfer bytes only; Lake trace hashes are
   noncryptographic and neither kind proves compilation provenance.

## Required restore boundary

No restore is authorized or performed by this preflight. A future reviewed
restore must first recover the ordinary source checkpoint, establish the exact
recorded toolchain/dependency/configuration identity, and use a new isolated
checkout with no concurrent output writers. It must not overwrite the current
gate's outputs, share a writable build directory, inject binaries through
`LEAN_PATH`, or bypass Lake tracking. Preserve original metadata rather than
editing it to make a guard pass.

Before restored outputs contribute to acceptance, run the complete normal
`./check.sh --candidate HEAD` gate in the pinned environment. That command
performs source/coverage and candidate-identity checks, the pre-build integrity
guard, `lake --no-cache --rehash build` for every project target, the post-build
guard, and the exhaustive audit. Missing or unrecognized evidence must result
in rebuilding under the existing rules. Follow with
`./check.sh --verify-candidate HEAD` immediately before acceptance. A saved
success message, archive digest or old verification record cannot replace
either command. Suspected stale output or an actual integrity failure retains
the README fresh-mode and incident-runbook requirements; unexplained repeated
failure must not be normalized by repeated cleanup.

This preserves the repository's existing trust limits. It does not establish
the stronger reuse contract tracked by #222, and no speedup or successful
reuse is promised.

## Review status and actions taken

The old Chapter 1 candidate remains
`1aabd512284fe86254278ac631eda061d311050b`; its running gate has not been accepted
by this assessment. Repair draft
`a14977b9e316cc484ffad8a470d26b15615956c0` is not compiled or approved here.
All current Chapter 1 findings and validation blockers remain open.

Only repository policy/source and existing control metadata were read. No
compiler, Lake hash helper, archive, restore, process interruption, cache edit,
candidate edit, checker change or incident creation was performed. This
outside-source report is the sole write made for the preflight.
