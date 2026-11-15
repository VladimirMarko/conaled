# Required proof-audit regression prerequisite

Read-only finding, 2026-11-02, current candidate de575a8. No compiler/build was
started and no project source, configuration, dependency or cache was changed
by this investigation.

The unchanged scripts/check.py builds explicit targets excluding ProofAudit,
then runs `lake env lean ProofAudit.lean` without an output flag so the exhaustive
audit executes on every gate invocation. This intentionally does not create an
olean behind Lake's back. At inspection, neither main nor isolated checkout had
`.lake/build/lib/lean/ProofAudit.olean`.

The required scripts/test-proof-audit.py compiles four separate temporary
fixtures, and each audit file contains `import ProofAudit` followed by a new
`#audit_project_axioms` invocation. It therefore requires the managed compiled
ProofAudit target to exist. README prescribes the regression after lake build;
the existing library configuration includes ProofAudit in its module globs.
A successful check.sh run alone does not supply this import artifact on the
current cold project build.

After actual success of the unchanged full candidate gate, preserve its
matching verification record first. Once no auxiliary compiler is running,
run the normal focused target in the same stable isolated pinned checkout:

```sh
LEAN_NUM_THREADS=1 LAKE_ARTIFACT_CACHE=false nix develop --command lake --no-cache --rehash build +ProofAudit
```

Record its exact command, candidate identity, log and independent return code.
Do not copy a hand-generated artifact into a Lake cache. If the target fails,
retain that failure and resolve it before the regression; no gate is waived.
Then execute the unchanged required regression:

```sh
LEAN_NUM_THREADS=1 nix develop --command lake env python3 scripts/test-proof-audit.py
```

Its four fixtures cover harmless unused external axioms, private transitive
forbidden axioms, a private admission, and unsafe source declarations. Preserve
actual fixture outcomes, logs and return code. The final reviewer evidence
assessment and `./check.sh --verify-candidate HEAD` remain required after these
steps. This prerequisite is not a new source/tooling change or a fresh-mode
trigger, and does not replace any full build, audit, regression or review.

Inspected source SHA-256 values:

- scripts/check.py: 80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29
- scripts/test-proof-audit.py: 72e8f1c06ad1ca427b6b2edb914cbf4c36b028a381a205be047f5792fcb1f839
- ProofAudit.lean: 8099f95ca5886ced6b0f3be7793dce5e348a4a3a855732549446c645fb3fe6fd

These are current read-only identities, not successful validation evidence.
