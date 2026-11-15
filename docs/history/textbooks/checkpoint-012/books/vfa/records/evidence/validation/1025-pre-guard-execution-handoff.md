# Pre-guard preservation: static execution handoff

This records the completed source-only preparation for the already approved
[pre-guard preservation plan](1025-pre-guard-preservation-plan.json). It is a
prospective execution handoff, not a new utility, review, acceptance gate or
successful diagnostic. No compiled output was inspected and no invocation below
was run during preparation. Fresh2 remains outside this task's control.

Root must first establish the fresh-completion prerequisite under the existing
workflow. This handoff does not resolve fresh2's process-handle loss or actual
outcome. An unavailable raw return must remain explicitly unavailable.

## Static source identities and references

The formal candidate is
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.

| Static source | SHA256 | Existing identity record |
| --- | --- | --- |
| [scripts/lake_integrity.py](../../conaled/scripts/lake_integrity.py) | `293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f` | [Approved preservation plan](1025-pre-guard-preservation-plan.json) |
| [scripts/check.py](../../conaled/scripts/check.py) | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` | [Existing audit prerequisite investigation](1002-audit-regression-prerequisite.md) |

These exact hashes are reused from the existing records for the unchanged
checker sources; this documentation save does not perform a new source hash or
inspection. Preparation also read the static [check.sh](../../conaled/check.sh)
wrapper, [lake-output-hashes.lean](../../conaled/scripts/lake-output-hashes.lean),
the [incident runbook](../../conaled/docs/agents/lake-integrity-incidents.md),
and the [acceptance checklist](1002-acceptance-evidence-checklist.json).

## Minimal non-repairing invocation

Run from the isolated checkout:

```text
/workspace/scratch/0c54f2db1fdf/vfa-validation
```

Use the established pinned Nix environment, including the existing Nix PATH
setup and this `NIX_CONFIG` value:

```text
build-users-group =
experimental-features = nix-command flakes
```

Keep `LEAN_NUM_THREADS=1`, remove caller `LEAN_PATH` and `LEAN`, and set
`LAKE_ARTIFACT_CACHE=false`. The inspector calls bare `lean --run`, so `lean`
must resolve through the pinned development environment. It does not need a
Lake build.

Supply this exact one-shot body as one argument to `python3 -B -c`, using the
existing approved capture workflow. No utility file is needed. Using `-c`
also avoids depending on stdin, which the recorder closes.

```python
import json
import os
from pathlib import Path
import sys

root = Path.cwd().resolve()
assert root == Path("/workspace/scratch/0c54f2db1fdf/vfa-validation")
sys.path.insert(0, str(root / "scripts"))

from lake_integrity import validate_layout, inspect_outputs

env = os.environ.copy()
env.pop("LEAN_PATH", None)
env.pop("LEAN", None)
env["LEAN_NUM_THREADS"] = "1"
env["LAKE_ARTIFACT_CACHE"] = "false"

sources = list(root.glob("*.lean"))
for directory in ("SquareKit", "Applications", "Examples"):
    sources.extend((root / directory).rglob("*.lean"))

normal_targets = sorted({
    ".".join(path.relative_to(root).with_suffix("").parts)
    for path in sources
} - {"ProofAudit"})

print(json.dumps({
    "phase": "inventory",
    "root": str(root),
    "normal_targets": normal_targets,
    "target_count": len(normal_targets),
}), flush=True)

validate_layout(root)
bad, artifact_count = inspect_outputs(root, normal_targets, env)

print(json.dumps({
    "phase": "inspection_completed",
    "bad_modules": bad,
    "hashed_artifact_count": artifact_count,
}), flush=True)
```

The enclosing argument vector is:

```text
nix develop --command python3 -B -c <the exact body above as one argv element>
```

Do not invoke `check.main()` to obtain its inventory: starting another check
removes the current verification record. Do not invoke the repairing guard
before preservation. The invocation above calls only `validate_layout` and
`inspect_outputs`; importing their module does not run the checker.

### Target inventory

`check.py` inventories root `.lean` files and recursively inventories
`SquareKit`, `Applications` and `Examples`. It constructs a dependency order,
checks public coverage, visits `ProofAudit`, then excludes only `ProofAudit`
from normal build targets.

After successful coverage on the stable, unchanged candidate, the set above is
the same normal target set, including inventoried audit dependencies. The
inspector checks families independently and does not need the checker's
topological ordering. Do not substitute a public-import-only closure, omit
audit dependencies, include archived/staging sources or hard-code a count.

### Result serialization and limits

The returned pair is:

```text
(dict[str, str] mapping module names to discrepancy reasons,
 number of artifact paths hashed)
```

Both values serialize directly to JSON. The count is artifact count, not
module count. A nonempty discrepancy dictionary is a completed diagnostic,
not an API exception: the one-shot process can exit zero while reporting
discrepancies. Preserve and classify them; this exit is not validation success.

Where eligible artifact entries exist, the inspector creates a temporary path
manifest and invokes the pinned `lake-output-hashes.lean` with `lean --run`.
This is non-repairing but is not a pure metadata inspection. `-B` avoids Python
bytecode-cache writes; it does not eliminate the inspector's temporary manifest.

The helper uses the pinned Lake binary-hash implementation and does not trust
replaceable `.hash` sidecars. Its successful raw hash array is consumed
internally. The public API returns neither that array nor an independent helper
exit-status field. A helper failure raises an exception containing its output;
do not invent a numeric helper return that the API did not expose.

The inspector generally reports the first relevant reason per module.
Missing/malformed trace evidence can prevent checking further members of that
family. Exceptions, malformed helper results, interruption, timeout or absence
of the final `inspection_completed` record mean an incomplete/failed diagnostic,
never an empty discrepancy set. There is no built-in helper timeout.

These APIs do not perform all candidate/dependency/compiler checks,
authenticate trace provenance, inspect external dependency-cache integrity or
establish the absence of writers. Inspection does not freeze inputs.

## Exact family and provenance locations

For module `A.B.C`, let `stem = A/B/C`.

| Member | Location relative to the isolated checkout |
| --- | --- |
| `olean`, `olean.server`, `olean.private`, `ilean`, `ir`, `ir.sig`, `trace` | `.lake/build/lib/lean/<stem>.<extension>` |
| `c`, `bc`, `ltar` | `.lake/build/ir/<stem>.<extension>` |
| Corresponding sidecars | Each filename above plus `.hash` |
| Available setup provenance | `.lake/build/ir/<stem>.setup.json`, plus any available corresponding sidecar or command-recorded alternative |

Enumerate these paths and preserve them when present; do not assume existence.
Setup files are outside the guard's deletion set but remain relevant evidence.
`artifact_path(root, name, extension)` implements the artifact mapping. The
guard's constants are:

```python
LIB_EXTENSIONS = (
    "olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig"
)
IR_EXTENSIONS = ("c", "bc", "ltar")
```

Add `trace` and each corresponding `.hash` when enumerating the preservation
family. Retain raw traces and sidecars as observed; do not normalize, repair or
replace their values while collecting evidence.

## Capture sequence after the completion prerequisite

1. Preserve the fresh outcome first. Retain actual available outcome evidence
   and its matching `mode: fresh` verification record before another candidate
   check removes that record. Never replace an unavailable raw return with an
   inferred zero or restore an old success record to conceal a later failure.

2. Establish stable, idle isolated inputs, then run the non-repairing invocation.
   Retain its exact command, target inventory, complete diagnostic output,
   actual available process outcome and any exception/interruption evidence.

3. Classify discrepancies against history. Never-built absences and documented
   ENOSPC partials can be ordinary recovery cases. Unexpected mismatches or
   missing/malformed evidence for previously completed modules require incident
   assessment; shared error wording does not establish a common cause.

4. Preserve all four known families even if currently consistent, plus every
   newly suspect family:

   - `Applications.Resources.BoundedSummary`
   - `Examples.BoundedSummary`
   - `Applications.Sequences.ByteBuffer`
   - `Examples.ByteBuffer`

   Copy surviving artifact parts, raw traces, corresponding sidecars and
   available setup/command provenance outside managed caches. Record missing
   members, source and copy identities/digests, and observed changes during
   capture. Keep the exact candidate, compiler, dependency and command context.
   Current or regenerated bytes cannot reconstruct the four original
   pre-invalidation artifacts that are no longer available.

5. Durably preserve newly material incident evidence before repair. Keep it
   distinct from the accepted installable cache companion, which intentionally
   omits bad families. Copying and inspection are not an atomic snapshot;
   stable-input assumptions and any observed changes remain explicit.

6. Proceed only when preservation and incident disposition permit the unchanged
   guarded incremental check. Preserve its separate outcome and verification
   record. The managed `+ProofAudit`, required regression, both original reviewer
   assessments and final candidate verification remain separate gates. If the
   managed audit build unexpectedly rebuilds project dependencies, retain that
   event and re-establish corresponding guard evidence before relying on those
   dependencies for the regression, as already required.

This handoff changes no acceptance condition and makes no current cache-validity
or root-cause claim. It is frozen documentation of the completed preparation.
