# Evidence layout and replay reconstruction

[cohort.json](cohort.json) and `authors/slot-N/summary.json` contain readable
per-author results, selected source lists, failures, helper names, raw-usage
provenance and file measurements. Final Lean files and rejection prose are
readable beside each summary. Slot 5's unselected ScaleDraft remains there too.
These files are historical submitted artifacts, outside library entrypoints;
no supplied theorem or author proof was edited for reporting.

[evidence-map.json](evidence-map.json) maps original paths relative to the
recorded work root to `evidence/SHA256.txt`. Each blob is the original UTF-8
file's exact bytes. Duplicate bytes share a blob; the `.txt` suffix does not
change original file identity or classify a Lean proof as prose. Every entry
records SHA-256 and byte length. Original command paths inside receipts remain
unchanged, so the evidence preserves what actually ran. Their `/tmp` paths are
historical provenance, not required live links for reading this report.

The map includes frozen submissions; every complete and failed recorder attempt
(source, context, command, start/result and output); phase releases/completions;
public and sealed release material; bootstrap metadata and selected raw usage;
coordinator setup errors; replay selection, source/derived artifact inventories,
commands, logs and origin probes; audit drivers and queue state; preparation and
accepted-source validation receipts. Source mirrors and compiled binaries are
not copied. Retained source maps and content identities tie those mirrors back
to accepted Git inputs and the included fixture/submission bytes. Original
private rollout transcripts were never exported.

## Check and materialize receipts

From this directory, the following standard-library snippet verifies all blob
identities and reconstructs the relative evidence paths into a new external
directory. Pick a new destination; existing files are refused. Reconstruction
writes receipt bytes only and runs no recorded command.

```python
import hashlib, json
from pathlib import Path
archive = Path.cwd()
record = json.loads((archive / "evidence-map.json").read_text())
destination = Path("/absolute/new/evidence-copy")
destination.mkdir(exist_ok=False)
for name, entry in record["entries"].items():
    relative = Path(name)
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (archive / entry["blob"]).read_bytes()
    assert len(data) == entry["bytes"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"]
    target = destination / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("xb") as output:
        output.write(data)
```

Every mapped file/hash and every readable author source was checked during
report capture. The exact candidate's validation receipt is supplied to the
independent reviewers outside the source diff. Hashes establish byte
correspondence, not authenticity against an unrestricted writer or proof that
unobserved files never influenced a process.

## Reconstruct the Lean replay inputs

Use the pinned repository development shell and source commit
`1d9d4357f93b91a0f01ddef3103a7e4b72e5dc0e`, its `lean-toolchain`, Lake manifest
and dependency revisions. Rebuild dependencies into private outputs when the
recorded binary inputs are unavailable. Such a rebuild is a new validation run,
not reuse of the historical output hashes. Keep every run's new receipt distinct.

Recreate the complete filesystem source mirror using that accepted repository
and the ten fixture mappings retained under `423-trial-stage-round3/source-map.json`.
The committed fixture sources and private references live one directory above
this report; phase baseline Repair is additionally retained in sealed and
completion evidence. Preserve the production `ProofAudit.lean` and
`scripts/project_sources.py`, the full source inventory, and the pinned config.
Do not narrow the mirror to imported author modules or replace the production
auditor with a proof-only shortcut. Source correspondence receipts reconcile
the stage's historical candidate label with the accepted source used at launch.

For each slot, `replay-*/sources.json` maps the included exact author bytes into
its `Examples.ConversionTrial.Author.*` module files. Use only the final selected
set. Slot 2's failed `replay-01` remains historical; `replay-02` is the successful
input set. Slot 5's ScaleDraft is historical, not an extra selected module.
Copy exact authored files; do not rename declarations to hide helper overlap.
The baseline repair is replayed against the full accepted fixture with unchanged
baseline declarations, while the original restricted-release phase receipts
remain separate evidence.

Recompile each selected module independently into a private output root using
the recorded command structure, actual source-root path and pinned Lean. Make
all required Examples outputs available in the first applicable output root;
slot 2's retained setup failure demonstrates why a later root alone was
insufficient. Native policy commands, environment receipts, preparation scripts
and focused results identify imports and inputs. Rebase historical absolute
paths explicitly to the recreated roots; retain both the original argv and
new argv rather than rewriting historical receipts.

Finally reproduce every required audit driver/import context using the retained
`Audit*.lean`, origin probe sources and `audit-queue.json` commands. Slot 2 has
two contexts, with ScaleProof and HeldOutProof first in turn. Slot 5 has six,
with Composition, Context, Substitution, HeldOutDraft, Before and After first in
turn. Each imports the full selected submission; a successful combined import
alone is not exhaustive ownership evidence. Other slots use one full context.
Require zero exit, full inventoried module coverage, expected original helper
owners and only the permitted `propext`, `Classical.choice`, `Quot.sound` axiom
union. Root serializes actual audit execution; this report does not launch it.

Historical receipts marked pending remain pending history even after a later
receipt succeeds. A current gate must cite the actual completed result and
matching identities. Neither queued commands nor captured hashes certify that
an audit ran. The full-audit gate passed; independent report review and publication require
separate exact-candidate acceptance recorded on #423.
[audit-completion.json](audit-completion.json) identifies every completed context.
The evidence map's `completion/` namespace records later bytes without replacing
original pending receipts. The queue-interruption archive preserves pre-restart
state, exact scripts and input hashes; its cause remains unknown.
