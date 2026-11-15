# Conditional after-fresh cache capacity action

Recorded 2026-11-04. Prospective operational assessment only. No cache removal
has occurred under this plan, and the active fresh run's inputs remain frozen.

The bounded static inventory in `1036-static-cache-closure/` reports 3,525
Mathlib modules inside the closure of all 954 integrated local modules, auxiliary
audit/hash/regression/setup roots, and all 406 cached non-Mathlib modules. It
reports 5,100 outside Mathlib modules with 76,500 generated artifact files and
3,774,812,160 allocated bytes. This is not guaranteed reclaimable space. The
entire official toolchain, every non-Mathlib artifact, source, configuration,
shared/native output and all local candidate outputs remain retained.

The independent native advisor inspected the exact fresh checker, non-repairing
collector, guarded checker, managed +ProofAudit, four regression fixtures and
final candidate-verification routes. It found no concrete request for an outside
Mathlib module. Guarded Lake commands name explicit local module targets, not
the whole Mathlib library. The audit examines the loaded environment and axiom
summaries. Native expansion is conditional on configuration; no inspected pin
enables an extra plugin/dynlib/precompilation route. ProofWidgets JS dependencies
remain covered by retaining all non-Mathlib artifacts. ImportGraph can load
invocation-supplied module names, but the examined gates/local sources do not
invoke those APIs. This is bounded source analysis, not a complete execution trace.

Lean's import machinery follows env.header.imports; following every metadata
edge regardless of flags conservatively covers its public/private/IR selection.
Before relying on the inventory, reconcile the explicit-name source-header
cross-check for all visited metadata nodes. Any unexplained mismatch, missing
source or unsupported header requires reassessment. A clean cross-check closes
that particular consistency gap; it does not prove every possible runtime path.

Root's continuation decision is conditional: after attributable full fresh
success and a separately preserved fresh verification record, remeasure available
capacity. If capacity remains insufficient for the unchanged preservation gate,
a bounded removal of exactly enumerated complete generated Mathlib families
strictly outside the cross-checked closure is supported without changing the
identified inputs to the remaining gates. The native advisor concluded that
such an action alone does not require another full fresh baseline. It changes
the installed cache inventory and must not be described as an unchanged whole
cache. No active-run deletion is authorized by this prospective decision.

Before any actual action, recheck candidate/source/dependency pins, helper and
configuration identities, source/metadata fingerprints, exact real approved
paths, the outside-module list digest, complete file families and file metadata.
Reject unexpected entries, symlinks, hardlinks, path escapes, changed identities
or overlapping retained families. Preserve the exact selected file manifest,
pre-action metadata/identities, actual action times and post-action observations.
Keep all retained families and protected inputs stable. Preserve existing incident
evidence; this plan concerns unused dependency outputs, not the historic local
BoundedSummary/ByteBuffer mismatch families.

Afterward, measure actual available bytes rather than subtracting an inventory
estimate. The unchanged collector still requires selected evidence bytes plus
64 MiB reserve and every existing completion/stability flag. All later guarded,
audit, regression, review and final-verification gates remain required. Git
identity and --verify-candidate do not authenticate dependency artifact bytes or
prove a cleanup was correct. No saved process handle establishes quiescence.
Any later source/gate/setup change requires re-evaluating this closure.

## Completed metadata/source consistency check

The frozen inventory now records all 3,931 visited dependency headers parsed,
with zero explicit import-name mismatches, zero missing sources, zero unparsed
headers and zero observed source/metadata fingerprint changes. All nine
dependency HEADs match their pins. Source-name and metadata-name edge digests
both equal `e11d745ebf7060b00b0a473922e2bc2666b47b07ae7a65024c9aa255c8ab75c4`.
Root verified the three frozen evidence-file SHA-256 values from the advisor.
The inventory digest is `5a550ae92e0787596d6b0cbcd74c638bf3bfb43b50efdd0cc6321eacc4ed25af`;
the outside list digest is `2777539c1a2f3e5b64c0af1cb2bf2b71ff90ac148adf6f3ddacb5a4e45840522`.
This resolves the specific header/metadata name-consistency gap. All timing,
current-identity, generated-family and capacity conditions above still apply.
No cache artifact has been removed under this plan.
