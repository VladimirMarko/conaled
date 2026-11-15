# Supplementary ordinary-build-output recovery assessment

Prepared2026-11-03 by build_cache_recovery. This is a bounded read-only
operational assessment for the user's durability goal, not candidate acceptance,
a proof result, a new independent code-review loop or permission to change a
running check. Only this report was written. No compiler, hash-tool execution,
build/test, cache mutation, Git/ref/index operation, process change, external
tracker action or upload was performed by this assessment.

## Recommendation

A supplementary archive of complete ordinary output groups is reasonable, with
the private-copy validation below. Keep it separate from the source/history/
ticket checkpoint and identify it as optional recovery acceleration. It must
not contain or synthesize `.lake/verification.json`, dependency caches, or an
approval claim. Every restored candidate still requires the ordinary stock
full candidate check, exhaustive audit, exact verification record and final
verification required by its existing review loop.

The existing warmers must not be used unchanged against the active901 donor.
They check donor output hashes before copying, then compare individual copied
files with donor bytes. That is useful for their inactive-donor setting, but
it does not establish a coherent copied trace/artifact generation if a writer
runs between those operations. The unchanged integrity guard expressly does
not protect concurrent readers/writers. Validate the fixed private snapshot,
not a mutable live donor after the fact.

Read-only identity observations during this assessment:

| Donor | Exact HEAD | Clean | Saved traces observed |
| --- | --- | --- | ---: |
| import-correction-r3 |901f734161920a76f3b399a575805b9a1d31e971|yes|715|
| validation-cache-counts |3dd930c3e3989f3e5530463f3ac937a629551335|yes|116|
| validation-chapter02-r3 |99a29dcd02eb529fbefbb675e244a8c47b78cdef|yes|25|

These are trace-existence observations, not counts of independently accepted
modules or a promise that every observed trace is eligible.901 remains active;
root owns its liveness and all copying decisions.

## Minimal staging requirement

`inspect_outputs` runs `lean --run scripts/lake-output-hashes.lean` in the
supplied root. The hash script imports `Lake.Build.Trace` and calls pinned
`Lake.computeBinFileHash` on the listed output bytes, deliberately ignoring
replaceable `.hash` sidecars. It does not resolve a Lake project workspace or
read the candidate's Lean source/dependency directories. `validate_layout`
reads the candidate's `lakefile.toml` and rejects the unsupported layouts/cache
configuration documented in README.

Consequently the private stage does not need another Git worktree, a copied
source tree or duplicated dependency caches. It needs the candidate's exact
layout/tool identity files, the unchanged `scripts/lake-output-hashes.lean`,
and the selected `.lake/build` groups. Retain `lean-toolchain` so a toolchain
shim cannot select a different compiler by changing the working directory.
Use the existing pinned Nix environment and remove caller `LEAN_PATH`, as the
warmers do. Record the exact adapter/hash-script/configuration identities.
No guard source change is required.

## Concrete capture procedure

1. Record each donor's exact commit, clean source status, selected source-module
   hashes, toolchain/configuration/dependency-pin hashes and source-validation
   status. Keep a separate namespace for each donor. Do not merge same-named
   outputs from different candidates into a single apparent generation.
2. Enumerate only saved project-module traces and require the corresponding
   tracked Lean source. Use the existing supported-schema parser and fixed
   module-to-path function. Never extract arbitrary output paths from trace
   strings. Skip missing or incomplete groups without changing the donor.
   A known currently compiling module can be excluded additionally, but a PID
   snapshot alone is not a concurrency guarantee.
3. Capture exact trace bytes T0. Copy the trace's required artifact set into a
   private temporary group and retain optional sidecars only as ordinary hints.
   Source paths, trace bytes and copied bytes must be measured, not inferred
   from timestamps alone. Record content hashes and the complete artifact set.
   Re-read the source trace and relevant file identities after copying; a
   changed trace, missing file or observed changing artifact causes the whole
   attempted group to be skipped. Preserve a factual skip reason.
4. Bind the private group to the original captured T0, not a subsequently read
   trace. Close the copied files and leave that private stage unchanged. Run
   the unchanged `inspect_outputs` on the fixed staged groups. This is the
   decisive ordinary-output consistency check: each copied required artifact
   must match the output identity in the captured trace. Merely comparing
   donor and destination SHA256 one file at a time is insufficient.
5. Keep only whole consistent groups in the published archive namespace.
   Do not run `guard_outputs(..., repair=True)` on the active donor, rewrite
   traces or regenerate expected hashes to obtain agreement. If a staged
   mismatch has an actually observed concurrent-copy change, record that race
   and exclude the whole group. An unexplained mismatch in a stable group must
   be preserved and returned to root under the existing local integrity-
   incident procedure; do not label every mismatch a race or silently delete
   its evidence. Hash-tool/layout/schema failures likewise need their actual
   diagnostics rather than an assumed output-corruption cause.
6. Once the selected private outputs are stable and checked, form the manifest
   and archive. The manifest should list every member's relative path, size
   and SHA256, candidate/source/configuration identities, capture interval,
   selected and skipped modules, stock inspection result and explicit
   `acceptance:false` / `approval_copied:false`. Publish only the completed
   archive, then upload and expose it as required by the user.

The guard validates output/trace agreement, not artifact derivation from the
claimed inputs, global dependency consistency, absence of all possible races,
or malicious substitution. The SHA256 transport manifest also does not prove
Lean derivation. README's trusted-checkout and native-hash limitations remain.
A mixed set of otherwise complete cache entries may need rebuilding when Lake
rehashes its actual input/dependency graph; that is why own full validation
cannot be replaced by this operation.

## Disk-constrained execution and archive roundtrip

Root reported63Gtotal/61Gused/0generally available at planning time and owns any
reclamation decision. This assessment authorizes no deletion. The proposed
reclamation is limited to redundant locally generated checkpoint006–025 files
whose exact saved identities are established, retaining026/027 and supplied
inputs; no source or build artifact deletion is part of this assessment.

After root has made enough actual space, use one private staging set plus the
compressed archive. A second full source checkout or a second extracted copy
of every output is unnecessary. After closing the archive, stream every tar
member through SHA256 and compare with the manifest, also checking names,
member types and sizes. That establishes the archive byte roundtrip while
keeping one staged set. The separate source checkpoint already exercises Git
restoration. Do not call this streaming check a proof of successful future
compilation or of complete-candidate acceptance. Record real available space
and actual staging/archive sizes; do not rely on filesystem reserved blocks.

## Recovery instructions to preserve

Restore the source/history checkpoint first. Create a NEW clean checkout at the
selected exact archived candidate, install the recorded pinned environment and
clean pinned dependencies, and verify the candidate/configuration/source hashes.
Use a private empty project-build destination; never overwrite another running
checkout's outputs. Verify all archive members and restore only the selected
whole groups. Copy required artifacts and retained sidecars first, with each
trace last. Retain their original bytes, including historical paths in logs.

Inspected traces already contain paths from previous donor worktrees such as
validation-persistence and chapter02-ordered; that is existing provenance, not
an instruction to recreate or rewrite those paths. Whether a relocated entry
is reused is decided by stock Lake's `--no-cache --rehash build` under check.sh.
Do not promise that every archived entry will survive relocation unchanged.
Run the candidate's own stock gate after recovery and retain its new evidence;
continue the same review/finding history. Never treat a copied cache or a saved
log as a new acceptance record.

## Inspected evidence identities

- `session/validation/warm-pure-cache-counts-focused-outputs.py`: `f7212bac60878a4ab298253e881b795f09cf2d7655c566ba2b78312d5436761d`
- `session/validation/warm-import-candidate-r3-after-interruption.py`: `0b65cd0b8e18b25dbdcaec42cd2cfa85cc313263e836dafefddb4af8875df0cf`
- `import-correction-r3/scripts/lake_integrity.py`: `293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f`
- `import-correction-r3/scripts/lake-output-hashes.lean`: `fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b`
- `import-correction-r3/scripts/check.py`: `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29`
- `import-correction-r3/README.md`: `85d09c317be36c015927e948a379cdc7a11c2a8ec8ad6268cbd61708d5e11216`
- `import-correction-r3/docs/agents/lake-integrity-incidents.md`: `af2791fe85d0f559356a73899c02a61dd4012599e3ae70b203c14e27483d4b11`

This report is complete. Root retains operational execution and any required
artifact/workflow review. No additional exploration or optional check is requested.
