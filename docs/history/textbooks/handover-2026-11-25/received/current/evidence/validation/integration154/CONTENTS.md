# Validation154 receipt reconstruction

Both completed native runs recorded actual exit0 and equal, nonnull before/after
source bindings: owners154 has1539 bindings; query154 has4056. The preparer and
the separate reconstruction helper both completed with actual exit0. All four
original start/result files reconstruct byte for byte, including JSON field and
map order, indentation and final newline.

The durable set contains one literal `query.start.json`, `run-capsules.json`,
the current `reconstruct_run_capsules.py`, both literal child-exit receipts and
the complete owners log. The complete query log is the existing canonical body
at `current/evidence/validation/integration153/query-b.log`: its960,006 bytes
and0644 mode match query154 exactly; SHA-256
`6e77461497967c5bcb53f3e6b6d0dc0bf55dec88076c3a01e48178d7a329ea91`.
The capsule preserves both original log descriptors and their distinct paths.

The owner map is the anchor map with exactly2517 keys omitted and no descriptor
overrides. The query projection omits nothing. Every nonmap record field is
preserved, including the actual command, timestamps, duration, exit, original
record/log paths and descriptors. Child/start/final/log agreement is checked.
No recorded command is executed by the reconstruction helper.

From a recovered packet, run the helper with the packet directory as `--root`:

```sh
python3 -B /packet/current/evidence/validation/integration154/reconstruct_run_capsules.py \
  /packet/current/evidence/validation/integration154/run-capsules.json \
  --root /packet
```

This verifies/reconstructs in memory. Optional `--output /fresh/directory`
materializes the four original JSON byte streams. Historical absolute paths
inside those streams remain literal evidence; they are not runtime dependencies.

The original four receipts total4,262,347 bytes. One1,036,160-byte anchor,
332,522-byte capsule and6065-byte helper save2,887,600 bytes, before this small
index. Sharing the exact existing query log avoids another960,006-byte copy.
Original full-file hashes identify reconstruction targets, never capsule bytes.

The current helper is a fresh4056-anchor instance of the retained153 schema;
the predecessor helper and evidence remain unchanged. Its lineage and changes
are recorded inside the capsule. Earlier failures and UNKNOWN outcomes remain
separate historical evidence and are not replaced by these two successful runs.

This package establishes exact operational evidence reconstruction. It does not
establish mathematical output reading, compiler provenance, whole validation,
independent review or acceptance. No compiler was invoked during compaction.
