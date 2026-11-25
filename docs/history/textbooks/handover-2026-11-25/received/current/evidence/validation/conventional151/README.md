# Exact completed-run receipt capsules152

The one literal `c.start.json` contains the3870-entry current binding map.
Seven projected receipts preserve every other field and top-level key order:
prereqs/a/b starts and all four results. The c result refers to the anchor map
twice. Each projection omits exactly the listed keys, preserving anchor order.
Actual before/after maps were compared to the projection before writing.

All eight original start/result JSON byte strings were reconstructed exactly
with UTF-8 JSON, indent2, original key order, ensure_ascii=True and one final LF.
The four child receipts and four complete logs remain literal, as does c.start.
Original full-receipt descriptors are not aliases for capsule bytes.

Canonical routes are under current/evidence/validation/conventional151/:

- c.start.json — literal existing current start receipt;
- run-capsules.json and reconstruct_run_capsules.py — these new small files;
- prereqs/a/b/c.child-exit.json and prereqs/a/b/c.log — literal existing files.

Verify from a complete packet without materializing large maps:

```sh
python3 -B PACKET/current/evidence/validation/conventional151/reconstruct_run_capsules.py \
  PACKET/current/evidence/validation/conventional151/run-capsules.json --root PACKET
```

The local check uses --path-map LOCAL_PATH_MAP.json to read the original files
in place. That map need not be retained after canonical packet assembly.
An optional --output FRESH_DIRECTORY recreates all eight original start/result
files, but was not used for the in-memory verification. The script executes no
receipt command, Lean invocation, build or project write.

Preserved outcomes are prereqs0, a1, b1, c0. Exact reconstruction establishes
receipt identity, not a new mathematical, ordinary-module or acceptance result.
