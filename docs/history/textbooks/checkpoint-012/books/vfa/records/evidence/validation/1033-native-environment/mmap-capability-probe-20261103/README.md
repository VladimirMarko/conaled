# One-page MAP_FIXED_NOREPLACE capability observation

Executed once on 2026-11-03 at 17:49:05 UTC. Actual child return code: **0**.
Captured wall time: **0.04939577599725453 seconds**. The result closes the
unsupported-flag hypothesis for this isolated capability test. It does not
measure the mapping success rate, preferred-address collisions, import
behavior, or performance of an actual Lean process.

The self-contained `probe.py` and its exact child argv, cwd, limits, addresses,
errno values, cleanup results, and interpretation are preserved in
`execution.json`. The outer invocation was:

```text
python3 -B /workspace/scratch/83865511e965/recovery/conaled-vfa-checkpoint-035-returned-archive-preservation/work-state/validation/1033-native-environment/mmap-capability-probe-20261103/probe.py
```

The probe created only its own new 4,096-byte mapped file. It opened that file
with `O_RDONLY`, matching the pinned Lean loader, and requested
`PROT_READ | PROT_WRITE` with a private mapping at offset zero.

| Operation | Result | errno |
| --- | --- | --- |
| Ordinary `MAP_PRIVATE` file map | `0x7fa9a3dee000` | 0 |
| Unmap that page | 0 | 0 |
| Map at the freshly freed address with `MAP_PRIVATE | MAP_FIXED_NOREPLACE` (`0x100002`) | Exact requested address `0x7fa9a3dee000` | 0 |
| Repeat those mapping flags against the occupied page | `MAP_FAILED` (`0xffffffffffffffff`) | 17 / `EEXIST` |
| Final unmap | 0 | 0 |

The collision preserved both a private sentinel and the entire mapped page.
The underlying file hash remained unchanged. All explicit mappings were
unmapped; peak live explicit mappings was one 4,096-byte page. No `LD_PRELOAD`
was present in the probe process.

The source imposed a 15-second parent timeout, 5-second child CPU limit,
256-MiB address-space limit, 64-KiB maximum individual output-file size,
64-KiB page-size cap, and at most two live explicit mappings. There was one
ordinary mapping, one preferred-address mapping, and one collision attempt;
the conditional ordinary fallback was not used. No compiler, shared runtime,
project source, dependency cache, or `/proc` interface was used. No additional
mapping experiment followed the successful result.

The flags reproduce the exact pinned loader in
[`src/library/module.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/library/module.cpp),
lines 524–540, SHA-256
`9b85a9a7610e73f240282fe288ad81c8b160fc975caa80bd5b13ddacdd6012a8`.

| Preserved file | Bytes | SHA-256 |
| --- | ---: | --- |
| `probe.py` | 11772 | `d1a811b04b9d2c27d35c159dd179d34a27ceeb4b1ae2eb6a223b4a3b0d297618` |
| `execution.json` | 4885 | `0e153ec219933d672c773b5eb42e0bc15cdcfddd7b35ae8c8bb586fa35ef2f17` |
| `stdout.log` | 3640 | `1e40ab3eaa2587818cdf6b275a3130ec10ae4b06f4aee74f85065aacbf3556ff` |
| `stderr.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `one-page.bin` | 4096 | `3aa183ba3cb7678808e5d91fa536da6203a01ec4f864f4100593669b856e9063` |

The source and captured observation were not edited after execution. This
README was added afterward. No production adapter was introduced and no
formal review or validation gate is completed by this observation.
