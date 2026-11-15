# Compacted-region mmap advice: static assessment

Date: 2026-11-03 UTC. This is source analysis and a bounded future-experiment
hypothesis, not a production adapter, a performance result, or formal
candidate approval. No `madvise` probe, interposition, Lean invocation, or
build was performed for this assessment.

## Existing pinned Lean behavior

The exact Lean commit is
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (Lean 4.35.0).
Both complete upstream files were fetched read-only and their hashes matched
the earlier preserved source assessment:

| Source | Lines | SHA-256 |
| --- | ---: | --- |
| [`src/library/module.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/library/module.cpp) | 648 | `9b85a9a7610e73f240282fe288ad81c8b160fc975caa80bd5b13ddacdd6012a8` |
| [`src/runtime/compact.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/compact.cpp) | 688 | `d2243af4a8d6d774d47cdf781cb15de56e257111b9c84dcd028110c601e75bae` |

Neither file contains a `madvise`, `fadvise`, `MADV_*`, `POSIX_FADV_*`,
`MAP_POPULATE`, `MAP_NONBLOCK`, or readahead call/setting. This absence claim
is scoped to those complete files; it is not a claim about all kernel or
filesystem behavior.

The loader at `module.cpp` lines 524–540 uses a private writable file mapping
at the saved base address, with `MAP_FIXED_NOREPLACE` on Linux. It contains no
explicit random-access advice. The successful preferred-address fast path
in `compact.cpp` lines 643–656 avoids the structural pointer-relocation walk.

The separate one-page capability observation is preserved in
`mmap-capability-probe-20261103/`. It completed with actual exit 0, established
successful exact-address mapping with the pinned flags, and observed
`EEXIST` on collision with unchanged private memory. That closes the
unsupported-flag hypothesis for that isolated observation. It neither
applied mmap advice nor measured actual Lean mapping success rates. No
extension of that runtime experiment was made.

## What MADV_RANDOM would and would not change

[Linux man-pages, `madvise(2)`](https://man7.org/linux/man-pages/man2/madvise.2.html)
classifies `MADV_RANDOM` among conventional advice values that preserve
application semantics. It describes a random-access expectation for the
selected mapped range. The start address must be page-aligned and the size
is rounded to whole pages. Success returns zero; an error returns minus one
with `errno`. Documented errors include invalid/alignment arguments,
unmapped ranges, and unavailable kernel resources. Advice can affect mapped
portions of a partly unmapped range before the syscall reports failure.
Availability also depends on the kernel's advice-syscall configuration.

The official tagged Linux v6.12 sources provide a concrete implementation
example:

- [`mm/madvise.c`](https://raw.githubusercontent.com/torvalds/linux/v6.12/mm/madvise.c),
  lines 1050–1058, sets `VM_RAND_READ` and clears `VM_SEQ_READ` for
  `MADV_RANDOM`. Range handling can change or split VMA metadata.
- [`mm/filemap.c`](https://raw.githubusercontent.com/torvalds/linux/v6.12/mm/filemap.c),
  lines 3170–3172 and 3220–3222, bypasses the ordinary synchronous and
  asynchronous mmap readahead paths when that flag is set.
- The hugepage branch at `filemap.c` lines 3152–3166 precedes the ordinary
  early return. It can still obtain a PMD-sized folio; random advice suppresses
  fetching the extra second folio. Therefore the claim that it disables all
  readahead or all larger reads would be too strong.

Linux v6.12 is an illustrative tagged implementation, not a measured version
of this host. Those kernel sources were read-only corroboration by the
`fresh_scheduler` agent; source hashes were not captured for them. Kernel
versions and filesystem-specific fault paths can differ.

Conventional random advice does not rewrite the file, change the mapped
address, or deliberately replace the region with an anonymous copy. Applied
to an otherwise unchanged successful mapping, it therefore preserves the
conditions for Lean's preferred-address relocation fast path. This is a
narrower resource experiment than forcing malloc/read fallback. It supplies
no guarantee of fewer faults, lower memory consumption, less IO, or shorter
runtime. Already-resident data may show no change, and suppressing useful
read-ahead can make sequential accesses slower.

## Bounded experimental interpretation

A tightly scoped advisory-only comparison is technically sensible as a
future hypothesis. It should retain the original mapping's address,
protection, flags, bytes, and return behavior and apply only `MADV_RANDOM`
to the verified eligible successful compacted-region mapping. Unrelated
mappings and the existing fallback path should keep their ordinary
behavior. Advice failure is a recorded unsupported/failed optimization,
not a reason to substitute a different mapping or skip validation.

Any mechanism that applies the hint still needs correct scope and error
handling. A hint's semantic contract does not establish the correctness of
an unimplemented adapter. This review supplies no implementation and makes
no claim that the accepted native adapter evidence already covers one.

The earlier Squares sample recorded 71,899,496 input-block-counter units and
144,730 major faults. These are whole-process observations, including other
loading and IO, and are not a measurement of wasted compacted-region
readahead. Their ratio cannot by itself establish causation, a byte count,
or an expected improvement. A future bounded result would need to preserve
the original output/validation interpretation and report the actual
syscall outcome and resource observations. Overlapping work and uncontrolled
cache state would limit any causal timing comparison.

No further experiment is recommended as part of the completed flag-capability
task. The ongoing fresh4 run and production helper/wrappers remain unchanged.
