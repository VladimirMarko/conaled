# Source basis and scope for the experimental mmap adapter

The exact behavioral contract is the parent-owned
`work-state/specs/1035-mmap-random-experiment.md`. This is a prototype for a
bounded experiment, with no production or formal approval. The source forwards
the Linux x86_64 LP64 `mmap` boundary and conditionally issues conventional
`MADV_RANDOM` advice; it does not emulate mapping contents or force fallback.

## Primary sources

The pinned Lean loader, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
[`src/library/module.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/library/module.cpp),
lines 524–540, supplies the matched mapping shape. Its SHA-256 is
`9b85a9a7610e73f240282fe288ad81c8b160fc975caa80bd5b13ddacdd6012a8`.
The earlier complete static advice assessment is retained at
`../1033-native-environment/mmap-advice-static-assessment.md`.

The current process reports `glibc 2.39` through `os.confstr`, and the recorded
compiler is Ubuntu GCC 13.3.0. The following official versioned sources were
independently inspected by the `fresh_scheduler` agent:

| Source | SHA-256 |
| --- | --- |
| [glibc 2.39 mmap64.c](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/sysdeps/unix/sysv/linux/mmap64.c) | `8d7fce267d736bcd5a471b3875741a6abbf111a0a4c3b0a0c06a3cf64aa52706` |
| [glibc 2.39 mmap_internal.h](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/sysdeps/unix/sysv/linux/mmap_internal.h) | `c1cc0b13218e9a58f34955f540f3bb9cf71f0eb99a61ff5a8722e5cf92383268` |
| [glibc 2.39 x86_64 syscall.S](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/sysdeps/unix/sysv/linux/x86_64/syscall.S) | `fcf71a0976cad540e5af2a863907b6990a6a351689e753614821cf69b4858dd3` |
| [glibc 2.39 x86_64 sysdep.h](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/sysdeps/unix/sysv/linux/x86_64/sysdep.h) | `1177f6a3c84edef6b83bdac3f49c51dbefcc4360a8cb7deefd46c2dd5f0d6647` |
| [Linux v6.12 x86_64 syscall entry](https://raw.githubusercontent.com/torvalds/linux/v6.12/arch/x86/kernel/sys_x86_64.c) | `2aa7fb47d27b772e4eecb76b3d9cb4a55844425ace1f4b6d5bda814b5acf49d5` |

On this ABI, glibc aliases `mmap` to its 64-bit-offset implementation. It
rejects a nonzero low-12-bit byte-offset remainder before issuing a syscall;
the prototype preserves that check. The byte offset is forwarded unchanged,
not shifted into page units. Libc's `syscall` function converts kernel errors
to the expected minus-one/errno convention. The prototype retains that result
and captures its errno immediately.

Linux v6.12 is a tagged explanatory kernel source, not an observed host kernel
version. The source assessment establishes the ordinary LP64 mapping argument
path, not a universal syscall-register equivalence claim for arbitrary ABIs.

[Linux man-pages madvise(2)](https://man7.org/linux/man-pages/man2/madvise.2.html)
describes conventional random advice as preserving application semantics.
The hint's contract does not validate an adapter or establish a speedup. The
prototype preserves the successful mapping even if advice fails, records the
advice outcome, and restores mmap's original errno.

## Deliberate limits

The adapter exports `mmap`; it does not intercept hidden libc aliases, direct
syscalls, or every `mmap64` caller. The official Lean shared library's exported
dependency on `mmap` was separately observed. Matching is by the exact call
shape in an explicitly identified process, not by cryptographic identification
of each mapped file.

There is no `dlsym`, lazy initialization cache, allocator, or reporting inside
the mapping path. Linker `-z now` resolves imported functions at load time.
Counters use compile-time guaranteed lock-free unsigned-long atomics. A
snapshot reads counters individually and is not a coherent transaction across
simultaneously running threads. Counters are public diagnostics, not an
independent kernel trace.

Opt-in/identity strings must remain stable during the process. The normal
mapping-ownership assumption also remains: another thread must not replace
the just-created range before the immediate advice call. No new process-wide
lock or environment mutation is introduced to address unrelated races.

Explicit diagnostics write one bounded line to the captured stderr stream on
normal exit. They are off by default, best-effort, and are not guaranteed after
signal termination or when stderr cannot accept the line. No per-mapping IO
is added. Root's bounded Lean probe must record the actual diagnostic, rather
than inferring advice from successful startup alone.

The separate `fail_madvise.c` library is only a boundary-test injector returning
`EAGAIN` for `MADV_RANDOM`. It must never be selected in a real Lean probe.
It changes no mmap behavior and permits testing the actual prototype's
advice-failure handling without relying on a host kernel failure.

Accepted helpers, startup shim, overlays, official compiler bytes, formal
sources, dependency caches, and active fresh4 inputs are outside the write
scope. Only root may run the separate bounded Lean experiment. No result here
provides chapter credit or replaces either full formal acceptance gate.
