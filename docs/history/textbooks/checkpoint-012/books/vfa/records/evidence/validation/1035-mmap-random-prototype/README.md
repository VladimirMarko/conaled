# #1035 experimental mmap / MADV_RANDOM prototype

The isolated prototype and its small boundary checks are complete. Source and
binary are frozen for root's separately owned bounded Lean probe. This is not
production adoption, a formal candidate gate, or a performance claim. No Lean
compiler was invoked by the prototype implementer.

The contract is `work-state/specs/1035-mmap-random-experiment.md`.
`SOURCE_BASIS.md` preserves the exact primary-source basis and limits.
`prototype-ready.json` records final identities and outcomes.

## Select only for the bounded experiment

The real library is:

```text
/workspace/scratch/83865511e965/recovery/conaled-vfa-checkpoint-035-returned-archive-preservation/runtime-tmp/1035-mmap-random-prototype/libconaled_mmap_random.so
```

| Input | SHA-256 |
| --- | --- |
| `mmap_random.c` | `c7eb24d83bc3554f1a9ac2f986e5c7dcf0913a44e24f65f782898a00a61ec807` |
| `mmap_random.h` | `80911142ad8b8a6dd7836dfcbc8b8e25fdd7d2ec82486b922b41e72a5f613694` |
| `libconaled_mmap_random.so` | `5927638bd66ec29be8ea496f3a8fe9e13b3d17fd2b7dc7bcf9567d105009799b` |

The three environment settings are:

| Setting | Meaning |
| --- | --- |
| `CONALED_MMAP_RANDOM=1` | Exact opt-in; absent, `0`, or other values disable advice. |
| `CONALED_MMAP_RANDOM_EXE=/absolute/executed/payload` | Must be absolute and exactly equal to the current process's in-memory `AT_EXECFN`. |
| `CONALED_MMAP_RANDOM_REPORT=1` | Optional single stderr summary on normal exit. Omit for the default of no diagnostic output. |

The explicit report also requires the opt-in and matching identity. Its line
begins `conaled-mmap-random-v1` and includes total calls, preferred-shape
successes, gate rejections, selected mappings, selected bytes, advice successes,
advice failures, and the last advice errno. Counters are observational, not an
independent kernel trace. The report is best-effort and not guaranteed on
signal termination. Root must preserve the actual captured diagnostic.

Only root's separate probe selects this library. The accepted helper, native
startup shim/overlays, and active fresh4 environment remain unchanged. Root's
`probe-original-squares.py` and `original-squares-input.json` are root-owned
and were left untouched. **Do not include the separately built
`libfail_madvise_test_only.so` in a real Lean invocation.**

## Behavior

The exported `mmap` path is restricted to the actual Linux x86_64 LP64 ABI.
It retains glibc's low-12-bit offset-alignment rejection, then forwards the
ordinary call through libc's `syscall(SYS_mmap, ...)` with the byte offset
unchanged. There is no `dlsym`, mutable initialization cache, forced fallback,
remapping, file write, address/protection change, or eager region copy.

Advice is possible only after a successful mapping returns the requested
non-null preferred address, with a nonnegative file descriptor, zero offset,
exact `PROT_READ | PROT_WRITE`, exact
`MAP_PRIVATE | MAP_FIXED_NOREPLACE`, and both opt-in/identity checks satisfied.
The prototype then calls only `madvise(..., MADV_RANDOM)` and returns the
original mapping with its original errno, regardless of the advice outcome.

Counters use lock-free atomics. The read-only snapshot API is described in
`mmap_random.h`. Stable environment strings and ordinary ownership of the
just-created mapping remain assumptions; this is not a general-purpose
interposer for arbitrary concurrent environment/range mutation or other ABIs.

## Build identity

`scope-start.json` records `/usr/bin/cc`, resolved to
`/usr/bin/x86_64-linux-gnu-gcc-13`, Ubuntu GCC 13.3.0-6ubuntu2~24.04. The
compiler driver SHA-256 is
`6117c52522997d2aaccb2b52b3c6bf42c0a6c5edb1d718431fed6b2fc5fec234`.
The process reports glibc 2.39.

`prototype-build.json` preserves exact source/header/binary identities, argv,
cwd, stdout, stderr, exit codes, and timings. Both final builds exited 0.
The real library's build flags were:

```text
/usr/bin/cc -std=c11 -shared -fPIC -O2 -Wall -Wextra -Werror -Wl,-z,now -Wl,-z,relro -o REAL_LIBRARY_PATH mmap_random.c
```

The record contains the actual absolute paths. The first compile attempt
reported a `-Werror` warning about an ignored diagnostic `write` result.
That failed command/source are retained as `build-attempt-1.json` and
`mmap_random.build-attempt-1.c`; the final source handles that result. No
successful runtime input was replaced by this correction.

## Observed checks

The agreed test seam is the actual mmap interface in fresh bounded processes,
with the public snapshot/report interface providing advice observations.
Every fixture used one newly created 4,096-byte file and at most one live
explicit page mapping. Limits were 15 seconds externally, 5 CPU seconds,
256 MiB of address space, and 64 KiB per output file in the child. Fixtures
never execute their mapped file bytes and never access the beyond-EOF test
mapping.

| Evidence | Actual result |
| --- | --- |
| `red-positive-test.json` | Intentional exit 1 with the precise missing-advice assertion under a diagnostic-only control; real libc mmap otherwise behaved normally. |
| `green-positive-test.json` | Exit 0. One real advice call succeeded for 4,096 bytes; original address/bytes/errno 123 were retained; private writes left the file unchanged; collision returned `EEXIST` without advice or overwrite; cleanup succeeded. |
| `boundary-suite.json` | Ten additional process cases, all exit 0; direct libc passthrough outcomes matched the prototype. |

The boundary suite covered unset/zero/invalid opt-in; unset, mismatched, and
relative executable identity; default-off diagnostics; and injected advice
failure. The injected `EAGAIN` was recorded while the successful mmap retained
its original address, bytes, and errno 123. The original collision/file-isolation
checks still passed. This was a test-only injected error, not an observed host
kernel failure.

Two passthrough cases ran the same ten mapping shapes with direct libc and
with the real prototype: ordinary private, anonymous, writable shared,
read-only, executable, additional flags, aligned nonzero offset, unaligned
offset, zero length, and invalid descriptor. No advice was issued; results
and errno values matched. The tests checked readable contents and unchanged
backing bytes where applicable.

`positive-tracer-v1.py` preserves the exact first red/green fixture.
`test_mmap_random.py` contains the extended fixture; `run_boundary_tests.py`
records the one-use negative suite. The source and actual records identify
each command, selected environment, timeout, outcome, and input hash. No
additional successful-test repeats or larger runtime experiments were run.

The final identity check confirmed the parent specification, accepted helper,
accepted startup-shim source, and root-owned original Squares input record
still matched their starting hashes. No formal source, dependency tree,
active compiler input, or active fresh4 output was changed.
