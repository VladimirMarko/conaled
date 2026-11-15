# Native execution alternative: executable metadata boundaries

Read-only design investigation, 2026-11-03, responding to
`session/requirements/REQUEST-native-toolchain-042.md`. This document is an
analysis and proposed test scope, not a runtime approval or validation result.
No adapter was authored, no native fixture, emulator, or Lean command was run, and no active
runtime, controller, project source, dependency, or reference was changed by
this investigation. Only this report was written. A delegated source analysis
independently checked the executable-name and preload boundaries.

## Assessment

A narrowly scoped native adapter is technically plausible because glibc's
`getauxval(AT_EXECFN)` reads the current process's already-present auxiliary
vector. The retained glibc 2.39 implementation scans `GLRO(dl_auxv)`; it does
not open `/proc`. The previously recorded public fixture established that an
absolute direct invocation had matching auxiliary-vector metadata while the
ordinary own-executable `readlink` failed with `ENOENT`. That result is in
`native-metadata-feasibility-042.json`; it was not rerun here. [G1]

The proposed fallback can supply a missing item of own-process metadata
without retrieving a protected file or changing permissions. This conclusion
depends on preserving the ordinary runtime call, restricting applicability,
and keeping all executable inputs and pathname bindings stable. It is not a
claim that `AT_EXECFN` universally equals `/proc/self/exe`, or that a preload
adapter is automatically an accepted project runtime.

The important missing condition in a generic "absolute path resolving to a
regular ELF" rule is **launch identity**. A file that exists at a pathname now
need not be the file mapped into this process. Prefer direct execution of a
launcher-validated canonical absolute ELF, with a per-invocation marker that
matches this process's exact `AT_EXECFN`, and explicit frozen-input
preconditions. The marker is an applicability guard against accidental child
inheritance, not an unforgeable security credential.

## Supported native alternatives considered

| Route | Source finding and consequence |
| --- | --- |
| `LEAN_SYSROOT`, `LEAN_PATH`, or CLI root options | Lean's internal search-path initialization calls `getBuildDir`, which obtains `IO.appDir`. `LEAN_SYSROOT` affects the separate external `findSysroot` route. These variables do not skip the initial executable-path lookup. [L1, L2] |
| `lake env lean` or `lake lean` | The exact release spawns the same Lean executable. Lake's installation variables can select an installation; they do not replace Lean's source compiler or its startup dependency. The earlier `lean-native-path-options.md` records the exact entry points. [L3] |
| glibc loader `--preload` | This standard option scopes loading to one program, but requires direct-loader invocation. glibc rewrites `AT_EXECFN` in this mode, while kernel executable identity remains distinct. It is not a drop-in correction for the proc-path contract. [G2, M1] |
| Native execution on a normally provisioned host with working own-executable metadata | This avoids both emulation and the compatibility adapter while retaining the same official compiler bytes. No such additional available execution target was established by this investigation. Provisioning it must respect the environment's existing access controls. |
| Rebuilt/patched Lean or alternate compiler entry points | These are not the unchanged official-binary route under investigation. Existing `leanchecker`/`leanexport` consume compiled modules and do not replace the required source build. No compiler patch or substitute checker is proposed. |
| Existing QEMU profile | It remains a measured working recovery route in the parent session. This analysis makes no speed claim or recommendation to interrupt its jobs. |

## Why the launch contract matters

Linux source shows two different mechanisms: `AT_EXECFN` receives a copied
launch pathname, while proc executable lookup uses the task's executable
file object. The referenced upstream v6.8 sources establish the distinction;
they are not evidence that this host runs kernel v6.8. [K1, K2, K3]

| Launch or lifecycle case | Consequence and bounded treatment |
| --- | --- |
| Relative invocation followed by `chdir` | Later pathname resolution can name another file. Resolve before launch and directly execute the absolute canonical file; reject relative metadata. |
| Symlink invocation | A later link change can redirect canonicalization. Execute the resolved regular file itself and keep the directory bindings stable. |
| Rename, unlink, or replacement | The running image can survive while the pathname disappears or names another ELF. Rechecking existence or a hash is not a universal identity proof. These mutations are outside the frozen runtime contract; fail on an observed change. |
| Script invocation | The launch name and the interpreter image differ. Exclude script launch; checking ELF magic helps reject this case but does not establish the other conditions. |
| Descriptor execution | `execveat` can supply `/dev/fd/N`-style auxiliary metadata. Exclude `fexecve` and descriptor-relative execution; do not resolve through descriptor/proc aliases. [K1] |
| Direct `ld-linux PROGRAM` | glibc 2.39 explicitly rewrites `AT_EXECFN` to the target program at startup. An existing regular ELF and a matching marker alone cannot distinguish this launch mode. The controlled launcher must directly exec the target ELF. [G2] |
| `fork` without `exec` | Executable identity is retained, PID changes. Evaluate `getpid()` for each request; never cache the parent's PID. |
| `exec` of a different program | The new process receives new auxiliary metadata but can inherit the preload and marker. A stale parent marker must disable the fallback until an appropriate child launcher supplies its own marker. |

Frozen pathname and file-content assumptions are operational preconditions,
not an adversarially race-free checksum-then-exec guarantee. The adapter
should not claim complete procfs emulation, including deleted-file naming.

## Delegation and applicability contract

1. Preserve all inherited preload entries and their relative order. For this
   proposed profile, appending the compatibility library leaves inherited
   machinery first. Never replace the inherited list or print its contents.
   If a prior layer declines without delegating, accept that outcome. The
   fact that the adapter was not reached is not grounds to bypass the layer.
2. Resolve the next ordinary `readlink` with `dlsym(RTLD_NEXT, "readlink")`.
   Do not open libc separately, choose a hidden/versioned implementation to
   skip a layer, or issue a raw syscall. `RTLD_NEXT` is specifically defined
   to continue after the current object in a layered preload chain. [M1, M2]
3. Invoke that ordinary function before examining a potential fallback.
   Preserve its successful result and every error except the narrowly
   eligible `ENOENT`. In particular, do not retry or transform `EACCES` or
   `EPERM`. Ordinary workspace symlinks and unrelated missing paths must
   retain their normal behavior.
4. Match only `/proc/self/exe` or exactly `/proc/<current getpid()>/exe`.
   Relative spellings, suffixes, other proc resources, and other-process
   paths receive no fallback. Pure string checks or controlled fixture
   layers can test negative matching without reading another process.
5. Require a nonempty absolute launcher marker, exact equality to this
   process's `AT_EXECFN`, and the declared canonical, regular, frozen ELF
   launch contract. Perform launcher checks through ordinary allowed file
   APIs. Do not turn a validation error into a reason to access another
   pathname or use another I/O mechanism.
6. For valid output buffers, copy at most the requested byte count, return
   the copied count, and append no NUL. Retain ordinary zero-size errors.
   Userspace copying does not reproduce arbitrary kernel pointer-fault
   handling: invalid buffers are explicitly unsupported. [M3]

Canonicalization and immutable-file/hash checks fit most naturally in the
launcher, before direct execution. Keeping the fallback itself limited to
already-validated own-memory metadata reduces reentrancy and filesystem
work in the interposed function. If validation is also performed there, it
must use ordinary exported APIs, reject every failed validation, and avoid
manual selection of implementation entry points that skip runtime layers.

An inherited marker alone deliberately does not activate unrelated helpers.
Consequently, intended Lake-to-Lean invocations, optional `leanir`, cache
programs that use `IO.appDir`, and server workers need their own explicit
launch paths. Lake derives tool paths from its selected installation;
merely placing a wrapper first in `PATH` is insufficient if the selected
sysroot still leads to an unwrapped binary. The Lean watchdog can select
`LEAN_SYSROOT/bin/lean` or `LEAN_WORKER_PATH`. These installation paths must
remain consistent with the validated distribution. [L3, L4]

## Initialization, errno, and unsupported cases

Symbol resolution needs thread-safe publication and a recursion guard.
Another shared object's constructor can call `readlink` before this
adapter's constructor, so a constructor alone is not a complete strategy.
An unresolved or reentrant initialization must fail honestly; it must not
fall through to a syscall or return invented metadata. Avoid logging and
allocation in the resolver/fallback where practical. `dlsym` is documented
thread-safe, but that does not make arbitrary wrapper initialization
recursion-safe. [M2]

Save the caller's errno before initialization, restore it before delegation,
and preserve the delegated result's errno when returning that result.
If eligible fallback succeeds, document restoring the caller's initial
errno as the chosen convention; this avoids leaking the internal `ENOENT`
or validation errors. If eligibility fails, return the saved ordinary
failure. Successful libc calls are allowed to change errno, so tests must
not impose a nonexistent general POSIX guarantee on the delegated layer.
[M4]

Ordinary `readlink` is async-signal-safe; a wrapper that lazily calls `dlsym`,
locks, allocates, or canonicalizes paths need not be. The initial supported
case should therefore be normal Lean/Lake runtime calls, not an unrestricted
claim of libc equivalence in signal handlers or during reentrant loader
initialization. The valid-buffer, Linux/glibc/x86-64, dynamic-ELF, direct-exec
conditions should be explicit. Static executables, other libcs, secure
execution, `readlinkat`, and fortified alternate entry points are separate
cases; do not try to override loader restrictions to support them. [M1, M5]

## Recommended bounded tests

These are proposals for the parent implementation loop. No test in this
table was executed by this investigation.

| Fixture | Required observation |
| --- | --- |
| Direct absolute own-executable query | Both own-path spellings return the validated path; arbitrary `argv[0]` and a later workspace `chdir` do not affect it. Baseline ordinary failure remains recorded separately. |
| Buffer boundaries | Sizes 0, 1, exact pathname length, and larger capacity; sentinel bytes demonstrate correct count, truncation, no added NUL, and no write beyond the buffer. |
| Ordinary filesystem calls | An ordinary symlink and an unrelated missing file wholly inside the fixture directory behave exactly as without the adapter. |
| Controlled next-layer interposer | A harmless fixture records delegation and produces selected success, `ENOENT`, `EACCES`, `EPERM`, and another error. Check preservation without accessing protected files or presenting fixture responses as real host-policy observations. |
| Inheritance | A different child executable with the parent's marker receives no fallback; its own launcher can activate its own metadata. A fork-only child uses its new PID. |
| Applicability rejection | Missing, empty, relative, or mismatched markers are inactive. The launcher rejects unsupported script/descriptor/loader-direct launch forms and changed candidate inputs. All files remain task-local. |
| Initialization | Constructor-time and concurrent first calls do not deadlock or race. Any deliberately unsupported resolution case fails visibly, without an alternate filesystem mechanism. |

Once those implementation checks and the project's independent reviews
support proceeding, genuine Lean/Lake version and prefix queries, a small
theorem, and rejection of a deliberately false proposition can establish
bounded native functionality. They are still not a complete project gate.
A full native gate must have its own runtime/source identity and terminal
record; it cannot inherit success from an unfinished QEMU run. This report
neither authorizes nor records such runs.

## Primary-source basis

- **L1:** [Lean v4.35.0 path initialization](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Util/Path.lean), read from the verified installed distribution; `getBuildDir`, `initSearchPathInternal`, `findSysroot`.
- **L2:** [Lean v4.35.0 runtime I/O](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/runtime/io.cpp), retained as `session/tools/native-source-042/lean-runtime-io.cpp`; SHA-256 `c8ef5d102a706d2aae710eac1f2dc9a2b6a81e5245cf5ccb36500973b32aa77f`. Linux `lean_io_app_path` calls ordinary `readlink` on the current PID path.
- **L3:** [Lake v4.35.0 installation discovery](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/Config/InstallPath.lean), read from the verified distribution. Related exact subprocess entry points and hashes are retained in `lean-native-path-options.md`.
- **L4:** [Lean v4.35.0 watchdog](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Server/Watchdog.lean), read from the verified distribution; `findWorkerPath`.
- **G1:** [glibc 2.39 getauxval](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/misc/getauxval.c), retained as `session/tools/native-source-042/glibc-getauxval.c`; SHA-256 `c29f55fc007d37ef7a186326428a7ebddd1ab215636771b1fe9c0160a856868e`. Original source acquisition is recorded in `native-source-provenance-042.json`.
- **G2:** [glibc 2.39 runtime loader](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/elf/rtld.c), fetched into memory during this investigation; 88,632 bytes, SHA-256 `03681f7c7cea6f542a6416e3478a8c6bfe6c3a7969d1bb081dbba4f18395ed49`. The direct-loader auxiliary-vector rewrite is at 1620–1622; preload handling is at 1838 onward.
- **K1:** [Linux v6.8 exec](https://raw.githubusercontent.com/torvalds/linux/v6.8/fs/exec.c), fetched into memory; 53,615 bytes, SHA-256 `6df9a811b61b67caf4b48a3d55b2bf89ce46a8147563ce3fdbfaf86dccbc9838`. Filename construction and copying establish launch-name semantics.
- **K2:** [Linux v6.8 ELF loader](https://raw.githubusercontent.com/torvalds/linux/v6.8/fs/binfmt_elf.c), fetched into memory; 57,242 bytes, SHA-256 `2ba2e4e6b60cb3366010d37e26238774b79cad9f303c5ad4699628f14117ff5e`. `AT_EXECFN` receives `bprm->exec`.
- **K3:** [Linux v6.8 proc executable lookup](https://raw.githubusercontent.com/torvalds/linux/v6.8/fs/proc/base.c), fetched into memory; 96,308 bytes, SHA-256 `12c5c231cf7ddb0d15145f7b900e9244f04099e7d5143881c6d3208ee0e5dca8`. `proc_exe_link` obtains the executable file object's path.
- **M1:** [Linux man-pages project: ld.so](https://man7.org/linux/man-pages/man8/ld.so.8.html), examined by the delegated investigator for preload order, `--preload`, and secure-execution limits.
- **M2:** [Linux man-pages project: dlsym](https://man7.org/linux/man-pages/man3/dlsym.3.html), read directly for next-layer resolution and thread-safety semantics.
- **M3:** [Linux man-pages project: readlink](https://man7.org/linux/man-pages/man2/readlink.2.html), read directly for byte-count, truncation, termination, and errors.
- **M4:** [Linux man-pages project: errno](https://man7.org/linux/man-pages/man3/errno.3.html), read directly for error/success conventions.
- **M5:** [Linux man-pages project: signal-safety](https://man7.org/linux/man-pages/man7/signal-safety.7.html), read directly for the ordinary `readlink` contract.
