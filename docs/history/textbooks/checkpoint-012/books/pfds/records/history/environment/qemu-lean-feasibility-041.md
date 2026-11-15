# QEMU Linux user-mode feasibility for exact Lean 4.35.0

Read-only source investigation, 2026-11-03, by
`/root/lean_native_path_options`. This extends
`lean-native-path-options.md` after the user's clarification that Nix is
optional. It does not record a successful emulator, compiler, or build run.

## Assessment

An explicit invocation of the unchanged official Lean binary through QEMU
Linux user-mode is a technically plausible way to provide the compiler's own
executable-path metadata in this workspace. The inspected QEMU source has
dedicated handling for that metadata. Direct invocation needs no system
installation, binfmt registration, mount, preload interposition, or compiler
patch. Actual compatibility remains an execution question for the parent;
this investigation performed no such experiment.

A transparent launcher for each required compiler executable is needed for a
Lake integration. Starting only Lake under QEMU does not automatically keep
all its child executables under emulation. The proposed separate workspace
profile can preserve the original distribution and retain byte-identical
compiler copies while providing those explicit launch points.

## Exact executable-path and process behavior

In upstream v7.2.0, `is_proc_myself` recognizes both self and own-PID paths;
emulated `getpid` matches that PID. `readlink` and `readlinkat` return the
canonical guest executable path without reading host `/proc`. Successful
guest `execve` calls host execve and leaves the emulator; fork alone does
not. Thus emulating Lake does not automatically emulate its subsequently
executed compiler children. [Q1]

The argument parser stores the supplied guest program argument.
Canonicalization happens later and follows symlinks, so use an absolute
path that remains valid after directory changes. [Q2, Q1]

## Proposed separate profile: feasibility and boundaries

The parent proposed a profile with genuine compiler bytes copied to
`<profile>/bin/lean.real` and a transparent `<profile>/bin/lean` launcher.
The launcher would invoke QEMU with the absolute path of `lean.real` and
forward all original arguments, streams, environment, working directory and
terminal status. It must produce no compiler output of its own, including
version output. No launcher was written by this investigation.

With a regular copied executable there, Lean's `getBuildDir` would identify
the profile: it takes the executable directory's parent, irrespective of the
filename suffix. A symlink into the original distribution instead resolves
to that original root. The profile needs consistent compiler, library,
header and source paths. [Q1, Q2, L1]

Lake constructs its tool paths from the discovered sysroot. `LEAN` is used
for sysroot discovery; it does not remain an arbitrary compiler-command
override. `LEAN_SYSROOT` takes precedence, and `LeanInstall.get` derives
`bin/lean`, `bin/leanir`, and other tool paths from it. An isolated profile
therefore fits Lake's existing path model, while setting only `LEAN` to a
wrapper is insufficient. The genuine `--print-prefix` and `--githash`
responses must agree with the intended profile. [L2]

### Child and helper paths that matter

| Path | Exact-release source finding | Consequence for the profile |
|---|---|---|
| Ordinary batch Lean elaboration | No compiler self-spawn was found in the inspected Shell, Elab, Compiler and Runtime sources; a second agent independently checked these paths. | A direct per-invocation launcher is plausible for the batch compiler; this is a bounded source inspection, not a claim about every metaprogram. [L7] |
| Lake module compilation | `compileLeanModule` invokes the selected `lean` executable. | Lake must resolve the profile's launcher. [L3] |
| Postponed native compilation | If `compiler.postponeCompile` is enabled for a module and the relevant artifacts are requested, Lake separately invokes `leanir`. The option defaults to false. `LeanIR.main` also calls internal search-path initialization. | A lean-only profile does not cover this optional build path; a corresponding genuine `leanir` launch path may be needed. [L3, L4, L5] |
| Lean language-server workers | `findWorkerPath` starts from `IO.appPath`, then applies `LEAN_SYSROOT/bin/lean`, then `LEAN_WORKER_PATH` if supplied. The watchdog spawns that result with worker arguments. | Without an override, it could execute `lean.real` natively. Keeping the profile sysroot selects the launcher; the documented-in-source worker override has final precedence. [L6] |
| Native helpers and user code | Lake also has C compiler, archiver and archive-tool paths. Lean tactics or metaprograms may execute additional programs. | QEMU does not automatically wrap these. Their real execution and availability must be established by the unchanged required workload. [L2] |

## Runtime and performance limits

QEMU user-mode translates instructions and system calls; it is not a new
guest kernel or a complete proc filesystem. Its v7.2 documentation describes
host-thread creation for guest threads and host-kernel participation in
signal handling. Running the same architecture still uses the emulator's
execution loop, so compilation overhead and additional translation memory
are expected, but no slowdown factor has been measured here. [Q2, Q3]

The guest ELF interpreter and dynamic libraries must remain accessible.
QEMU's ELF loader opens the guest interpreter through its configured path
mapping, and the manual documents an interpreter-prefix option. A static
QEMU executable removes QEMU's own dynamic-library requirement; it does not
make Lean or its dependencies static. Existing scoped library paths remain
relevant until actual probes establish otherwise. [Q3, Q4, D1]

A successful version probe would establish only startup. It would not
establish cache restoration, native helper execution, a complete build,
project audits, or the candidate's acceptance. The parent's existing full
and focused gates must still finish with authentic terminal results, fixed
inputs, ordinary proof checking, and the existing resource/concurrency
policy. Runtime overhead is not grounds to weaken those requirements.

## Debian package correspondence

The parent's `session/tools/qemu-041/package.json` selects official Debian
bookworm `qemu-user-static` version `1:7.2+dfsg-7+deb12u18+b3`, amd64, and
records package SHA256
`c3e3ba2bd87f8c5b9a5da5ef21b5a3b82d7c63b89dd448d9ddaa4eabc5b6e402`.
Binary acquisition and execution are the parent's work, not this report's
validation result.

This investigation fetched that source version's official `.dsc` and Debian
patch archive. The archive's SHA256 matches the value in the `.dsc`; no PGP
signature verification was performed here. The patch series includes stable
updates through v7.2.22. Inspection of all patches touching the two relevant
Linux-user files found no change to the readlink, own-PID or execve branches
described above. Debian's additional binfmt-preserve-argv patch activates for
a special executable-name suffix; it does not supply recursive emulation
for ordinary direct invocation. The original Debian source tarball was not
downloaded or rebuilt. [D2, D3]

## Primary-source records

QEMU and Debian source downloads are retained under
`session/tools/lean-native-path-options/qemu-7.2/`. Lean sources were read
from the parent's checksum-verified official v4.35.0 distribution.

| ID | Official source | Local SHA256 |
|---|---|---|
| Q1 | [QEMU v7.2.0 Linux-user syscalls](https://raw.githubusercontent.com/qemu/qemu/v7.2.0/linux-user/syscall.c) | `052e666363397f18e466b93b007434f6e84ac65c7f1d3fc6362b1b1c46917d52` |
| Q2 | [QEMU v7.2.0 Linux-user main](https://raw.githubusercontent.com/qemu/qemu/v7.2.0/linux-user/main.c) | `7f64389216056361869d9bc39ee6fe58d4663126d19b839365a74a1777774d3a` |
| Q3 | [QEMU v7.2.0 user manual source](https://raw.githubusercontent.com/qemu/qemu/v7.2.0/docs/user/main.rst) | `b12cb70660d437fd4b174e582f116d9e02dd75a0e518ff43ecbca4041e63627d` |
| Q4 | [QEMU v7.2.0 ELF loader](https://raw.githubusercontent.com/qemu/qemu/v7.2.0/linux-user/elfload.c) | `a59d024cea52f63084554954f63129bd596ff8dc6257f6032b77eaf578e381c2` |
| D1 | [Debian bookworm static-user-emulator manual](https://manpages.debian.org/bookworm/qemu-user-static/qemu-x86_64-static.1.en.html) | Web documentation; no local-byte hash asserted |
| D2 | [Debian source descriptor](https://deb.debian.org/debian/pool/main/q/qemu/qemu_7.2+dfsg-7+deb12u18.dsc) | `6b6bd27b947ec89e40a1d6b26d9c9f3c698ca691da13163e0483f6061bbb20b3` |
| D3 | [Debian patch archive](https://deb.debian.org/debian/pool/main/q/qemu/qemu_7.2+dfsg-7+deb12u18.debian.tar.xz) | `28a1c86310ee53b6bf1854cffe6f6be6ed29a08db7d05759f8ac57b8d6a6cb2f` |
| L1 | [Lean v4.35.0 path initialization](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Util/Path.lean) | `52cf9aa41a82db18d0d3c93bf6257d064f773af9e62b8b43be89ce1b0e00055f` |
| L2 | [Lake v4.35.0 installation paths](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/Config/InstallPath.lean) | `fc5bc3094122fb0384c01cb4d70bf0bd0e84744ec340affadf04b09c88088277` |
| L3 | [Lake v4.35.0 build actions](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/Build/Actions.lean) | `9c7d7101f89eb1d0618d8a76b86c30d628932ed2d2088db29792fdf88fb1e870` |
| L4 | [Lean v4.35.0 IR executable](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/LeanIR.lean) | `cb0e362fc299ab84ead24874efacc462e25c8c43aaa9d24276518a9ef538dee2` |
| L5 | [Lean v4.35.0 compiler options](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Compiler/Options.lean) | `26077071ffc64e4032d2d573c4013e96078367dc832a677afc981fb16c7496f2` |
| L6 | [Lean v4.35.0 server watchdog](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Server/Watchdog.lean) | `b7effb6f7e34f7a3b634cf6b4dc3772ddf1ccbfc418f351115755b85e8a5e642` |
| L7 | [Lean v4.35.0 shell](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Shell.lean) | `bbfcf01a93bcb9ca3f4d1264d3ad9890f3a6384dbbc949f5bf3cc286c0ec2225` |

No compiler, emulator, build, cache restoration, or audit was executed by
this investigator. No executable, project source, tracker, dependency pin,
global environment, mount, or access policy was modified. Only official
source material was retrieved and this report was added.
