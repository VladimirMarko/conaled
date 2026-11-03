# Recover the PFDS environment without the old workspace or chat

This is the takeover entry point for the **PFDS book/thesis union** workstream.
Read `../STATUS.md`, the local tracker, and the full governing requests under
`../requirements/`: `REQUEST.md`, `REQUEST-union-v2.md`,
`REQUEST-direct-toolchain-041.md`, `REQUEST-environment-handoff-042.md`, and
`REQUEST-native-toolchain-042.md`.

The user permits development without Nix and has explicitly asked for an
alternative to slow emulation. The native route below executes the unchanged
pinned Lean binaries. QEMU is retained as a tested fallback in section10.
Current review and formal-validation status always comes from the actual
records; working compiler smoke tests do not accept a mathematical candidate.
Exact pins, source policy, proof audits, independent reviews, isolated frozen
candidates, final verification, chapter order, local tickets, and immediately
exposed/uploaded durability checkpoints remain mandatory. Do not push to GitHub.

## 1. Restore the correct source history

Use the latest delivered **conaled-pfds-checkpoint-NNN.tar.gz**, its published
SHA256, and that archive's top-level `README.md` and `restore.py`. The archive
contains all Git refs/history and local session records; it excludes ordinary
build outputs, dependency checkouts, downloaded toolchains, and manuscripts.

Checkpoint041 is a verified recovery baseline:

| Item | Identity |
| --- | --- |
| Archive SHA256 | `42886cbe040211571e9dba330e67e08dcfc1c3d6a962b40fb54cf987cf4f0301` |
| Archive bytes | 76796513 |
| Main branch | `pfds/local` |
| Main HEAD at that checkpoint | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Approved operational-helper snapshot | `822cb7adeed4943acaf10454e9facfc2e3ee8ceb` |

For a newer checkpoint, its manifest, delivered checksum, current status and
tracker take precedence over these historical baseline values. An archive's
own upload receipt necessarily postdates its payload; the next checkpoint
retains it. A passed restore test is not a proof/build result.

The user-supplied comparison guide's other “checkpoint039” (SHA256 beginning
`5ac950...`, branch `local/adwh-continue-2026-11-03`, candidate `f62c48...`)
belongs to a different workstream. Our original PFDS039 has SHA256
`c9df19c0c3af4c08295cca6e0dabeadf3775e4ec8f0148e90295f8e2317947d1`.
Do not substitute the other archive, branch, candidate or acceptance commands.

Extract the selected archive into a new staging directory. Its entries are
at the top level (including `restore.py`), rather than under an extra named
folder. Run its restore script with a **new absolute destination directory**:

```sh
python3 /absolute/staging-directory/restore.py /absolute/new/pfds
```

From here, run acquisition commands from that restored `pfds` directory. The
recipes use only workspace paths. Existing unknown directories are deliberately
not reset or overwritten. If a partial installation conflicts, preserve it and
inspect it or choose a fresh workspace; do not remove source or evidence to make
a check pass.


## 2. Supporting programs and runtime constraints

The native route uses x86-64 Linux with glibc, Python3.12+, Git, curl with HTTPS,
`sha256sum`, GNU tar with zstd support, and a native C compiler available as `cc`
with the ordinary C, dynamic-loader and pthread development interfaces. The
optional QEMU extraction additionally needs `dpkg-deb`. This host reports
glibc2.39 and nine CPUs; these are observations, not new project pins.

A normally provisioned Linux host can run the official distribution directly.
This restricted host lacks the executable-path entry that Lean expects under
`/proc`. The native profile supplies only that missing own-process metadata
from the same process's existing auxiliary vector. It does not emulate CPU
instructions, patch Lean, mount filesystems, or change host permissions.
`LEAN_SYSROOT` alone does not prevent Lean's initial executable-path lookup.

Use a dedicated Bash shell and stop on acquisition errors:

```sh
set -euo pipefail
cd /absolute/new/pfds
PFDS_ROOT="$(pwd -P)"
mkdir -p toolchains/downloads session/tools
```

Do not replace `HOME` or `CODEX_HOME`. The launcher scopes its settings to the
invoked command, preserving existing preload entries and their relative order.

## 3. Acquire the exact official Lean distribution

The project pin is `leanprover/lean4:v4.35.0`; its official Linux distribution
includes Lake5.0.0-src+eb6cafb. The following is for a fresh extraction. If the
directory already exists, verify the installation rather than extracting over it.

```sh
test ! -e toolchains/lean-4.35.0-linux
curl --fail --location \
  https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst \
  --output toolchains/downloads/lean-4.35.0-linux.tar.zst
sha256sum --check <<'SHA256'
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  toolchains/downloads/lean-4.35.0-linux.tar.zst
SHA256
tar --no-same-owner --zstd \
  -xf toolchains/downloads/lean-4.35.0-linux.tar.zst -C toolchains
```

The archive is 594481375 bytes. Its digest was checked against official GitHub
release metadata; see `direct-toolchain-041.json`. `--no-same-owner` avoids
restoring the archive's original uid/gid on a restricted host and does not
change the distributed file contents.


## 4. Construct and verify the native profile

Check the three original executable digests before profile construction:

```sh
sha256sum --check <<'SHA256'
bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38  toolchains/lean-4.35.0-linux/bin/lean
8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1  toolchains/lean-4.35.0-linux/bin/lake
5908f2917dcda5ed840e1ff5d6cdac5d104f9f6ca1ab1dc9f11d1c9fe220487e  toolchains/lean-4.35.0-linux/bin/leanir
SHA256
python3 session/environment/run-native-toolchain.py --create
python3 session/environment/run-native-toolchain.py --describe
python3 session/environment/run-native-toolchain.py -- lean --version
python3 session/environment/run-native-toolchain.py -- lake --version
```

Expected genuine outputs:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

`--create` compiles the included `native-own-exe.c`, stages a complete new
`toolchains/lean-4.35.0-native` profile, and renames it into place. It refuses
an existing profile. `--describe` is read-only and validates source, native
library, original executables, copied executables, wrappers and receipt hashes.
An existing installation should be inspected, not overwritten. Reconstruct
from source after relocation: generated wrappers contain absolute paths.

The native profile copies the three small `lean`, `lake`, and `leanir` ELF
entrypoints byte for byte; other release content is referenced unchanged.
The original compiler and kernel execute natively. Each wrapper marks its own
regular executable with `PFDS_NATIVE_EXECUTABLE`. The compatibility library
first delegates `readlink` to the next existing implementation. Only an
`ENOENT` for this process's exact executable link, with a matching canonical
absolute regular ELF launch, permits the fallback. Successful original calls,
other paths, and permission errors retain their ordinary result. Existing
preload machinery stays first; the new library is appended.

This is a bounded launcher contract, not general procfs or libc emulation.
Keep executable bytes and directory bindings frozen. Unsupported cases include
scripts/direct-loader/descriptor execution, moved or replaced executables,
invalid pointers, asynchronous signal-handler calls, and alternate libc or
readlink entry points. A marker is not an authentication credential. An exec
into a different program with a stale marker disables the fallback; intended
compiler children obtain their own marker from their wrapper.

The launcher fixes PATH, sysroot, library paths, both cache paths, TMPDIR and
one Lean thread. Unexpected inherited Lean/Lake selectors are rejected with
their names. Start a clean launch shell instead of hiding or overriding the
stock check's compiler-selection rules. Do not remove host permission or
authentication machinery. No native runtime change is accepted solely because
version strings print; consult the retained current review and actual tests.

## 5. Restore every dependency at the manifest revision

The expected manifest SHA256 for the current candidates is
`dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b`.
It pins all nine repositories. This complete recipe is durable; no script from
an excluded downloads/tools directory is needed. Existing checkouts are only
verified, never reset, updated or overwritten.

```python
from pathlib import Path
import hashlib
import json
import subprocess

root = Path.cwd().resolve()  # run from the restored pfds directory
repo = root / "conaled"
manifest_path = repo / "lake-manifest.json"
assert hashlib.sha256(manifest_path.read_bytes()).hexdigest() == (
    "dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b")
manifest = json.loads(manifest_path.read_text())
store = root / "dependency-store-041"
store.mkdir(exist_ok=True)

def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()

for package in manifest["packages"]:
    assert package["type"] == "git"
    path = store / package["name"]
    if not path.exists():
        path.mkdir()
        git(path, "init", "--quiet", "--initial-branch=restoration")
        git(path, "remote", "add", "origin", package["url"])
        git(path, "config", "remote.origin.pushurl", "DISABLED-local-only")
        git(path, "fetch", "--depth=1", "--no-tags", "origin", package["rev"])
        git(path, "checkout", "--quiet", "--detach", "FETCH_HEAD")
    assert Path(git(path, "rev-parse", "--show-toplevel")).resolve() == path.resolve()
    assert git(path, "rev-parse", "HEAD") == package["rev"], package["name"]
    assert git(path, "remote", "get-url", "origin") == package["url"], package["name"]
    assert not git(path, "status", "--porcelain=v1", "--untracked-files=all"), package["name"]
    print(package["name"], package["rev"], "clean")
```

Save the block as a temporary Python script inside the restored workspace and
run it with Python3, or paste it into `python3 - <<'PY' ... PY`. Never use
`lake update` to repair this environment. Preserve every transitive pin, not
only Mathlib's `56a005855ea17e0b0958f73ec801ae140b0a1679`.


## 6. Materialize the current candidates and private build directories

Consult current status first. At this handoff, the next full candidate is
`901f734161920a76f3b399a575805b9a1d31e971` and the focused candidate is
`956c4b06abe8d54f78a6166690c12453115f8304`. In a new restoration where their
directories do not exist:

```sh
git -C conaled worktree add --detach "$PFDS_ROOT/import-correction-r3" \
  901f734161920a76f3b399a575805b9a1d31e971
git -C conaled worktree add --detach "$PFDS_ROOT/signed-potential" \
  956c4b06abe8d54f78a6166690c12453115f8304
```

Each checkout needs its own real `.lake` directory. Only `.lake/packages`
points to the shared exact dependency store. Never share project `.lake/build`
directories or candidate verification records between active checkouts.

```python
from pathlib import Path
import subprocess
root = Path.cwd().resolve()
for name, expected in (
    ("import-correction-r3", "901f734161920a76f3b399a575805b9a1d31e971"),
    ("signed-potential", "956c4b06abe8d54f78a6166690c12453115f8304"),
):
    checkout = root / name
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip() == expected
    assert not subprocess.check_output(["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=checkout, text=True)
    lake = checkout / ".lake"
    assert not lake.is_symlink(), "Each candidate needs a real private .lake"
    lake.mkdir(exist_ok=True)
    assert lake.resolve() == checkout / ".lake"
    build = lake / "build"
    assert not build.is_symlink(), "Never share project build directories"
    if build.exists():
        assert build.is_dir() and build.resolve() == lake / "build"
    assert not (lake / "verification.json").is_symlink()
    link = lake / "packages"
    target = root / "dependency-store-041"
    if link.exists() or link.is_symlink():
        assert link.is_symlink() and link.resolve() == target
    else:
        link.symlink_to(target, target_is_directory=True)
```

Do not carry temporary `GIT_INDEX_FILE` settings into `git worktree add`.
An earlier artifact-test checkout had a missing private index from that setup
mistake; its preserved reconciliation is not permission to waive clean state
for any formal candidate run.


## 7. Check the public compiler path and obtain the dependency cache

From `pfds`, run the supplied real smoke tests with new report filenames:

```sh
python3 session/environment/test-direct-toolchain.py \
  --workspace "$PFDS_ROOT" \
  --runner "$PFDS_ROOT/session/environment/run-native-toolchain.py" \
  --report "$PFDS_ROOT/session/validation/recovery-cli-new.json"
python3 session/environment/test-direct-lake-build.py \
  --workspace "$PFDS_ROOT" \
  --runner "$PFDS_ROOT/session/environment/run-native-toolchain.py" \
  --report "$PFDS_ROOT/session/validation/recovery-lake-new.json"
```

These test the exact versions, a valid theorem with no axioms, rejection of a
false theorem, Lake's compiler path, and native compilation/linking/execution.
They create their temporary parents after a cold recovery. They are not a
full project acceptance check. Choose unused report names to preserve history.

Initialize the shared dependency outputs once from `import-correction-r3`:

```sh
cd "$PFDS_ROOT/import-correction-r3"
python3 "$PFDS_ROOT/session/environment/run-native-toolchain.py" -- lake build cache
python3 "$PFDS_ROOT/session/environment/run-native-toolchain.py" -- lake env \
  env PFDS_NATIVE_EXECUTABLE="$PFDS_ROOT/dependency-store-041/mathlib/.lake/build/bin/cache" \
  "$PFDS_ROOT/dependency-store-041/mathlib/.lake/build/bin/cache" get
cd "$PFDS_ROOT"
```

The cache executable also calls `IO.appDir`. `lake env` supplies the source
search environment, and the explicit per-invocation marker supplies its own
native executable identity. Keep the bundled leantar and default cache policy.
The historical QEMU cache run downloaded/decompressed9031 files; a recovery
must observe its own real exit and recheck all nine dependency heads/statuses.

The native public metadata-contract suite is also included:

```sh
python3 session/environment/test-native-own-exe.py \
  --workspace "$PFDS_ROOT" \
  --profile-identity "$PFDS_ROOT/toolchains/lean-4.35.0-native/profile-identity.json" \
  --record "$PFDS_ROOT/session/validation/native-own-exe-contract-042-r-recovery.json"
```

Its controlled downstream-library failures are test fixtures, not claims about
protected host paths. The recorded eighteen cases passed, including original
success/denial preservation, fork/exec, constructor/concurrent calls, buffer
semantics and stale-marker refusal. Keep actual logs and input identities.

## 8. Resume the exact pending gates with honest evidence

Read the actual current records before launching. The QEMU run
`import-901-direct-fresh-r1` was intentionally interrupted after the user asked
for native alternatives. The tool reported130, the full lock was available,
and the wrapper's original partial record remains preserved; see its separate
`-interruption-042.json`. It is not a full pass. The d24 focused run genuinely
ended1 with example-proof errors. Candidate956c4b06 corrects proof names/rewrite
order without changing theorem statements; its own native record is separate.

Use new lowercase run IDs and never overwrite evidence. The native-bound runner
captures its own helper, compatibility source/library, compiler/dependencies,
source closure and genuine terminal results. From `pfds`:

```sh
python3 session/validation/run-native-validation.py full recovered-full-001 --fresh
python3 session/validation/run-native-validation.py focus recovered-focus-001
```

The current full route is bound to exact901 and invokes stock
`./check.sh --candidate HEAD --fresh --jobs 1`. The focused route is bound to
exact956c4b06 and the retained eleven targets. At most one full and one focused
wrapper may run concurrently. Freeze all inputs. Do not substitute another
candidate or change runtime/thread settings inside a recorded run.

Fresh mode reuses pinned dependency caches but builds project outputs in a
private temporary directory and removes them. It does not populate ordinary
project outputs or restore an old donor cache. A successful record remains
specific to its exact source/runtime inputs. Only after a successful full run:

```sh
python3 session/validation/run-native-validation.py verify recovered-verify-001 \
  --full-record recovered-full-001
```

The verifier reads the saved mode and receives no fresh/jobs flags. Both
independent formal review axes need the complete matching evidence. Repeat
immediate stock verification before accepting identical candidate bytes. All
runner records retain `acceptance: false`; acceptance is a separate decision.

A restored `running` record after workspace loss has unknown terminal outcome.
Do not reuse old process/session IDs or count partial output as completion.
The current full runner is901-specific. Chapter2 candidate99a29dc requires its
own correctly bound invocation, full check/audit, review and final verification
after prerequisites. Do not run old absolute-path Nix wrappers unchanged or
merge901 as though it were99's ancestor.

## 9. Continue the workstream and preserve the next handoff

The union is not complete. Chapter1 introductory accounting is accepted with
forward contracts still open; Chapter2 remains the earliest unaccepted
chapter. Later preparation is not algorithm or chapter acceptance. The
published book is absent in this recovery; retained inspections support the
current candidate checks, while new unresolved source/page questions need the
book reattached. The thesis identity and reacquisition URL are in current status.

Keep requirements, local tickets/coverage, exact source refs, complete reviews,
closed or explicitly partial run evidence, this runbook and helper source in
each checkpoint. Generate checkpoints with `session/checkpoint.py`, retain its
actual restoration result, expose/upload immediately, and save post-creation
receipts for the next checkpoint. Freeze writers or use an explicitly recorded
safe snapshot of ongoing work. Do not archive credentials, ordinary caches,
downloaded third-party binaries, or manuscripts as if they were authored source.

Historical Nix failures remain evidence, not a prohibition on the user's
permitted direct route. The supplied guide's optional Nix tests establish only
the stated client/local-derivation behavior, not a full conaled flake. Native
performance evidence and its limits are retained in
`native-performance-analysis-042.md`; the other agent's route comparison is
`environment-route-comparison-042.md`. No general speedup or completed whole-book
formalization is implied by an environment checkpoint.

## 10. Optional QEMU fallback

Use this only when intentionally choosing the emulated fallback. The user has
asked us to pursue faster native development. This section preserves the
previously tested route and its provenance; it is not the default native path.


The retained QEMU fallback uses the official Debian amd64 package
`1:7.2+dfsg-7+deb12u18+b3`; the executable reports QEMU7.2.22. This acquisition
was verified against the official HTTPS package index and exact digests. It
does not claim the separately established Ubuntu signature chain.

```sh
test ! -e toolchains/qemu-7.2-deb12u18
mkdir -p toolchains/qemu-7.2-deb12u18
curl --fail --location \
  https://deb.debian.org/debian/pool/main/q/qemu/qemu-user-static_7.2+dfsg-7+deb12u18+b3_amd64.deb \
  --output toolchains/downloads/qemu-user-static_7.2+dfsg-7+deb12u18+b3_amd64.deb
sha256sum --check <<'SHA256'
c3e3ba2bd87f8c5b9a5da5ef21b5a3b82d7c63b89dd448d9ddaa4eabc5b6e402  toolchains/downloads/qemu-user-static_7.2+dfsg-7+deb12u18+b3_amd64.deb
SHA256
dpkg-deb --fsys-tarfile \
  toolchains/downloads/qemu-user-static_7.2+dfsg-7+deb12u18+b3_amd64.deb \
  | tar --no-same-owner -xOf - ./usr/bin/qemu-x86_64-static \
      > toolchains/qemu-7.2-deb12u18/qemu-x86_64-static
sha256sum --check <<'SHA256'
8f2e8d5017b23a877fdf52e4021e6348bb5ad92306dd0d0615159ab6276da442  toolchains/qemu-7.2-deb12u18/qemu-x86_64-static
SHA256
chmod 0755 toolchains/qemu-7.2-deb12u18/qemu-x86_64-static
```

The package is 62603724 bytes. See `qemu-lean-smoke-041.json` for its actual
identity and working-runtime evidence. This extracts one executable and does
not install a system package or register a binary-format handler.

The supplied Ubuntu8.2.2 route has separately authenticated acquisition
evidence under `qemu-ubuntu-042/`. That is an alternative artifact, not the
selected runtime or an automatic replacement for this profile. Read
`environment-route-comparison-042.md` before considering a future change.


### Construct the optional QEMU profile

Check the exact original compiler executables before creating the profile:

```sh
sha256sum --check <<'SHA256'
bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38  toolchains/lean-4.35.0-linux/bin/lean
8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1  toolchains/lean-4.35.0-linux/bin/lake
5908f2917dcda5ed840e1ff5d6cdac5d104f9f6ca1ab1dc9f11d1c9fe220487e  toolchains/lean-4.35.0-linux/bin/leanir
SHA256
python3 session/environment/make-direct-toolchain-profile.py
python3 session/environment/run-direct-toolchain.py --describe
python3 session/environment/run-direct-toolchain.py -- lean --version
python3 session/environment/run-direct-toolchain.py -- lake --version
```

Expected genuine outputs:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

The builder stages a new `toolchains/lean-4.35.0-profile` and renames it into
place. It deliberately refuses an existing profile. Use the read-only
`--describe` command to verify an existing one; do not blindly rerun creation.
The launcher verifies recorded executable, wrapper and profile identities.

Both Lean and Lake are byte-identical regular copies inside the same profile.
A symlink back to the originals would make executable-path discovery leave
that profile. Each required child entrypoint needs its own wrapper because
QEMU does not automatically emulate a child after `execve`. Our profile also
wraps `leanir`; this is structural coverage, not a claim that a postponed
compilation workload has been validated.

Generated wrappers contain absolute paths. After relocation, reconstruct the
profile from the included source and reacquired distributions. Do not carry
old generated wrappers into a new root. No download, generated profile, or
excluded temporary helper is a hidden prerequisite for the included source.

The QEMU launcher sets PATH, library paths, sysroot, explicit Lake/Mathlib
cache paths, TMPDIR and `LEAN_NUM_THREADS=1`. It does not clear every inherited
selector. Before a new run, inspect the presence of `LEAN`, `LEAN_PATH`,
`LEAN_AR`, `LEAN_CC`, `LEAN_GITHASH`, `LAKE_HOME`, `LAKE_OVERRIDE_LEAN` and
`LEAN_WORKER_PATH` in the launching shell. Use a dedicated clean shell or
explicitly clear accidental selectors there. Do not alter any running job's
inputs. Preserve the stock check's refusal of unsupported compiler overrides.
Do not unset host permission or authentication machinery.


