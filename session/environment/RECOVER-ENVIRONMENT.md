# Recover the PFDS environment without the old workspace or chat

This is the takeover entry point for the **PFDS book/thesis union** workstream.
It supplements the complete helper sources shipped in this checkpoint. Read
`../STATUS.md`, `../requirements/REQUEST.md`, `REQUEST-union-v2.md`,
`REQUEST-direct-toolchain-041.md`, and `REQUEST-environment-handoff-042.md`
before continuing. The last three request files are in `../requirements/`.

Nix is optional under the user's explicit exception. Exact Lean/dependency
pins, source policy, proof audits, independent reviews, final verification,
chapter order, local tickets, and immediate durable checkpoints still apply.
Do not push branches or create GitHub tickets.

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

The verified route is x86-64 Linux with glibc. Required tools: Python3.11 or
later, Git, curl with HTTPS, `sha256sum`, GNU tar with zstd support, and
`dpkg-deb`. This host reports Python3.12.14, Git2.51.1, curl8.5.0, glibc2.39
and nine CPUs. These are observations, not new project pins. Another platform
requires the corresponding artifacts and genuine new validation.

Native Lean startup fails here because `/proc/<own-pid>/exe` is unavailable.
The reviewed QEMU user-mode route supplies the guest's own executable metadata.
It needs no privileged installation, host mount, tracing facility, compiler
patch, or host permission change. `LEAN_SYSROOT` alone does not fix the native
startup call. The original binaries remain unchanged.

Use a dedicated Bash shell for the acquisition blocks and stop on errors:

```sh
set -euo pipefail
cd /absolute/new/pfds
PFDS_ROOT="$(pwd -P)"
mkdir -p toolchains/downloads session/tools
```

Do not replace `HOME` or `CODEX_HOME`. The checked launcher scopes toolchain,
cache and temporary paths to each invoked command.

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

## 4. Acquire the currently reviewed QEMU binary

The current profile uses the official Debian amd64 package
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

## 5. Construct and verify the profile

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

The current launcher sets PATH, library paths, sysroot, explicit Lake/Mathlib
cache paths, TMPDIR and `LEAN_NUM_THREADS=1`. It does not clear every inherited
selector. Before a new run, inspect the presence of `LEAN`, `LEAN_PATH`,
`LEAN_AR`, `LEAN_CC`, `LEAN_GITHASH`, `LAKE_HOME`, `LAKE_OVERRIDE_LEAN` and
`LEAN_WORKER_PATH` in the launching shell. Use a dedicated clean shell or
explicitly clear accidental selectors there. Do not alter any running job's
inputs. Preserve the stock check's refusal of unsupported compiler overrides.
Do not unset host permission or authentication machinery.

## 6. Restore every dependency at the manifest revision

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

## 7. Materialize the current candidates and private build directories

Consult current status first. At this handoff, the next full candidate is
`901f734161920a76f3b399a575805b9a1d31e971` and the focused candidate is
`d24c443ba22019613b1ce646d6eed7279c791ad6`. In a new restoration where their
directories do not exist:

```sh
git -C conaled worktree add --detach "$PFDS_ROOT/import-correction-r3" \
  901f734161920a76f3b399a575805b9a1d31e971
git -C conaled worktree add --detach "$PFDS_ROOT/signed-potential" \
  d24c443ba22019613b1ce646d6eed7279c791ad6
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
    ("signed-potential", "d24c443ba22019613b1ce646d6eed7279c791ad6"),
):
    checkout = root / name
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip() == expected
    assert not subprocess.check_output(["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=checkout, text=True)
    lake = checkout / ".lake"
    lake.mkdir(exist_ok=True)
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

## 8. Check the public compiler path, then obtain the dependency cache

From `pfds`, run the supplied real smoke tests with new report filenames:

```sh
python3 session/environment/test-direct-toolchain.py \
  --workspace "$PFDS_ROOT" \
  --runner "$PFDS_ROOT/session/environment/run-direct-toolchain.py" \
  --report "$PFDS_ROOT/session/validation/recovery-cli-new.json"
python3 session/environment/test-direct-lake-build.py \
  --workspace "$PFDS_ROOT" \
  --runner "$PFDS_ROOT/session/environment/run-direct-toolchain.py" \
  --report "$PFDS_ROOT/session/validation/recovery-lake-new.json"
```

These test the exact versions, a valid theorem with no axioms, rejection of a
false theorem, Lake's compiler path, and native compilation/linking/execution.
They create their temporary parents after a cold recovery. They are not a
full project acceptance check. Choose unused report names to preserve history.

Initialize the shared dependency outputs once from `import-correction-r3`:

```sh
cd "$PFDS_ROOT/import-correction-r3"
python3 "$PFDS_ROOT/session/environment/run-direct-toolchain.py" -- lake build cache
python3 "$PFDS_ROOT/session/environment/run-direct-toolchain.py" -- lake env \
  "$PFDS_ROOT/toolchains/qemu-7.2-deb12u18/qemu-x86_64-static" \
  "$PFDS_ROOT/dependency-store-041/mathlib/.lake/build/bin/cache" get
cd "$PFDS_ROOT"
```

The cache executable also calls `IO.appDir`, so it needs explicit guest
execution inside `lake env`. Ordinary `lake exe cache get` alone does not
provide that child boundary on this host. Keep the bundled `leantar` and
default cache scope/trust policy. The recorded successful run downloaded and
decompressed 9031 files; a future run must establish its own real exit result.
Recheck all nine dependency heads and clean statuses afterward.

## 9. Resume the exact pending gates with honest evidence

Read the latest run records before launching. In this workspace, one fresh
full check and one focused wrapper were launched after checkpoint041. Their
current terminal state belongs to the actual JSON/logs, not this static guide.
The focused `signed-d24-direct-r1` run subsequently ended with exit 1 at
2026-11-03T16:00:25Z. Its unchanged-input record identifies actual errors in
`Examples.SignedPotential` and `Examples.PotentialTransport`. Preserve that
failure; corrected source needs its own candidate and applicable checks.
A `running` record restored after workspace loss has an unknown terminal
outcome. Do not reuse old process/session IDs or turn partial module output
into a full pass.

Use new lowercase run IDs, never overwrite existing evidence. From `pfds`:

```sh
python3 session/validation/run-direct-validation.py full new-full-run-id --fresh
python3 session/validation/run-direct-validation.py focus new-focus-run-id
```

The full route runs stock `./check.sh --candidate HEAD --fresh --jobs 1` at
exact901. The focused route builds the retained eleven targets at exactd24.
At most one full and one focused wrapper may run concurrently. Keep compiler
inputs frozen. The approved launcher currently sets `LEAN_NUM_THREADS=1`.
The attachment's four-thread command is not a permission to change a live
run or silently bypass recorded resource/evidence settings.

Fresh mode compiles project outputs into a private temporary directory and
removes them. It reuses dependency caches but does not populate ordinary
project outputs for a later warm handoff. A successful fresh check therefore
does not recreate the old donor cache or validate old migration receipts.

Only after a genuine successful full record, use:

```sh
python3 session/validation/run-direct-validation.py verify new-verify-run-id \
  --full-record new-full-run-id
```

The stock verifier receives no fresh/jobs flags; it reads the saved record's
mode. Both independent formal review axes still need the matching complete
evidence. Repeat immediate final verification before accepting identical
candidate bytes. Every runner record keeps `acceptance: false`; acceptance is
a separate reviewed decision. Failed or interrupted evidence remains preserved.

The current full runner is901-specific. Chapter2 candidate99a29dc needs its
own correctly bound invocation, full check/audit, review reconciliation and
final verification after prerequisite acceptance. Never run the old absolute-path
Nix-era wrappers unchanged or merge901 as though it were99's ancestor.

## 10. Continue the workstream and preserve the next handoff

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

Historical Nix failures remain evidence, not a current prohibition on the
user-authorized direct route. The optional Nix experiment in the comparison
guide proves only its stated client/local-derivation tests, not a complete
conaled flake environment. No native interposition alternative is selected;
the separate own-process metadata feasibility probe is research only.
