#!/usr/bin/env python3
"""Acquire the exact guide-specified QEMU package without installing it."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import lzma
from pathlib import Path
import shutil
import subprocess
import tarfile


PROVENANCE = Path(__file__).resolve().parent
WORKSPACE = PROVENANCE.parents[3]
ARTIFACTS = WORKSPACE / "bootstrap/qemu-user"
BASE = "https://archive.ubuntu.com/ubuntu/"
INDEX_PATH = "universe/binary-amd64/Packages.xz"
PACKAGE_PATH = "pool/universe/q/qemu/qemu-user-static_8.2.2+ds-0ubuntu1.18_amd64.deb"
PACKAGE_SHA256 = "5bb397f66063efa349f6fd5cb3b68cd96f29edd0994e4ba5115cf0859a716bf0"
EXECUTABLE_SHA256 = "90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0"
KEYRING = Path("/usr/share/keyrings/ubuntu-archive-keyring.gpg")
COMMANDS: list[dict] = []


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def command(args: list[str]) -> dict:
    started = now()
    result = subprocess.run(args, capture_output=True, text=True)
    record = {"command": args, "started_at": started, "finished_at": now(),
              "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
    COMMANDS.append(record)
    if result.returncode:
        raise RuntimeError(f"Command exited {result.returncode}: {args!r}; {result.stderr}")
    return record


def download(url: str, path: Path) -> None:
    if path.exists():
        raise RuntimeError(f"Refusing to replace an existing acquisition input: {path}")
    command(["curl", "--fail", "--location", "--retry", "2", "--connect-timeout", "30",
             "--max-time", "240", "--silent", "--show-error", url, "--output", str(path)])


def main() -> None:
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    evidence = PROVENANCE / "evidence"
    evidence.mkdir(exist_ok=True)
    gpg_home = WORKSPACE / "runtime-config/qemu-auth-gpgv"
    gpg_home.mkdir(parents=True, exist_ok=True)
    release = PROVENANCE / "InRelease"
    index = PROVENANCE / "Packages.xz"
    deb = ARTIFACTS / Path(PACKAGE_PATH).name
    report: dict = {"started_at": now(), "guide_package_version": "1:8.2.2+ds-0ubuntu1.18",
                    "host_keyring": str(KEYRING), "commands": COMMANDS}
    try:
        copied_keyring = evidence / "ubuntu-archive-keyring.gpg"
        shutil.copyfile(KEYRING, copied_keyring)
        report["host_keyring_sha256"] = digest(KEYRING)
        assert digest(copied_keyring) == report["host_keyring_sha256"]
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = [pool.submit(download, url, path) for url, path in [
                (BASE + "dists/noble-updates/InRelease", release),
                (BASE + "dists/noble-updates/" + INDEX_PATH, index),
                (BASE + PACKAGE_PATH, deb),
            ]]
            for future in futures:
                future.result()
        signature = command(["gpgv", "--homedir", str(gpg_home), "--status-fd", "1",
                             "--keyring", str(KEYRING), str(release)])
        report["signature"] = signature
        release_text = release.read_text()
        in_sha256 = False
        index_entry = None
        for line in release_text.splitlines():
            if line == "SHA256:":
                in_sha256 = True
                continue
            if in_sha256 and line and not line.startswith(" "):
                in_sha256 = False
            if in_sha256:
                fields = line.split()
                if len(fields) == 3 and fields[2] == INDEX_PATH:
                    index_entry = {"sha256": fields[0], "size": int(fields[1]), "path": fields[2]}
        assert index_entry is not None, "The verified release does not identify the required index"
        assert digest(index) == index_entry["sha256"]
        assert index.stat().st_size == index_entry["size"]
        report["authenticated_index"] = index_entry
        report["release_headers"] = [line for line in release_text.splitlines()
                                     if line.startswith(("Date:", "Valid-Until:", "Suite:", "Codename:", "Origin:"))]
        package = None
        for stanza in lzma.decompress(index.read_bytes()).decode().split("\n\n"):
            fields = dict(line.split(": ", 1) for line in stanza.splitlines()
                          if line and not line.startswith(" ") and ": " in line)
            if (fields.get("Package") == "qemu-user-static" and
                    fields.get("Version") == "1:8.2.2+ds-0ubuntu1.18" and
                    fields.get("Architecture") == "amd64"):
                assert package is None, "Duplicate package stanza"
                package = fields
        assert package is not None, "Fresh authenticated index lacks the guide's exact package version"
        assert package["Filename"] == PACKAGE_PATH
        assert package["SHA256"] == PACKAGE_SHA256
        assert digest(deb) == package["SHA256"]
        assert deb.stat().st_size == int(package["Size"])
        (PROVENANCE / "official-package-metadata.json").write_text(json.dumps(package, indent=2) + "\n")
        report["authenticated_package"] = package
        report["package_file"] = str(deb)
        # Stream the package's tar payload and copy only two explicitly named
        # regular files. No package installation or maintainer script runs.
        extracted = {"./usr/bin/qemu-x86_64-static": ARTIFACTS / "bin/qemu-x86_64-static",
                     "./usr/share/doc/qemu-user-static/copyright": ARTIFACTS / "copyright"}
        extraction_started = now()
        proc = subprocess.Popen(["dpkg-deb", "--fsys-tarfile", str(deb)], stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        found = set()
        assert proc.stdout is not None
        with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
            for member in archive:
                if member.name in extracted:
                    assert member.isfile(), f"Expected regular archive member: {member.name}"
                    target = extracted[member.name]
                    if target.exists():
                        raise RuntimeError(f"Refusing to replace extracted file: {target}")
                    target.parent.mkdir(parents=True, exist_ok=True)
                    stream = archive.extractfile(member)
                    assert stream is not None
                    with target.open("xb") as destination:
                        shutil.copyfileobj(stream, destination)
                    target.chmod(0o755 if target.name == "qemu-x86_64-static" else 0o644)
                    found.add(member.name)
        stderr = proc.stderr.read().decode() if proc.stderr else ""
        code = proc.wait()
        COMMANDS.append({"command": ["dpkg-deb", "--fsys-tarfile", str(deb)],
                         "started_at": extraction_started, "finished_at": now(), "exit_code": code,
                         "stderr": stderr, "selected_regular_members": sorted(found)})
        assert code == 0, stderr
        assert found == set(extracted)
        executable = ARTIFACTS / "bin/qemu-x86_64-static"
        assert digest(executable) == EXECUTABLE_SHA256
        report["extracted_executable"] = {"path": str(executable), "sha256": digest(executable),
                                          "size": executable.stat().st_size}
        report["authentication_inputs"] = [{"path": str(path), "sha256": digest(path),
                                             "size": path.stat().st_size}
                                            for path in [release, index, copied_keyring]]
        report["result"] = "authenticated-and-extracted"
    except BaseException as error:
        report["result"] = "failed"
        report["error"] = repr(error)
        raise
    finally:
        report["finished_at"] = now()
        (PROVENANCE / "qemu-acquisition.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({key: report.get(key) for key in ["result", "error", "authenticated_index", "extracted_executable"]}, indent=2), flush=True)


if __name__ == "__main__":
    main()
