#!/usr/bin/env python3
"""Restore an extracted trusted format-2 checkpoint into an empty workspace."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

def run(*args, **kwargs):
    return subprocess.run(list(args), check=True, **kwargs)

def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()

def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def contained(root, relative):
    path = (root / relative).resolve()
    if not path.is_relative_to(root):
        raise SystemExit("Unsafe archive path")
    return path

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--asset", type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent.parent
    target = args.destination.resolve()
    if target.exists() and any(target.iterdir()):
        raise SystemExit("Destination must be absent or empty")
    for line in (source / "SHA256SUMS").read_text().splitlines():
        expected, relative = line.split("  ", 1)
        if digest(contained(source, relative)) != expected:
            raise SystemExit("Checksum mismatch: " + relative)
    manifest = json.loads((source / "MANIFEST.json").read_text())
    if manifest["format"] != 2:
        raise SystemExit("Unsupported checkpoint format")
    target.mkdir(parents=True, exist_ok=True)
    repo = target / "conaled"
    run("git", "init", "--quiet", str(repo))
    with tempfile.TemporaryDirectory(prefix="restore-assets-", dir=target) as temp:
        for item in manifest["external_assets"]:
            asset = args.asset.resolve() if args.asset else Path(temp) / item["git_blob"]
            if args.asset is None:
                with urllib.request.urlopen(item["url"], timeout=60) as response, asset.open("wb") as out:
                    shutil.copyfileobj(response, out)
            if asset.stat().st_size != item["size_bytes"] or digest(asset) != item["sha256"]:
                raise SystemExit("External baseline asset size/SHA-256 mismatch")
            actual = git(repo, "hash-object", "-w", str(asset))
            if actual != item["git_blob"]:
                raise SystemExit("External baseline asset Git identity mismatch")
        with (source / "source.pack").open("rb") as pack:
            run("git", "-C", str(repo), "index-pack", "--strict", "--stdin", stdin=pack, stdout=subprocess.DEVNULL)
    for ref in manifest["refs"]:
        run("git", "-C", str(repo), "update-ref", "--no-deref", ref["ref"], ref["oid"])
    for ref in manifest["refs"]:
        if ref["symref"]:
            run("git", "-C", str(repo), "symbolic-ref", ref["ref"], ref["symref"])
    main_state = next(w for w in manifest["worktrees"] if w["name"] == "conaled")
    if main_state["branch_ref"]:
        run("git", "-C", str(repo), "symbolic-ref", "HEAD", main_state["branch_ref"])
    else:
        run("git", "-C", str(repo), "update-ref", "--no-deref", "HEAD", main_state["head"])
    run("git", "-C", str(repo), "reset", "--hard", "--quiet", main_state["head"])
    run("git", "-C", str(repo), "remote", "add", "origin", manifest["repository"])
    for wt in manifest["worktrees"]:
        checkout = contained(target, wt["name"])
        if checkout != repo:
            run("git", "-C", str(repo), "worktree", "add", "--detach", str(checkout), wt["head"], stdout=subprocess.DEVNULL)
            if wt["branch_ref"]:
                run("git", "-C", str(checkout), "symbolic-ref", "HEAD", wt["branch_ref"])
        payload = contained(source, wt["payload"])
        for filename, extra in [("staged.patch", ["--index"]), ("unstaged.patch", [])]:
            patch = payload / filename
            if patch.stat().st_size:
                run("git", "-C", str(checkout), "apply", *extra, str(patch))
        with tarfile.open(payload / "untracked.tar") as tar:
            tar.extractall(checkout, filter="data")
        if git(checkout, "rev-parse", "HEAD") != wt["head"]:
            raise SystemExit("Worktree HEAD mismatch")
        expected_status = "\n".join(line for line in wt["status"].splitlines()
                                    if line[3:] not in manifest["excluded_unrelated_untracked"])
        actual_status = git(checkout, "status", "--porcelain=v1", "--untracked-files=all")
        if actual_status != expected_status.strip():
            raise SystemExit("Worktree status mismatch: " + wt["name"])
    for ref in manifest["refs"]:
        if git(repo, "rev-parse", ref["ref"]) != ref["oid"]:
            raise SystemExit("Ref mismatch: " + ref["ref"])
    run("git", "-C", str(repo), "fsck", "--full", "--no-reflogs")
    shutil.copytree(source / "fdsa-control", target / "fdsa-control")
    print(json.dumps({"restored": str(target), "checkpoint": manifest["checkpoint"],
                      "refs": len(manifest["refs"]), "worktrees": len(manifest["worktrees"]),
                      "acceptance": "Read fdsa-control/STATUS.md; recovery does not imply acceptance."}))

if __name__ == "__main__":
    main()
