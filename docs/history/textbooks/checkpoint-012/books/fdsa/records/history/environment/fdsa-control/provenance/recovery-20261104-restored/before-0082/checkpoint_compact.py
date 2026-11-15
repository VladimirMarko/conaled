#!/usr/bin/env python3
"""Current recovery archive with one explicitly pinned public baseline asset."""
from pathlib import Path
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import shutil
import subprocess
import tarfile
import tempfile

ASSET = {
    "path": "docs/history/algorithm-design-haskell/checkpoint-233.zip",
    "size_bytes": 67920919,
    "sha256": "8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63",
    "git_blob": "e887c040b8c9902c6d9d38672ca54dd84937959d",
    "url": "https://raw.githubusercontent.com/VladimirMarko/conaled/7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd/docs/history/algorithm-design-haskell/checkpoint-233.zip",
}
EXCLUDED = {"docs/history/algorithm-design-haskell/.checkpoint-233.zip.n7UlkJ"}

def git(repo, *args, binary=False):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=not binary)

def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def source_fingerprint(repo):
    """Detect changed bytes even when porcelain status remains unchanged."""
    if git(repo, "ls-files", "--unmerged", "-z"):
        raise SystemExit("Resolve unmerged index entries before checkpointing")
    visible = set(git(repo, "diff", "--cached", "--name-only", "-z", "--ita-visible-in-index").split("\0"))
    invisible = set(git(repo, "diff", "--cached", "--name-only", "-z", "--ita-invisible-in-index").split("\0"))
    if visible != invisible:
        raise SystemExit("Stage or unstage intent-to-add entries before checkpointing")
    files = []
    for relative in sorted(p for p in git(repo, "ls-files", "--others", "--exclude-standard", "-z").split("\0")
                           if p and p not in EXCLUDED):
        path = repo / relative
        meta = path.lstat()
        files.append({"path": relative, "mode": meta.st_mode,
                      "content": os.readlink(path) if path.is_symlink() else digest(path)})
    return {"staged": hashlib.sha256(git(repo, "diff", "--cached", "--binary", binary=True)).hexdigest(),
            "unstaged": hashlib.sha256(git(repo, "diff", "--binary", binary=True)).hexdigest(),
            "untracked": files}

def worktrees(repo):
    result = []
    for block in git(repo, "worktree", "list", "--porcelain").strip().split("\n\n"):
        fields = dict(line.split(" ", 1) if " " in line else (line, "") for line in block.splitlines())
        path = Path(fields["worktree"])
        result.append({"path": str(path), "head": fields["HEAD"],
                       "branch_ref": fields.get("branch"),
                       "status": git(path, "status", "--porcelain=v1", "--untracked-files=all"),
                       "source_fingerprint": source_fingerprint(path)})
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    args = parser.parse_args()
    if not args.name.replace("-", "").replace("_", "").isalnum():
        parser.error("Invalid checkpoint name")
    control = Path(__file__).resolve().parent
    workspace = control.parent
    repo = workspace / "conaled"
    out = workspace / "checkpoints"
    out.mkdir(exist_ok=True)
    archive = out / (args.name + ".tar.gz")
    if archive.exists():
        raise SystemExit("Refusing to overwrite a checkpoint")
    before = worktrees(repo)
    refs = [{"oid": parts[0], "ref": parts[1], "symref": parts[2]} for parts in
            (line.split(" ", 2) for line in git(repo, "for-each-ref",
             "--format=%(objectname) %(refname) %(symref)").splitlines())]
    heads = [w["head"] for w in before]
    objects = set(line.split(" ", 1)[0] for line in
                  git(repo, "rev-list", "--objects", "--all", *heads).splitlines())
    omitted = [ASSET] if ASSET["git_blob"] in objects else []
    for item in omitted:
        objects.remove(item["git_blob"])
        original = repo / item["path"]
        if original.stat().st_size != item["size_bytes"] or digest(original) != item["sha256"]:
            raise SystemExit("Externalized asset no longer matches its pin")
    with tempfile.TemporaryDirectory(prefix="fdsa-recovery-", dir=workspace) as temp:
        stage = Path(temp) / args.name
        stage.mkdir()
        with (stage / "source.pack").open("wb") as stream:
            subprocess.run(["git", "-C", str(repo), "pack-objects", "--stdout", "--compression=9"],
                           input=("\n".join(sorted(objects)) + "\n").encode(), stdout=stream, check=True)
        states = []
        for index, wt in enumerate(before):
            path = Path(wt["path"])
            label = "conaled" if path == repo else path.name
            relative = f"worktrees/{index:03d}"
            dest = stage / relative
            dest.mkdir(parents=True)
            (dest / "staged.patch").write_bytes(git(path, "diff", "--cached", "--binary", binary=True))
            (dest / "unstaged.patch").write_bytes(git(path, "diff", "--binary", binary=True))
            untracked = [p for p in git(path, "ls-files", "--others", "--exclude-standard", "-z").split("\0")
                         if p and p not in EXCLUDED]
            with tarfile.open(dest / "untracked.tar", "w") as tar:
                for p in untracked:
                    tar.add(path / p, arcname=p, recursive=False)
            states.append({**wt, "name": label, "payload": relative, "untracked": untracked})
        shutil.copytree(control, stage / "fdsa-control", ignore=shutil.ignore_patterns("__pycache__"))
        manifest = {"format": 2, "checkpoint": args.name,
                    "created_utc": datetime.now(timezone.utc).isoformat(),
                    "repository": "https://github.com/VladimirMarko/conaled.git",
                    "refs": refs, "worktrees": states, "external_assets": omitted,
                    "included_git_objects": len(objects),
                    "excluded_unrelated_untracked": sorted(EXCLUDED),
                    "scope": "Whole FDSA book; actual acceptance is in fdsa-control/STATUS.md",
                    "excluded_regenerable": ["compiler/runtime installation and dependency caches",
                                               "copyrighted book PDF and extracted text"]}
        (stage / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
        (stage / "RECOVER.md").write_text("""# Recover current FDSA work

This compact archive preserves all task source, every reachable Git commit/ref,
current worktree edits, local tickets, requirements, reviews, evidence, and the
complete supplied unified native environment kit. It requires no earlier task
checkpoint or conversation. It is NOT a completely offline archive: one unchanged
67,920,919-byte public baseline ZIP is externalized with exact byte and Git pins.
The restore downloads it from its immutable URL, or accepts an exact local copy.

1. Extract this archive and verify `sha256sum -c SHA256SUMS`.
2. Run `python3 fdsa-control/restore_compact.py /absolute/new/workspace`.
   The destination must be absent or empty. For an offline baseline-asset seed,
   append `--asset /absolute/path/to/checkpoint-233.zip`. A mismatched asset fails.
   Restore inserts the verified blob, installs the object pack, checks every ref
   and Git integrity, then recreates source worktrees and their saved edits.
3. Read `fdsa-control/REQUEST.md`, `CURRENT.md`, `STATUS.md`, and `tickets/INDEX.md`.
   Partial/running logs and environment smoke tests are not chapter acceptance.
4. Follow `fdsa-control/ENVIRONMENT.md`. The unified native kit is included in
   `fdsa-control/tooling/unified-native-kit-4.35.0/`; acquire its exact compiler and
   dependencies, then resume the first unaccepted chapter and preserved reviews.
5. Keep changes and tickets local. No GitHub mutation/push is authorized.

The original book PDF is not redistributed; its URL, edition, size, and SHA-256
are recorded in source provenance. Historical process IDs are not live evidence.
The externalized ZIP is pre-existing public repository material, not new task
work. All task recovery information remains in this archive; there is no delta
chain and no dependence on previous recovery checkpoints.
""")
        files = sorted(p for p in stage.rglob("*") if p.is_file())
        (stage / "SHA256SUMS").write_text("".join(f"{digest(p)}  {p.relative_to(stage)}\n" for p in files))
        if before != worktrees(repo):
            raise SystemExit("Source changed during capture; retry after stabilizing writers")
        if refs != [{"oid": p[0], "ref": p[1], "symref": p[2]} for p in
                    (line.split(" ", 2) for line in git(repo, "for-each-ref",
                     "--format=%(objectname) %(refname) %(symref)").splitlines())]:
            raise SystemExit("Refs changed during capture")
        with tarfile.open(archive, "w:gz", compresslevel=6) as tar:
            tar.add(stage, arcname=args.name)
    result = {"file": str(archive), "sha256": digest(archive), "size_bytes": archive.stat().st_size,
              "format": 2, "worktrees": states, "external_asset_bytes": sum(a["size_bytes"] for a in omitted)}
    (out / (args.name + ".json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))

if __name__ == "__main__":
    main()
