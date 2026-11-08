#!/usr/bin/env python3
"""Export a frozen source closure and private artifacts for one trial arm.

Coordinator-only. Run with the repository's pinned Python through direnv.
No task solution is generated. Records are kept outside the public handoff.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import shutil
import subprocess
import time


CONFIG = (".envrc", "flake.nix", "flake.lock", "lean-toolchain",
          "lakefile.toml", "lake-manifest.json")
WRAPPER = "experiments/dependent-author-trial/check_attempt.py"


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def digest(data):
    return sha256(data).hexdigest()


def uncomment(text):
    # Lean supports nested block comments. Preserve newlines and token spacing.
    result = []
    depth = 0
    index = 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == "/-":
            depth += 1
            result.append("  ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            result.append("  ")
            index += 2
        elif not depth and pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        else:
            result.append(text[index] if not depth or text[index] == "\n" else " ")
            index += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(result)


def imports(data):
    source = uncomment(data.decode())
    for match in re.finditer(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)",
                             source, re.MULTILINE):
        for name in match.group(1).split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", name):
                raise ValueError(f"Unsupported import token: {name}")
            yield name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--donor", required=True, type=Path)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--entry", action="append", required=True)
    parser.add_argument("--destination", required=True, type=Path)
    parser.add_argument("--record", required=True, type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    start = datetime.now(timezone.utc).isoformat()
    repo, donor = args.repo.resolve(), args.donor.resolve()
    root = args.destination.absolute()
    if root.exists() or args.record.exists():
        raise ValueError("Destination and record must be new")
    if root.resolve() != root:
        raise ValueError("Handoff path must not use symlinks")
    revision = git(repo, "rev-parse", f"{args.revision}^{{commit}}").decode().strip()
    tracked = set(git(repo, "ls-tree", "-r", "--name-only", revision).decode().splitlines())
    modules = {}
    external = set()
    pending = list(args.entry)
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        name = module.replace(".", "/") + ".lean"
        if name not in tracked:
            raise ValueError(f"Entrypoint or local dependency absent: {module}")
        data = git(repo, "show", f"{revision}:{name}")
        if not (donor / name).is_file() or (donor / name).read_bytes() != data:
            raise ValueError(f"Donor source does not match frozen source: {name}")
        modules[module] = data
        for dependency in imports(data):
            dep_name = dependency.replace(".", "/") + ".lean"
            if dep_name in tracked:
                pending.append(dependency)
            else:
                external.add(dependency)
    # Validate all inputs before creating the destination.
    config = {name: git(repo, "show", f"{revision}:{name}") for name in CONFIG}
    for name, data in config.items():
        if (donor / name).read_bytes() != data:
            raise ValueError(f"Donor configuration differs: {name}")
    wrapper = git(repo, "show", f"{revision}:{WRAPPER}")
    artifacts = {}
    for module in sorted(modules):
        stem = Path(module.replace(".", "/"))
        required = donor / ".lake/build/lib/lean" / stem.with_suffix(".olean")
        if not required.is_file():
            raise ValueError(f"Missing compiled module: {module}")
        # Direct Lean checks need compiled imports, not Lake trace logs or C
        # outputs. Trace logs can mention private donor checkout paths.
        parent = donor / ".lake/build/lib/lean" / stem.parent
        for source in parent.glob(stem.name + ".olean*"):
            if source.is_file():
                name = str(source.relative_to(donor))
                artifacts[name] = digest(source.read_bytes())
    packages = (donor / ".lake/packages").resolve()
    dependency_commits = {}
    manifest = json.loads(config["lake-manifest.json"])
    for package in manifest["packages"]:
        checkout = packages / package["name"]
        commit = git(checkout, "rev-parse", "HEAD").decode().strip()
        if commit != package["rev"]:
            raise ValueError(f"Unpinned dependency: {package['name']}")
        if git(checkout, "status", "--porcelain", "--untracked-files=no").strip():
            raise ValueError(f"Modified dependency: {package['name']}")
        dependency_commits[package["name"]] = commit
    root.mkdir(parents=True)
    for name, data in config.items():
        (root / name).write_bytes(data)
    (root / "check_attempt.py").write_bytes(wrapper)
    for module, data in modules.items():
        target = root / (module.replace(".", "/") + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    for name in artifacts:
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(donor / name, target, follow_symlinks=True)
    (root / ".lake").mkdir(exist_ok=True)
    subprocess.run(["cp", "-a", "--reflink=auto", str(packages),
                    str(root / ".lake/packages")], check=True)
    links = [str(path.relative_to(root)) for path in (root / ".lake/packages").rglob("*")
             if path.is_symlink()]
    for name in links:
        if not (root / name).resolve().is_relative_to(root / ".lake/packages"):
            raise ValueError(f"Dependency link escapes private copy: {name}")
    (root / "attempts").mkdir()
    record = {
        "schema": 1, "revision": revision, "donor_revision":
            git(donor, "rev-parse", "HEAD").decode().strip(),
        "start": start, "finish": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "destination": str(root), "entrypoints": args.entry,
        "modules": {name: digest(data) for name, data in sorted(modules.items())},
        "external_imports": sorted(external),
        "configuration": {name: digest(data) for name, data in config.items()},
        "wrapper_sha256": digest(wrapper), "project_artifacts": artifacts,
        "dependency_commits": dependency_commits,
        "dependency_copy": "cp -a --reflink=auto; private files; internal links only",
        "dependency_internal_links": links,
        "project_history": "not copied",
        "status": "closure-prepared; public overlay and final freeze pending",
    }
    args.record.parent.mkdir(parents=True, exist_ok=True)
    args.record.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"Prepared {len(modules)} local modules and {len(artifacts)} artifacts: {root}")


if __name__ == "__main__":
    main()
