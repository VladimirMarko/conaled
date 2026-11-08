#!/usr/bin/env python3
"""Add coordinator-approved public files, then freeze one prepared handoff.

Each overlay is a directory whose contents are copied at the handoff root.
Overwriting an existing source or exposing symlinks is rejected. This script
never compiles or solves the task. Compile any added specification module before
freezing and record that coordinator validation separately.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import shutil


EXCLUDED = {".git", ".lake", ".direnv", "attempts", "__pycache__"}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--handoff", required=True, type=Path)
    parser.add_argument("--preparation", required=True, type=Path)
    parser.add_argument("--overlay", action="append", default=[], type=Path)
    parser.add_argument("--record", required=True, type=Path)
    args = parser.parse_args()
    root = args.handoff.absolute()
    if root.resolve() != root or not root.is_dir():
        raise ValueError("Expected a prepared unlinked handoff directory")
    if (root / "public-manifest.json").exists() or args.record.exists():
        raise ValueError("Refusing to replace a frozen manifest or record")
    preparation = json.loads(args.preparation.read_text())
    if preparation["destination"] != str(root):
        raise ValueError("Preparation record belongs to another handoff")
    overlays = {}
    for overlay in args.overlay:
        for source in sorted(overlay.rglob("*")):
            relative = source.relative_to(overlay)
            if source.is_symlink() or relative.parts[0] in EXCLUDED:
                raise ValueError(f"Forbidden overlay input: {source}")
            if source.is_dir():
                continue
            if str(relative) == "public-manifest.json":
                raise ValueError("Overlay cannot provide manifest")
            target = root / relative
            if target.exists() or str(relative) in overlays:
                raise ValueError(f"Overlay cannot replace input: {relative}")
            overlays[str(relative)] = source
    for name, source in overlays.items():
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    files = {}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if relative.parts[0] in EXCLUDED:
            continue
        if path.is_symlink():
            raise ValueError(f"Linked public input: {relative}")
        if path.is_file():
            files[str(relative)] = digest(path)
    modules = sorted(name[:-5].replace("/", ".") for name in files if name.endswith(".lean"))
    for module in modules:
        compiled = root / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        if not compiled.is_file():
            raise ValueError(f"Public module requires coordinator compilation: {module}")
    for module, expected in preparation["modules"].items():
        source = module.replace(".", "/") + ".lean"
        if files.get(source) != expected:
            raise ValueError(f"Prepared source changed: {source}")
    manifest = {"schema": 1, "files": files, "allowed_imports": modules}
    (root / "public-manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    record = {
        "schema": 1, "time": datetime.now(timezone.utc).isoformat(),
        "handoff": str(root), "preparation_sha256": digest(args.preparation),
        "manifest_sha256": digest(root / "public-manifest.json"),
        "overlay": {name: digest(source) for name, source in overlays.items()},
        "public_file_count": len(files), "allowed_module_count": len(modules),
    }
    args.record.parent.mkdir(parents=True, exist_ok=True)
    args.record.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"Frozen {len(files)} public files; {len(modules)} local modules: {root}")


if __name__ == "__main__":
    main()
