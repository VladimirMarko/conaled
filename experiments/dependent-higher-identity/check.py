#!/usr/bin/env python3
"""Fresh source check against the preserved Myers checkpoint's exact toolchain."""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tarfile
from datetime import datetime, timezone
from pathlib import Path

ARCHIVE_SHA = "19e6f70f5c86856ccd98b6ffb96817f6ee4a58938aa76e5aef1d91b670ba6a53"
CUBICAL_COMMIT = "b150186d2544e7efeddd31e5d14a8b9ecbb100f7"
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", required=True, type=Path,
                        help="New directory for private sources, interfaces and receipts")
    parser.add_argument("--compiler-state", type=Path,
                        help="Existing kit state, verified by doctor; otherwise set up privately")
    parser.add_argument("--compiler-archive", type=Path,
                        help="Pinned compiler tar.xz for offline setup")
    args = parser.parse_args()
    work = args.work_dir.resolve()
    work.mkdir(parents=True, exist_ok=False)
    archive = REPO / "docs/history/orbifold/agda-checkpoints/myers-orbifolds-agda-checkpoint-022.tar.gz"
    if sha(archive) != ARCHIVE_SHA:
        raise RuntimeError("Preserved checkpoint archive hash mismatch")
    with tarfile.open(archive) as tar:
        tar.extractall(work, filter="data")
    checkpoint = work / "myers-agda-checkpoint"
    kit = checkpoint / "agda-native-kit-2.8.0.2/agda_native.py"
    cubical = checkpoint / "dependencies/cubical-0.9"
    state = args.compiler_state.resolve() if args.compiler_state else work / "state"
    launcher = [sys.executable, str(kit), "--state", str(state)]
    subprocess.run(launcher + ["verify"], check=True)
    if not args.compiler_state:
        setup = launcher + ["setup"]
        if args.compiler_archive:
            setup += ["--archive", str(args.compiler_archive.resolve()), "--offline"]
        subprocess.run(setup, check=True)
    subprocess.run(launcher + ["doctor"], check=True)
    source = work / "source"
    source.mkdir()
    for path in list(HERE.glob("*.agda")) + [HERE / "memo.agda-lib"]:
        shutil.copyfile(path, source / path.name)
    registry = work / "libraries"
    registry.write_text(str(cubical / "cubical.agda-lib") + "\n")
    graph = work / "imports.dot"
    command = launcher + ["--library-file", str(registry), "check",
                          str(source / "Everything.agda"), "--ignore-interfaces",
                          "--dependency-graph=" + str(graph), "-l", "cubical-0.9", "-i", str(source)]
    result = subprocess.run(command, cwd=source, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (work / "check.log").write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    raw_receipt = json.loads((state / "logs/latest.json").read_text())
    # --ignore-interfaces makes each checked module appear in the checker log.
    checked = {}
    for module, filename in re.findall(r"Checking ([\w.]+) \(([^\n]+)\)\.", result.stdout):
        path = Path(filename)
        if path.is_relative_to(source):
            key = "source/" + str(path.relative_to(source))
        elif path.is_relative_to(cubical):
            key = "cubical/" + str(path.relative_to(cubical))
        elif path.is_relative_to(state / "data"):
            key = "compiler-data/" + str(path.relative_to(state / "data"))
        else:
            raise RuntimeError("Unrecognized checked source: " + str(path))
        checked[module] = {"path": key, "sha256": sha(path)}
    if result.returncode == 0 and not {"Everything", "FrozenMemo", "HigherWitness", "Monodromy"} <= checked.keys():
        raise RuntimeError("Checker log lacks required fresh source checks")
    compiler_receipt = json.loads((state / "receipt.json").read_text())
    pins = compiler_receipt["pins"]
    builtin_modules = {}
    graph_modules = set(re.findall(r'label="([^"]+)"', graph.read_text())) if graph.exists() else set()
    for module in sorted(graph_modules - checked.keys()):
        if not module.startswith("Agda."):
            raise RuntimeError("Import graph contains an unreported library module: " + module)
        relative = pins["agda_version"] + "/lib/prim/" + module.replace(".", "/") + ".agda"
        path = state / "data" / relative
        digest = sha(path)
        if digest != compiler_receipt["setup_files"]["data/" + relative]:
            raise RuntimeError("Builtin source pin mismatch: " + module)
        builtin_modules[module] = {"path": "compiler-data/" + relative, "sha256": digest}
    if result.returncode == 0 and graph_modules != checked.keys() | builtin_modules.keys():
        raise RuntimeError("Checker log and import graph disagree")
    receipt = {
        "scope": "External Agda source checking only; no Lean model or translation",
        "completed_utc": datetime.now(timezone.utc).isoformat(),
        "checkpoint_sha256": ARCHIVE_SHA,
        "cubical_commit": CUBICAL_COMMIT,
        "compiler_pins": pins,
        "exit_code": result.returncode,
        "fresh_project_and_library_interfaces": True,
        "builtin_note": "Compiler-owned modules omitted from Checking lines; sources verified against kit pins",
        "builtin_modules": builtin_modules,
        "import_closure_module_count": len(graph_modules),
        "checked_module_count": len(checked),
        "checked_modules": dict(sorted(checked.items())),
        "input_hashes": {p.name: sha(p) for p in sorted(HERE.iterdir())
                         if p.suffix == ".agda" or p.name in ("memo.agda-lib", "check.py")},
        "checker_receipt": raw_receipt,
        "log_sha256": sha(work / "check.log"),
        "dependency_graph_sha256": sha(graph) if graph.exists() else None,
    }
    (work / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if result.returncode:
        raise SystemExit(result.returncode)
    print(f"Checked {len(checked)} source modules; receipt: {work / 'validation.json'}")


if __name__ == "__main__":
    main()
