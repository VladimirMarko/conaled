#!/usr/bin/env python3
"""Replay #115 in a new private directory using the verified release binary."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile

from inspect_interface import Interface

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
BINARY_SHA = "3fe070780fa370f5b74e5716ebe42fb60ec6b0ad90d13f8ab45d2903abf39b84"
ARCHIVE_SHA = "19e6f70f5c86856ccd98b6ffb96817f6ee4a58938aa76e5aef1d91b670ba6a53"
SELECTIONS = {
    "IdentityPattern": ["identity", "J", "predecessor", "forget", "opaqueIdentity"],
    "Monodromy": ["step", "circle-loop", "input", "erased-input", "transport-three",
                  "transport-two", "value-and-witness-twice", "transported-witness-twice"],
    "FrozenMemo": ["j-beta", "η", "w-twice", "apd-twice"],
    "Cubical.Data.Equality.S1": ["Cover", "S¹-rec", "loop"],
    "Cubical.Data.Equality.Conversion": ["pathToEq", "eqToPath"],
    "Cubical.Data.Int.Properties": ["sucPathℤ"],
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    binary, work = args.agda.resolve(), args.work_dir.resolve()
    if sha(binary) != BINARY_SHA:
        raise ValueError("Compiler binary does not match the pinned Linux release")
    archive = REPO / "docs/history/orbifold/agda-checkpoints/myers-orbifolds-agda-checkpoint-022.tar.gz"
    if sha(archive) != ARCHIVE_SHA:
        raise ValueError("Checkpoint pin mismatch")
    work.mkdir(parents=True, exist_ok=False)
    with tarfile.open(archive) as tar:
        members = [m for m in tar.getmembers() if m.name.startswith(
            "myers-agda-checkpoint/dependencies/cubical-0.9/")]
        tar.extractall(work, members=members, filter="data")
    cubical = work / "myers-agda-checkpoint/dependencies/cubical-0.9"
    source, ordinary, evidence = [work / name for name in ("source", "ordinary", "evidence")]
    for directory in (source, ordinary, evidence, work / "data", work / "config", work / "tmp"):
        directory.mkdir()
    for name in ("Monodromy.agda", "FrozenMemo.agda", "memo.agda-lib"):
        shutil.copyfile(REPO / "experiments/dependent-higher-identity" / name, source / name)
    shutil.copyfile(HERE / "IdentityPattern.agda", ordinary / "IdentityPattern.agda")
    registry = work / "libraries"
    registry.write_text(str(cubical / "cubical.agda-lib") + "\n")
    env = os.environ | {"Agda_datadir": str(work / "data"),
                        "AGDA_DIR": str(work / "config"), "TMPDIR": str(work / "tmp")}
    commands = {}

    def run(name, arguments, cwd, expected=0):
        command = [str(binary), *map(str, arguments)]
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = result.stdout.replace(str(work), "$WORK").replace(str(binary), "$AGDA")
        (evidence / (name + ".log")).write_text(log)
        commands[name] = {"command": [s.replace(str(work), "$WORK").replace(str(binary), "$AGDA")
                                       for s in command], "exit": result.returncode}
        if result.returncode != expected:
            raise RuntimeError(f"{name}: expected {expected}, got {result.returncode}: {log}")
        return result.stdout

    run("setup", ["--setup"], work)
    safe = ["--safe", "--no-allow-unsolved-metas", "--no-allow-incomplete-matches"]
    run("ordinary", ["--no-libraries", *safe, "--show-implicit", "--show-irrelevant",
                      "-v", "tc.signature:60", ordinary / "IdentityPattern.agda"], ordinary)
    library = ["--no-default-libraries", "--library-file", registry, "-i", source]
    log = run("monodromy", [*library, *safe, "--ignore-interfaces",
                            "--dependency-graph=" + str(work / "imports.dot"),
                            source / "Monodromy.agda"], source)
    closure = {}
    for module, filename in re.findall(r"Checking ([\w.]+) \(([^\n]+)\)\.", log):
        path = Path(filename)
        closure[module] = {"path": str(path.relative_to(work)), "sha256": sha(path)}
    graph = (work / "imports.dot").read_text()
    for module in set(re.findall(r'label="([^"]+)"', graph)) - closure.keys():
        if not module.startswith("Agda."):
            raise ValueError("Unreported library import: " + module)
        path = work / "data/2.8.0.2/lib/prim" / (module.replace(".", "/") + ".agda")
        closure[module] = {"path": str(path.relative_to(work)), "sha256": sha(path)}
    for module, names in SELECTIONS.items():
        suffix = module.replace(".", "/") + ".agdai"
        paths = [p for p in work.rglob("*.agdai") if str(p).endswith("/" + suffix)]
        if len(paths) != 1:
            raise ValueError(f"Expected one completed interface for {module}: {paths}")
        interface = Interface(paths[0])
        (evidence / (module + ".json")).write_text(json.dumps(interface.report(names), ensure_ascii=False, indent=2) + "\n")
        # Complete raw tables remain private: excerpts refer to these node IDs.
        (work / (module + ".tables.json")).write_text(json.dumps(vars(interface), ensure_ascii=False))
    run("javascript", ["--js", "--no-libraries", "--compile-dir=" + str(work / "js"),
                        ordinary / "IdentityPattern.agda"], ordinary)
    run("haskell", ["--compile", "--ghc-dont-call-ghc", "--no-main", "--no-libraries",
                     "--compile-dir=" + str(work / "hs"), ordinary / "IdentityPattern.agda"], ordinary)
    run("cubical-runtime", ["--js", *library, "--compile-dir=" + str(work / "cubical-js"),
                             source / "Monodromy.agda"], source, expected=42)
    shutil.copyfile(work / "js/jAgda.IdentityPattern.js", evidence / "IdentityPattern.js.txt")
    shutil.copyfile(work / "hs/MAlonzo/Code/IdentityPattern.hs", evidence / "IdentityPattern.hs.txt")
    receipt = {"compiler_sha256": BINARY_SHA, "checkpoint_sha256": ARCHIVE_SHA,
               "cubical_commit": "b150186d2544e7efeddd31e5d14a8b9ecbb100f7",
               "commands": commands, "closure": dict(sorted(closure.items())),
               "cpu_affinity": sorted(os.sched_getaffinity(0)),
               "scripts": {p.name: sha(p) for p in (HERE / "reproduce.py", HERE / "inspect_interface.py", HERE / "IdentityPattern.agda")}}
    (evidence / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(evidence)


if __name__ == "__main__":
    main()
