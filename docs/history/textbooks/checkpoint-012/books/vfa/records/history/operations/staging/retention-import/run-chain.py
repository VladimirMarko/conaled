"""One authorized sequential staging check for local #1024; no retries."""
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import time
from datetime import datetime, timezone

STAGE = Path(__file__).resolve().parent
ROOT = STAGE.parents[2]
OUTPUT = STAGE / "generated"
PREFLIGHT = json.loads((STAGE / "preflight.json").read_text())
MODULES = [
    ("SquareKit.RelationTransport", ["Mathlib.Logic.Relation", "Mathlib.Data.Set.Lattice.Image"]),
    ("SquareKit.InteractionContracts", ["SquareKit.RelationTransport"]),
    ("Applications.Durability.Retention", ["SquareKit.InteractionContracts", "Mathlib.Data.List.TakeDrop", "Mathlib.Tactic.SplitIfs", "Lean.Elab.Tactic.Omega"]),
]

def now():
    return datetime.now(timezone.utc).isoformat()

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {"path": str(path), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}

def save(path, value):
    with Path(path).open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")

def heads():
    return {name: subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT / folder, text=True).strip()
            for name, folder in [("main", "conaled"), ("candidate", "vfa-validation")]}

trace = json.loads((STAGE / "environment-command-source.trace.json").read_text())
command = next(entry["message"] for entry in trace["log"] if entry["message"].startswith(".> LEAN_PATH="))
tokens = shlex.split(command[3:])
assert tokens[0].startswith("LEAN_PATH=")
lean = tokens[1]
assert lean == "/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
assert tokens[-1] == "--json" and all(flag in tokens for flag in ["-o", "-i", "-c", "--setup"])
env_additions = {
    "PATH": "/root/.nix-profile/bin:" + os.environ["PATH"],
    "NIX_CONFIG": "build-users-group =\nexperimental-features = nix-command flakes",
    "LEAN_NUM_THREADS": "1",
    "LEAN_PATH": str(OUTPUT) + ":" + tokens[0].split("=", 1)[1],
}
search_directory_availability = [{"path": path, "exists": Path(path).is_dir()} for path in tokens[0].split("=", 1)[1].split(":")]
protected = PREFLIGHT["protected_inputs_before"]
protected += [identity(ROOT / folder / "lakefile.toml") for folder in ["conaled", "vfa-validation"]]
protected += [PREFLIGHT["spec"], PREFLIGHT["proposal"], identity(lean)]
protected += list(PREFLIGHT["staged_sources"].values())
protected += [identity(STAGE / name) for name in ["preflight.py", "preflight.json", "environment-command-source.trace.json", "run-chain.py"]]
protected += [identity(path) for path in sorted((STAGE / "prelaunch-guard").iterdir()) if path.is_file()]

def verify():
    current = [identity(item["path"]) for item in protected]
    changed = [new for old, new in zip(protected, current) if old != new]
    current_heads = heads()
    return {"checked_at_utc": now(), "protected_inputs": current, "changed_protected_inputs": changed,
            "heads": current_heads, "heads_unchanged": current_heads == PREFLIGHT["heads_before"]}

before = verify()
assert not before["changed_protected_inputs"] and before["heads_unchanged"]
assert PREFLIGHT["spec"]["sha256"] == "a06c5512cb30a686693bff2828b6fe99d7b2fe206d0345b831baf0af0ad84bd5"
assert not OUTPUT.exists()
save(STAGE / "STARTED.json", {"started_at_utc": now(), "modules": MODULES, "maximum_compiler_invocations": 3,
    "strictly_sequential": True, "stop_on_failure": True, "timeout_seconds_each": 180, "termination_grace_seconds_each": 5})
save(STAGE / "inputs.json", {"before": before, "environment_additions": env_additions,
    "inherited_search_directory_availability": search_directory_availability,
    "command_environment_provenance": identity(STAGE / "environment-command-source.trace.json"),
    "setup_used": False, "imports_override_created": False,
    "setup_omission": "No original Retention or prerequisite setup/trace exists. The amended specification permits direct LEAN_PATH. These unchanged legacy-format sources have no module command or extra source flags; both lakefile.toml files declare no leanOptions. Working directory and relative source paths preserve module names; emitted metadata is checked. The completed Finite trace supplies only pinned executable, environment and output-flag provenance."})
OUTPUT.mkdir()
env = os.environ.copy()
env.update(env_additions)
results = []
invocations = 0
error = None
try:
    for index, (module, imports) in enumerate(MODULES, 1):
        checked = verify()
        assert not checked["changed_protected_inputs"] and checked["heads_unchanged"]
        previous = [artifact for result in results for artifact in result["outputs"]]
        assert all(identity(item["path"]) == item for item in previous)
        record = STAGE / (str(index).zfill(2) + "-" + module.split(".")[-1])
        record.mkdir()
        source = Path(*module.split(".")).with_suffix(".lean")
        stem = OUTPUT.joinpath(*module.split("."))
        stem.parent.mkdir(parents=True, exist_ok=True)
        argv = ["timeout", "--signal=TERM", "--kill-after=5s", "180s", "nix", "develop", str(ROOT / "conaled"),
                "--command", lean, str(source), "-o", str(stem.with_suffix(".olean")),
                "-i", str(stem.with_suffix(".ilean")), "-c", str(stem.with_suffix(".c")), "--json"]
        started = {"module": module, "started_at_utc": now(), "working_directory": str(STAGE),
            "argv": argv, "shell_rendering_for_reference_only": shlex.join(argv), "environment_additions": env_additions,
            "source": identity(STAGE / source), "generated_dependencies_verified_before_consumer": previous,
            "expected_direct_imports": imports, "setup_used": False, "imports_override_created": False}
        save(record / "STARTED.json", started)
        print("START " + module, flush=True)
        start = time.monotonic()
        with (record / "diagnostics.jsonl").open("xb") as log:
            invocations += 1
            completed = subprocess.run(argv, cwd=STAGE, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        result = {**started, "finished_at_utc": now(), "elapsed_seconds": time.monotonic() - start,
            "exit_code": completed.returncode, "timed_out": completed.returncode in [124, 137],
            "diagnostics": identity(record / "diagnostics.jsonl"),
            "outputs": [identity(path) for path in sorted(stem.parent.glob(stem.name + ".*")) if path.is_file()]}
        ilean = stem.with_suffix(".ilean")
        if ilean.exists():
            data = json.loads(ilean.read_text())
            metadata = {key: data[key] for key in ["module", "directImports", "version"]}
            metadata["declarations"] = sorted(data["decls"])
            cfile = stem.with_suffix(".c")
            metadata["c_initializers"] = sorted(set(re.findall(r"initialize_[A-Za-z0-9_]+", cfile.read_text()))) if cfile.exists() else []
            save(record / "module-metadata.json", metadata)
            result["metadata"] = identity(record / "module-metadata.json")
            result["module_name_matches"] = metadata["module"] == module
            result["direct_imports_match"] = [row[0] for row in metadata["directImports"]] == imports
        result["success"] = completed.returncode == 0 and result.get("module_name_matches", False) and result.get("direct_imports_match", False) and all(stem.with_suffix(suffix).exists() for suffix in [".olean", ".ilean", ".c"])
        save(record / "result.json", result)
        results.append(result)
        print("END " + module + " exit=" + str(completed.returncode) + " elapsed=" + str(round(result["elapsed_seconds"], 3)) + " verified=" + str(result["success"]), flush=True)
        if not result["success"]:
            break
except Exception as exc:
    error = {"type": type(exc).__name__, "message": str(exc)}
finally:
    outputs = [identity(path) for path in sorted(OUTPUT.rglob("*")) if path.is_file()]
    save(STAGE / "generated-output-identities.json", outputs)
    after = verify()
    shutil.rmtree(OUTPUT)
    after["generated_output_tree_removed"] = not OUTPUT.exists()
    after["no_setup_or_import_map_created"] = not list(STAGE.rglob("*.setup.json"))
    save(STAGE / "postcheck.json", after)
    success = len(results) == 3 and all(result["success"] for result in results) and error is None and not after["changed_protected_inputs"] and after["heads_unchanged"]
    aggregate = {"finished_at_utc": now(), "compiler_invocations": invocations, "success": success,
        "results": results, "runner_error": error, "postcheck": identity(STAGE / "postcheck.json"),
        "generated_output_identities": identity(STAGE / "generated-output-identities.json"),
        "generated_output_tree_removed": not OUTPUT.exists()}
    save(STAGE / "result.json", aggregate)
    print(json.dumps({key: aggregate[key] for key in ["compiler_invocations", "success", "runner_error", "generated_output_tree_removed"]}), flush=True)
raise SystemExit(0 if success else 1)
