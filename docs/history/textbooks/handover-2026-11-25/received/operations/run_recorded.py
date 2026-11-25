#!/usr/bin/env python3
"""Record an actual native-route command with an immediate durable child-exit receipt."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def describe(path):
    if not path.exists():
        return None
    raw = path.read_bytes()
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
            "mode": format(path.stat().st_mode, "o")}


def write_new_json(path, value):
    """Never replace prior evidence; sync both contents and directory entry."""
    with path.open("x") as out:
        json.dump(value, out, indent=2)
        out.write("\n")
        out.flush()
        os.fsync(out.fileno())
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    parser.add_argument("--project", type=Path)
    parser.add_argument("--inputs", type=Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    work = Path(__file__).resolve().parent
    root = work.parent
    project = args.project or root / "conaled"
    inputs = json.loads(args.inputs.read_text()) if args.inputs else []
    before = {name: describe(project / name) for name in inputs}
    requested = args.command
    if requested and requested[0] == "--":
        requested = requested[1:]
    if not requested:
        parser.error("a command is required")
    native = Path(os.environ["CONALED_NATIVE"]).resolve(strict=True)
    state = Path(os.environ["CONALED_PROFILE_STATE"]).resolve(strict=True)
    command = ["python3", "-B", str(native), "--state", str(state),
               "run", "--project", str(project), "--", *requested]
    start = {"schema": 1, "name": args.name, "command": command,
             "project": str(project), "started_utc": utc(), "source_bindings": before,
             "resource_or_time_limits_added": False,
             "boundary": "Actual command result; focused compilation is not whole-library acceptance."}
    start_path = work / (args.name + ".start.json")
    log_path = work / (args.name + ".log")
    child_exit_path = work / (args.name + ".child-exit.json")
    result_path = work / (args.name + ".result.json")
    for path in [start_path, log_path, child_exit_path, result_path]:
        if path.exists() or path.is_symlink():
            parser.error("refusing to overwrite actual evidence: " + str(path))
    write_new_json(start_path, start)
    start_descriptor = describe(start_path)
    print("Started " + args.name, flush=True)
    begin = time.monotonic()
    with log_path.open("x") as log:
        result = subprocess.run(command, cwd=project, stdout=log, stderr=subprocess.STDOUT)
        finished = utc()
        elapsed = time.monotonic() - begin
        # Persist the real subprocess result before hashing any post-run input.
        write_new_json(child_exit_path, {
            "schema": 1, "name": args.name, "command": command, "project": str(project),
            "started_utc": start["started_utc"], "finished_utc": finished,
            "elapsed_seconds": elapsed, "exit_code": result.returncode,
            "start_record": {"path": str(start_path), **start_descriptor},
            "log": str(log_path), "post_run_hashing_completed": False,
            "resource_or_time_limits_added": False,
            "boundary": "Actual native-route child exit only; input invariance and source acceptance are not inferred."})
        log.flush()
        os.fsync(log.fileno())
    after = {name: describe(project / name) for name in inputs}
    record = {**start, "finished_utc": finished, "elapsed_seconds": elapsed,
              "recorded_utc": utc(), "exit_code": result.returncode,
              "source_bindings_after": after, "sources_unchanged": before == after,
              "log": str(log_path), "log_descriptor": describe(log_path),
              "child_exit_receipt": {"path": str(child_exit_path), **describe(child_exit_path)}}
    write_new_json(result_path, record)
    print(json.dumps({"name": args.name, "exit_code": result.returncode,
                      "sources_unchanged": before == after,
                      "elapsed_seconds": record["elapsed_seconds"]}), flush=True)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
