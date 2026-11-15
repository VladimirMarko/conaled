#!/usr/bin/env python3
"""One bounded environment probe; not a formal acceptance command."""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
FIXTURE = ROOT / "runtime-tmp/1035-original-squares-probe"
LIBRARY = ROOT / "runtime-tmp/1035-mmap-random-prototype/libconaled_mmap_random.so"
SOURCE_SHA = "2556c4c895a747bc0092239b5dc5b220e8a6d4d6cf8a6f9fe66ab96fa2462dc7"
OUTPUT_SHA = "133589a2adff7fcb278b1bc79fd1fd8f2bcf9315cfae28d6d801a5efa099ac4c"
HELPER_SHA = "ab9e236bb60bf3bbd96e682cc1d48bd1b8566791a5d2213f325c3f5f81d8f19f"


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prototype-sha256", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{64}", args.prototype_sha256):
        parser.error("expected an exact SHA-256 identity")
    helper = ROOT / "work-state/tooling/pinned_native_toolchain.py"
    source = FIXTURE / "Squares.lean"
    if sha(helper) != HELPER_SHA or sha(source) != SOURCE_SHA:
        raise RuntimeError("Frozen helper or original source identity differs")
    if sha(LIBRARY) != args.prototype_sha256:
        raise RuntimeError("Prototype identity differs from the inspected binary")
    attempt = EVIDENCE / "original-squares-random-run1"
    attempt.mkdir(mode=0o700)
    output = FIXTURE / "Squares-random.olean"
    if output.exists():
        raise RuntimeError("Refusing to overwrite probe output")

    # Reuse the unchanged accepted environment and owned-child cleanup routine.
    sys.path.insert(0, str(helper.parent))
    import pinned_native_toolchain as native
    env, overrides = native.environment()
    recorder_path = ROOT / "work-state/validation-recorder/recorder.py"
    spec = importlib.util.spec_from_file_location("accepted_recorder", recorder_path)
    recorder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(recorder)
    payload = native.OVERLAY / "libexec/lean"
    env.update({
        "LD_PRELOAD": str(LIBRARY) + ":" + str(native.SHIM),
        "CONALED_SELF_EXE": str(payload),
        "CONALED_MMAP_RANDOM": "1",
        "CONALED_MMAP_RANDOM_EXE": str(payload),
        "CONALED_MMAP_RANDOM_REPORT": "1",
    })
    command = [str(payload), "-j1", "--root=" + str(FIXTURE),
               "-o", str(output), "Squares.lean"]
    identities = {str(p): sha(p) for p in
                  (helper, recorder_path, LIBRARY, native.SHIM, payload, source)}
    selected = ("LEAN_SYSROOT", "LD_LIBRARY_PATH", "LEAN_NUM_THREADS", "LD_PRELOAD",
                "CONALED_SELF_EXE", "CONALED_MMAP_RANDOM",
                "CONALED_MMAP_RANDOM_EXE", "CONALED_MMAP_RANDOM_REPORT")
    record = {
        "started_utc": now(), "command": command, "cwd": str(FIXTURE),
        "source_revision": "3279bacaec4087cc0d6b7e6b8ae862109cb2dfec",
        "current_formal_candidate_unchanged": "c988f183887896c00b09aaff9077a6ea7fb8d68f",
        "selected_environment": {k: env.get(k) for k in selected},
        "execution_input_sha256": identities, "timeout_seconds": 60,
        "cleanup_grace_seconds": 5, "expected_output_sha256": OUTPUT_SHA,
        "scope": "Separate bounded original-Squares environment probe while fresh4 is active. "
                 "Uncontrolled concurrent/cache conditions; no causal speedup or full formal credit.",
    }
    (attempt / "launch.json").write_text(json.dumps(record, indent=2) + "\n")
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    with (attempt / "child.log").open("xb", buffering=0) as log:
        child = subprocess.Popen(command, cwd=FIXTURE, env=env,
                                 stdin=subprocess.DEVNULL, stdout=log,
                                 stderr=subprocess.STDOUT, start_new_session=True)
        record["owned_child"] = {"pid": child.pid, "process_group": child.pid,
                                 "session": child.pid}
        record["timed_out"] = False
        try:
            record["child_returncode"] = child.wait(timeout=60)
        except subprocess.TimeoutExpired:
            record["timed_out"] = True
            record["cleanup"] = recorder.stop_owned_child(child, 5)
            record["child_returncode"] = child.returncode
        os.fsync(log.fileno())
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    record.update({
        "finished_utc": now(), "wall_seconds": time.monotonic() - started,
        "child_reaped": child.returncode is not None,
        "descendant_quiescence_verified": False,
        "user_cpu_seconds": after.ru_utime - before.ru_utime,
        "system_cpu_seconds": after.ru_stime - before.ru_stime,
        "max_rss_kib": after.ru_maxrss,
        "major_faults": after.ru_majflt - before.ru_majflt,
        "input_blocks": after.ru_inblock - before.ru_inblock,
        "resource_scope": "RUSAGE_CHILDREN for reaped children; counters retained as reported.",
        "execution_inputs_unchanged": all(sha(Path(p)) == h for p, h in identities.items()),
    })
    if child.returncode is not None and output.exists():
        record["output_sha256"] = sha(output)
        record["output_matches_expected"] = record["output_sha256"] == OUTPUT_SHA
    log_text = (attempt / "child.log").read_text(errors="replace")
    summaries = [line for line in log_text.splitlines()
                 if line.startswith("conaled-mmap-random-v1 ")]
    record["diagnostic_summary_count"] = len(summaries)
    if len(summaries) == 1:
        record["advice_counters"] = {
            key: int(value) for key, value in
            re.findall(r"([a-z_]+)=(\d+)", summaries[0])}
    counters = record.get("advice_counters", {})
    record["advice_actually_succeeded"] = counters.get("success", 0) > 0
    record["bounded_probe_passed"] = (
        not record["timed_out"] and record["child_returncode"] == 0
        and record.get("output_matches_expected", False)
        and record["execution_inputs_unchanged"]
        and record["advice_actually_succeeded"])
    (attempt / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2), flush=True)
    print(log_text, end="", flush=True)
    return 0 if record["bounded_probe_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
