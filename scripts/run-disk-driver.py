#!/usr/bin/env python3
"""Run the Lean JSON driver with explicit process limits (inside the Nix shell)."""
import json
import os
import pathlib
import resource
import signal
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (16 * 1024**3,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (15, 16))
    resource.setrlimit(resource.RLIMIT_FSIZE, (8 * 1024**2,) * 2)


def main():
    if len(sys.argv) != 2:
        print(json.dumps({'status': 'input_error', 'reason': 'expected request.json path'}))
        return 2
    request = str(pathlib.Path(sys.argv[1]).resolve())
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        process = subprocess.Popen(
            ['lake', 'env', 'lean', '-j1', '--run', 'scripts/disk-driver.lean', request],
            cwd=ROOT, stdout=out, stderr=err, start_new_session=True, preexec_fn=limits)
        try:
            code = process.wait(timeout=25)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            print(json.dumps({'status': 'resource_failure', 'reason': '25-second wall limit'}))
            return 3
        out.seek(0)
        raw = out.read()
        try:
            result = json.loads(raw)
        except (ValueError, UnicodeDecodeError):
            result = None
        if code not in (0, 2, 3) or not isinstance(result, dict):
            # A process failure is not a certified numerical result, even if it
            # happened after writing a prefix of a JSON object.
            print(json.dumps({'status': 'resource_or_process_failure', 'exit_code': code}))
            return 3
        print(json.dumps(result, separators=(',', ':')))
        return code


if __name__ == '__main__':
    raise SystemExit(main())
