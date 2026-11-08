#!/usr/bin/env python3
"""Time lock waiting separately while invoking the frozen trial checker."""
import argparse
from datetime import datetime, timezone
import fcntl
import json
from pathlib import Path
import resource
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--lock', default='/tmp/conaled-362-orchestration/build.lock')
    args = parser.parse_args()
    root = Path.cwd().resolve()
    source = (root / args.source).resolve()
    attempts = root / 'attempts'
    if source.parent != attempts or source.suffix != '.lean' or not source.is_file():
        parser.error('source must be an existing direct attempts/*.lean file')
    records = attempts / 'timing'
    records.mkdir(exist_ok=True)
    receipt = records / (source.stem + '.json')
    # Reserve the receipt before any check. Failed or interrupted attempts may
    # not silently reuse a name and overwrite their earlier timing evidence.
    with receipt.open('x') as output:
        started = time.monotonic()
        start_utc = datetime.now(timezone.utc).isoformat()
        command = ['direnv', 'exec', '.', 'python3', 'check_attempt.py',
                   str(source.relative_to(root))]
        state = {'schema': 1, 'source': str(source.relative_to(root)),
                 'command': command, 'start_utc': start_utc,
                 'status': 'waiting', 'lock': args.lock}
        json.dump(state, output, indent=2)
        output.write('\n')
        output.flush()
        with open(args.lock, 'a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            acquired = time.monotonic()
            state.update(status='running', lock_wait_seconds=acquired-started)
            output.seek(0)
            output.truncate()
            json.dump(state, output, indent=2)
            output.write('\n')
            output.flush()
            result = subprocess.run(command, cwd=root, check=False)
            finished = time.monotonic()
            usage = resource.getrusage(resource.RUSAGE_CHILDREN)
            state.update(status='finished', exit_code=result.returncode,
                         finish_utc=datetime.now(timezone.utc).isoformat(),
                         check_seconds=finished-acquired,
                         wall_seconds=finished-started,
                         child_maxrss_kib=usage.ru_maxrss,
                         memory_scope='Linux RUSAGE_CHILDREN high-water RSS; not aggregate concurrent RSS')
            output.seek(0)
            output.truncate()
            json.dump(state, output, indent=2)
            output.write('\n')
    raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
