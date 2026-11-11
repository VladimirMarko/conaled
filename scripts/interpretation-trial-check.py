#!/usr/bin/env python3
"""External per-arm Lean feedback budget and append-only snapshot runner.
The coordinator initializes the state before dispatch. Both routes use this runner.
This is a cooperative experimental boundary, not an operating-system sandbox.
"""
import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys
import time


def stamp():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--state', type=Path, required=True)
    p.add_argument('--initialize', action='store_true')
    p.add_argument('--minutes', type=float, default=45)
    p.add_argument('--rounds', type=int, default=30)
    p.add_argument('--source', type=Path)
    p.add_argument('--watch', type=Path, metavar='AUTHOR_OUTPUT', help='coordinator: snapshot output at time/round cutoff')
    args = p.parse_args()
    root = args.state.resolve().parent
    root.mkdir(parents=True, exist_ok=True)
    if args.initialize:
        with args.state.open('x') as f:
            json.dump({'started': stamp(), 'deadline_epoch': time.time()+args.minutes*60,
                       'round_limit': args.rounds, 'count': 0}, f)
        return 0
    if args.watch:
        while True:
            state = json.loads(args.state.read_text())
            if state['count'] >= state['round_limit'] or time.time() >= state['deadline_epoch']:
                target = root / 'cutoff'
                target.mkdir(exist_ok=False)
                manifest = {'snapshot_started': stamp(), 'files': {}}
                for source in sorted(args.watch.rglob('*')):
                    if source.is_file() and not any(x in {'.lake', '.git'} for x in source.relative_to(args.watch).parts):
                        relative = source.relative_to(args.watch)
                        destination = target / relative
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copyfile(source, destination)
                        manifest['files'][str(relative)] = hashlib.sha256(destination.read_bytes()).hexdigest()
                manifest['snapshot_finished'] = stamp()
                (root / 'cutoff.json').write_text(json.dumps(manifest, indent=2)+'\n')
                return 0
            time.sleep(0.2)
    if args.source is None:
        p.error('--source is required for checking')
    with (root / (args.state.name + '.lock')).open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        state = json.loads(args.state.read_text())
        if state['count'] >= state['round_limit'] or time.time() >= state['deadline_epoch']:
            print('TRIAL_BUDGET_EXHAUSTED: no further checker process started', file=sys.stderr)
            return 75
        # Account before invoking Lean, including failed/infrastructure checks.
        state['count'] += 1
        temp = args.state.with_suffix('.tmp')
        temp.write_text(json.dumps(state, indent=2)+'\n')
        os.replace(temp, args.state)
        attempt = root / f"round-{state['count']:03d}"
        attempt.mkdir(exist_ok=False)
        snapshot = attempt / 'source.lean'
        snapshot.write_bytes(args.source.read_bytes())
        command = ['lake', 'env', 'lean', '--json', str(snapshot)]
        record = {'started': stamp(), 'command': command, 'original_source': str(args.source.resolve()),
                  'source_sha256': hashlib.sha256(snapshot.read_bytes()).hexdigest(), 'round': state['count']}
        try:
            proc = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (attempt / 'compiler.log').write_text(proc.stdout)
            print(proc.stdout, end='')
            record['exit'] = proc.returncode
        except OSError as error:
            record['exit'] = 74
            record['error'] = str(error)
            print(str(error), file=sys.stderr)
        record['finished'] = stamp()
        (attempt / 'receipt.json').write_text(json.dumps(record, indent=2)+'\n')
        return record['exit']


if __name__ == '__main__':
    sys.exit(main())
