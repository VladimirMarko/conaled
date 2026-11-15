"""Trusted, no-descendant child for the bounded #194 experiment."""
import json
import os
import signal
from pathlib import Path
import sys
import time


def child(work, case, source_a, source_b):
    a = source_a.read_bytes()
    b = source_b.read_bytes()
    with (work / 'attempt.marker').open('xb') as marker:
        marker.write(b'attempt\n')
    stdout = os.open(work / 'stdout.bin', os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    os.dup2(stdout, 1)
    os.close(stdout)
    if case != 'missing-output':
        stderr = os.open(work / 'stderr.bin', os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        os.dup2(stderr, 2)
        os.close(stderr)
    payload = {'a': list(a), 'b': list(b), 'sum': sum(a) + sum(b)}
    output = (json.dumps(payload) + '\n').encode('ascii')
    if case == 'stdout-overflow':
        output = b'x' * 65537
    elif case == 'invalid-output':
        output = bytes([255])
    if case == 'timeout':
        output = b'partial:'
    os.write(1, output)
    if case != 'missing-output':
        os.write(2, b'x' * 65537 if case == 'stderr-overflow' else b'fixture-complete\n')
    if case == 'timeout':
        time.sleep(3)
    if case == 'boundary':
        time.sleep(0.99)
    if case == 'signal':
        os.kill(os.getpid(), signal.SIGTERM)
    if case == 'nonzero':
        raise SystemExit(7)


def writer(work):
    def snapshot():
        return [(work / 'live/A').read_text().strip(), (work / 'live/B').read_text().strip()]
    history = [snapshot()]
    (work / 'barrier/writer-ready').write_bytes(b'ready\n')
    for _ in range(500):
        if (work / 'barrier/a-read').exists():
            break
        time.sleep(0.01)
    else:
        raise TimeoutError('a-read barrier exhausted')
    (work / 'live/A').write_bytes(b'A1\n')
    history.append(snapshot())
    (work / 'live/B').write_bytes(b'B1\n')
    history.append(snapshot())
    (work / 'writer-history.json').write_text(json.dumps(history) + '\n')
    (work / 'barrier/writer-done').write_bytes(b'done\n')


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == 'writer':
        writer(Path(sys.argv[2]))
    elif len(sys.argv) == 6 and sys.argv[1] == 'child':
        child(Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4]), Path(sys.argv[5]))
    else:
        raise SystemExit('usage: fixture.py writer WORK | child WORK CASE INPUT_A INPUT_B')
