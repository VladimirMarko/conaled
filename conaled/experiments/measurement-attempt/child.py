"""Controlled, descendant-free finite child; regular-file output is the protocol."""
from pathlib import Path
import sys

mode, captured, output, counter = sys.argv[1:]
with Path(counter).open('a') as stream:
    stream.write('attempt\n')
if mode == 'missing-output':
    sys.exit(0)
data = b'x' * 4097 if mode == 'overflow' else Path(captured).read_bytes()
Path(output).write_bytes((b'partial:' if mode == 'timeout' else b'') + data)
if mode == 'boundary':
    import time
    time.sleep(0.99)
if mode == 'timeout':
    import time
    time.sleep(3)
if mode == 'nonzero':
    sys.exit(7)
