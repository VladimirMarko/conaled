#!/usr/bin/env python3
"""Matched public-adapter schedules; elapsed times include local pipe/dispatch costs."""
import json
import subprocess
import time

rows = []
for repetition in range(3):
    for name, commands in [('ordinary', 'aqqbqqc'), ('repartition', 'asmbhm c'.replace(' ', ''))]:
        process = subprocess.Popen(['lake', 'env', 'lean', '--run', 'scripts/regional-migration-main.lean'],
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True, bufsize=1)
        process.stdin.write('q'); process.stdin.flush()
        assert process.stdout.readline().startswith('Q:')
        for command in commands:
            start = time.perf_counter_ns()
            process.stdin.write(command); process.stdin.flush()
            lines = []
            while True:
                line = process.stdout.readline().strip()
                if not line:
                    raise RuntimeError('adapter stopped: ' + process.stderr.read())
                lines.append(line)
                if line.startswith(('C:', 'Q:')):
                    break
            rows.append({'repetition': repetition, 'schedule': name, 'command': command,
                         'elapsed_ns': time.perf_counter_ns() - start, 'responses': lines})
        process.stdin.close()
        assert process.wait() == 0, process.stderr.read()
print(json.dumps({'clock': 'perf_counter_ns', 'unit': 'ns',
                  'scope': 'local pipe round-trip after process startup; not a CPU-work or remote-latency proof',
                  'rows': rows}, indent=2))
