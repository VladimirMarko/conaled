#!/usr/bin/env python3
"""Reproduce one historical numerical probe using this checkout's built modules."""
import json
import os
import pathlib
import resource
import signal
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[2]


def caps():
    resource.setrlimit(resource.RLIMIT_AS, (16 * 1024**3,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (15, 16))
    resource.setrlimit(resource.RLIMIT_FSIZE, (8 * 1024**2,) * 2)


if len(sys.argv) != 10:
    raise SystemExit('usage: run-disk-feasibility.py OUTPUT_DIR NAME KIND N NUM DEN TOL_DEN BIT_CAP MODE')
outdir = pathlib.Path(sys.argv[1])
outdir.mkdir(parents=True, exist_ok=True)
name = sys.argv[2]
if pathlib.Path(name).name != name:
    raise SystemExit('NAME must be a basename')
args = sys.argv[3:]
command = ['lake', 'env', 'lean', '-j1', '--run', 'scripts/probes/DiskDriverFeasibility.lean', *args]
start = time.monotonic()
timed_out = False
with (outdir / (name+'.stdout')).open('wb') as out, (outdir / (name+'.stderr')).open('wb') as err:
    p = subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=err,
                         start_new_session=True, preexec_fn=caps)
    try:
        code = p.wait(timeout=25)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(p.pid, signal.SIGKILL)
        code = p.wait()
metadata = {'command':command, 'returncode':code, 'wall_seconds':time.monotonic()-start,
            'timed_out':timed_out, 'caps':{'address_space_gib':16,'cpu_seconds':[15,16],
                                        'wall_seconds':25,'output_bytes':8*1024**2},
            'max_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
            'receipt_kind':'probe execution; not candidate validation'}
(outdir / (name+'.meta.json')).write_text(json.dumps(metadata, indent=2)+'\n')
print(json.dumps(metadata))
raise SystemExit(1 if timed_out or code else 0)
