#!/usr/bin/env python3
"""Paired #253 experiment, retaining unsuccessful and incomplete attempts."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys
import sysconfig
import time
import tracemalloc
import unittest

from adapter import create, Environment
import test as behavior

ROOT = Path(__file__).resolve().parents[2]
OLD = ROOT / 'experiments/bounded-buffer-target/experiment.py'
spec = importlib.util.spec_from_file_location('prior_experiment', OLD)
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)


def execute(capacity, commands, cached, conversion=False, fault=None):
    env = Environment(fail_allocation=fault == 'allocation', fail_output=fault == 'output')
    status, b = create(capacity, cached and not conversion, env=env)
    if status != 'ready':
        return {'status': 'failed', 'operation': 'construct', 'reply': status}
    checksum = 0
    for index, command in enumerate(commands):
        if command[0] == 'convert':
            if conversion:
                status, destination = b.convert(env)
                if status != 'ready':
                    return {'status': 'failed', 'operation': 'convert', 'index': index, 'reply': status}
                b = destination
            continue
        tag, value = b.step(command, env)
        if tag in ('allocation', 'output'):
            return {'status': 'failed', 'operation': command[0], 'index': index, 'reply': tag}
        code = {'accepted': 1, 'overflow': 2, 'summary': 3, 'sequence': 4}[tag]
        checksum = (checksum * 33 + code) & 0xffffffff
        if isinstance(value, bytes):
            for byte in value:
                checksum = (checksum * 33 + byte) & 0xffffffff
        elif value is not None:
            checksum = (checksum * 33 + value) & 0xffffffff
        # Do not retain the snapshot into the next operation.
        del value
    return {'status': 'success', 'checksum': checksum}


def main(destination, fault=None, incomplete=False):
    with Path(destination).open('x') as stream:
        def record(value):
            stream.write(json.dumps(value, sort_keys=True) + '\n')
            stream.flush()
        sources = [Path(__file__).resolve(), Path(__file__).with_name('adapter.py'),
                   Path(__file__).with_name('test.py'), OLD, ROOT/'flake.lock',
                   ROOT/'lean-toolchain', ROOT/'lake-manifest.json',
                   ROOT/'Applications/Sequences/ByteBuffer.lean',
                   ROOT/'Applications/Resources/ByteBuffer.lean']
        record({'kind': 'environment', 'python': sys.version, 'executable': sys.executable,
                'platform': platform.platform(), 'compiler': platform.python_compiler(),
                'config_args': sysconfig.get_config_var('CONFIG_ARGS'),
                'clock': vars(time.get_clock_info('perf_counter')),
                'cpuinfo': Path('/proc/cpuinfo').read_text().split('\n\n')[0],
                'git_base': subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip(),
                'command': sys.argv, 'fault': fault, 'incomplete_requested': incomplete,
                'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}})
        try:
            started = time.perf_counter_ns()
            tests = unittest.defaultTestLoader.loadTestsFromModule(behavior)
            result = unittest.TextTestRunner().run(tests)
            record({'kind': 'checks', 'success': result.wasSuccessful(), 'tests': result.testsRun,
                    'short_traces': 5460, 'elapsed_ns': time.perf_counter_ns()-started})
            if not result.wasSuccessful():
                raise RuntimeError('behavior checks failed')
            failed = False
            for name, (capacity, commands, conversion) in prior.workloads().items():
                record({'kind': 'workload', 'name': name, 'capacity': capacity, 'commands': commands,
                        'model_plain': prior.model(capacity, commands, False),
                        'model_cached': prior.model(capacity, commands, True, conversion)})
                if incomplete:
                    record({'kind': 'incomplete', 'reason': 'controlled stop before first timed pair', 'injected': True})
                    return 2
                if fault:
                    for cached in (False, True):
                        outcome = execute(capacity, commands, cached, conversion and cached, fault)
                        record({'kind': 'attempt', 'name': name, 'cached': cached, 'outcome': outcome, 'injected': True})
                        if outcome['status'] == 'success':
                            raise AssertionError('controlled failure was not exercised')
                    failed = True
                    continue
                expected = execute(capacity, commands, False)
                if expected['status'] != 'success' or execute(capacity, commands, True, conversion) != expected:
                    raise AssertionError('workload outcomes differ')
                for cached in (False, True):
                    for _ in range(5):
                        if execute(capacity, commands, cached, conversion and cached) != expected:
                            raise AssertionError('warmup failed')
                for sample in range(9):
                    order = (False, True) if sample % 2 == 0 else (True, False)
                    for position, cached in enumerate(order):
                        start = time.perf_counter_ns()
                        outcomes = [execute(capacity, commands, cached, conversion and cached) for _ in range(20)]
                        elapsed = time.perf_counter_ns()-start
                        record({'kind': 'timing', 'name': name, 'cached': cached, 'sample': sample,
                                'position': position, 'repetitions': 20, 'elapsed_ns': elapsed,
                                'outcomes': outcomes})
                        if outcomes != [expected]*20:
                            raise AssertionError('timed execution failed')
                for cached in (False, True):
                    tracemalloc.start()
                    outcome = execute(capacity, commands, cached, conversion and cached)
                    current, peak = tracemalloc.get_traced_memory()
                    tracemalloc.stop()
                    record({'kind': 'memory', 'name': name, 'cached': cached,
                            'current_traced_bytes': current, 'peak_traced_bytes': peak, 'outcome': outcome})
                    if outcome != expected:
                        raise AssertionError('memory probe failed')
            record({'kind': 'complete', 'success': not failed})
            return 1 if failed else 0
        except BaseException as error:
            record({'kind': 'failure', 'exception': repr(error), 'success': False})
            raise

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('evidence')
    parser.add_argument('--fault', choices=('allocation','output'))
    parser.add_argument('--incomplete', action='store_true')
    args = parser.parse_args()
    raise SystemExit(main(args.evidence, args.fault, args.incomplete))
