#!/usr/bin/env python3
"""Bounded #250 CPython experiment; not a production backend or proof."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import sysconfig
import time
import tracemalloc

MAX_CAPACITY = 2**32 - 1

class Buffer:
    __slots__ = ('slots', 'size', 'cached', 'parity')

    def __init__(self, capacity, cached=False):
        if type(capacity) is not int or not 0 <= capacity <= MAX_CAPACITY:
            raise ValueError('capacity outside uint32 range')
        self.slots = bytearray(capacity)
        self.size = 0
        self.cached = cached
        self.parity = 0

    def query(self):
        if self.cached:
            return self.parity
        p = 0
        for i in range(self.size):
            p ^= self.slots[i]
        return p

    def step(self, command):
        op, value = command
        if op == 'append':
            if value not in (0, 1):
                raise ValueError('not a Boolean byte')
            if self.size == len(self.slots):
                return ('overflow', None)
            self.slots[self.size] = value
            self.size += 1
            if self.cached:
                self.parity ^= value
            return ('accepted', None)
        if op == 'query':
            return ('summary', self.query())
        if op == 'observe':
            return ('sequence', bytes(self.slots[:self.size]))
        raise ValueError('unknown command')

    def convert(self):
        # All capacity slots copied; original remains alive during conversion.
        result = object.__new__(Buffer)
        result.slots = self.slots.copy()
        result.size = self.size
        result.cached = True
        result.parity = 0
        for i in range(result.size):
            result.parity ^= result.slots[i]
        return result


def spec(capacity, history, command):
    op, value = command
    if op == 'append':
        return ((history + [value], ('accepted', None)) if len(history) < capacity
                else (history, ('overflow', None)))
    if op == 'query':
        return history, ('summary', sum(history) % 2)
    return history, ('sequence', bytes(history))


def checks():
    commands = [('append', 0), ('append', 1), ('query', None), ('observe', None)]
    traces = 0
    for capacity in range(4):
        for length in range(6):
            for trace in itertools.product(commands, repeat=length):
                plain, cached = Buffer(capacity), Buffer(capacity, True)
                history = []
                for command in trace:
                    history, reply = spec(capacity, history, command)
                    assert plain.step(command) == cached.step(command) == reply
                    assert bytes(plain.slots[:plain.size]) == bytes(history)
                    assert bytes(cached.slots[:cached.size]) == bytes(history)
                    assert cached.parity == sum(history) % 2
                converted = plain.convert()
                assert converted.slots is not plain.slots
                assert converted.slots == plain.slots
                for command in commands:
                    # Check extension from the same converted snapshot each time.
                    c = plain.convert()
                    assert c.step(command) == spec(capacity, history, command)[1]
                traces += 1
    wrong = Buffer(1, True)
    wrong.parity = 1
    assert wrong.step(('query', None)) != spec(1, [], ('query', None))[1]
    for bad in (-1, MAX_CAPACITY + 1, 1.5):
        try:
            Buffer(bad)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid capacity accepted')
    # Published #239 examples independently check the model projection.
    appends = [('append', x) for x in (1, 0, 1, 1)]
    batch = appends + [('query', None)]
    prefix = [c for a in appends for c in (a, ('query', None))]
    assert (model(4, batch, False), model(4, batch, True)) == (26, 27)
    assert (model(4, prefix, False), model(4, prefix, True)) == (41, 30)
    assert (model(4, appends, False), model(4, appends, True)) == (17, 26)
    return {'short_traces': traces, 'max_trace_length': 5, 'capacities': [0, 1, 2, 3],
            'invalid_cache_detected': True, 'invalid_capacities_rejected': True}


def model(capacity, commands, cached, conversion=False):
    # Projection of #239 unit tariffs, not hardware or Python event counters.
    cost, size = capacity + 1 + int(cached and not conversion), 0
    mode = cached and not conversion
    for op, _ in commands:
        if op == 'convert':
            if conversion:
                cost += 2 * capacity + 2 * size + 2
                mode = True
        elif op == 'append':
            cost += 1
            if size < capacity:
                cost += 2 + 2 * int(mode)
                size += 1
        elif op == 'query':
            cost += 1 if mode else 2 * size + 1
        else:
            cost += 2 * size + 1
    return cost


def execute(capacity, commands, cached, conversion=False):
    b = Buffer(capacity, cached and not conversion)
    checksum = 0
    for command in commands:
        if command[0] == 'convert':
            if conversion:
                b = b.convert()
            continue
        tag, result = b.step(command)
        # Consume every public reply in order. A checksum is only a timing sink;
        # checks() compares exact replies and does not rely on collision freedom.
        code = {'accepted': 1, 'overflow': 2, 'summary': 3, 'sequence': 4}[tag]
        checksum = (checksum * 33 + code) & 0xffffffff
        if isinstance(result, bytes):
            for x in result:
                checksum = (checksum * 33 + x) & 0xffffffff
        elif result is not None:
            checksum = (checksum * 33 + result) & 0xffffffff
    return checksum


def workloads():
    rng = random.Random(250)
    values = [rng.randrange(2) for _ in range(512)]
    appends = [('append', v) for v in values]
    return {
        'batch_final': (512, appends + [('query', None), ('observe', None)], False),
        'every_prefix': (512, [c for a in appends for c in (a, ('query', None))]
                         + [('observe', None)], False),
        'update_heavy': (512, appends + [('observe', None)], False),
        'conversion_erases': (4096, [('append', 1), ('convert', None),
                                    ('query', None), ('query', None), ('observe', None)], True),
    }


def main(destination, inject_allocation_failure=False):
    root = Path(__file__).resolve().parents[2]
    out = Path(destination)
    # Exclusive output avoids overwriting an earlier failed or successful attempt.
    with out.open('x') as stream:
        def record(data):
            stream.write(json.dumps(data, sort_keys=True) + '\n')
            stream.flush()
        record({'kind': 'environment', 'python': sys.version, 'executable': sys.executable,
                'implementation': platform.python_implementation(), 'compiler': platform.python_compiler(),
                'config_args': sysconfig.get_config_var('CONFIG_ARGS'), 'platform': platform.platform(),
                'machine': platform.machine(), 'processor': platform.processor(),
                'cpuinfo': Path('/proc/cpuinfo').read_text().split('\n\n')[0] if Path('/proc/cpuinfo').exists() else None,
                'clock': vars(time.get_clock_info('perf_counter')),
                'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                'command': sys.argv, 'source_hashes': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in [Path(__file__).resolve(), root/'flake.lock', root/'lean-toolchain',
                              root/'Applications/Sequences/BoundedSummary.lean', root/'Applications/Resources/BoundedSummary.lean']}})
        try:
            if inject_allocation_failure:
                record({'kind': 'fault_injection', 'boundary': 'bytearray allocation', 'injected': True})
                from unittest.mock import patch
                with patch(__name__ + '.bytearray', side_effect=MemoryError('injected allocation failure'), create=True):
                    Buffer(1)
            start = time.perf_counter_ns()
            record({'kind': 'checks', 'result': checks(), 'elapsed_ns': time.perf_counter_ns() - start})
            # Preserve an intentionally unsuccessful public-service invocation.
            try:
                Buffer(MAX_CAPACITY + 1)
            except ValueError as error:
                record({'kind': 'expected_failure', 'input_capacity': MAX_CAPACITY + 1,
                        'exception': repr(error), 'injected': False})
            for name, (capacity, commands, conversion) in workloads().items():
                record({'kind': 'workload', 'name': name, 'capacity': capacity, 'commands': commands,
                        'plain_model': model(capacity, commands, False),
                        'cached_model': model(capacity, commands, True, conversion)})
                expected = execute(capacity, commands, False)
                assert expected == execute(capacity, commands, True, conversion)
                # Warm both modes; alternating order limits a fixed ordering bias.
                for cached in (False, True):
                    for _ in range(5):
                        execute(capacity, commands, cached, conversion and cached)
                for sample in range(9):
                    for cached in ((False, True) if sample % 2 == 0 else (True, False)):
                        start = time.perf_counter_ns()
                        outputs = [execute(capacity, commands, cached, conversion and cached) for _ in range(20)]
                        elapsed = time.perf_counter_ns() - start
                        assert outputs == [expected] * 20
                        record({'kind': 'timing', 'name': name, 'cached': cached, 'sample': sample,
                                'repetitions': 20, 'elapsed_ns': elapsed, 'checksum': expected})
                for cached in (False, True):
                    tracemalloc.start()
                    output = execute(capacity, commands, cached, conversion and cached)
                    current, peak = tracemalloc.get_traced_memory()
                    tracemalloc.stop()
                    assert output == expected
                    record({'kind': 'memory', 'name': name, 'cached': cached,
                            'current_traced_bytes': current, 'peak_traced_bytes': peak})
            record({'kind': 'complete', 'success': True})
        except BaseException as error:
            record({'kind': 'failure', 'exception': repr(error), 'success': False})
            raise

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('evidence', help='new JSONL evidence path')
    parser.add_argument('--inject-allocation-failure', action='store_true')
    args = parser.parse_args()
    main(args.evidence, args.inject_allocation_failure)
